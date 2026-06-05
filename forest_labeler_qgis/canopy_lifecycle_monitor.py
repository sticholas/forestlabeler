"""Observe QGIS mutations on the active Forest Labeler canopy layer."""

from __future__ import annotations

from qgis.PyQt.QtCore import QTimer
from qgis.core import QgsFeatureRequest, QgsGeometry

from ..forest_labeler_core.canopy_attributes import canopy_geometry_metric_updates
from .canopy_attempt_log import (
    canopy_attempt_record_from_feature,
    feedback_event_store_path,
    log_removed_canopy_attempt_from_record,
    log_edited_canopy_attempt_from_record,
    log_restored_canopy_attempt_from_record,
    log_reviewed_canopy_attempt,
)
from ..forest_labeler_core.canopy_attempt_log import CANOPY_ATTEMPT_REJECTED_REMOVED
from ..forest_labeler_core.canopy_lifecycle import (
    canopy_attribute_change_invalidates_review,
    canopy_geometry_change_invalidates_review,
)
from ..forest_labeler_core.feedback_event_store import latest_feedback_event_type
from .canopy_metrics import recalculate_canopy_chm_metrics_by_id


# Disabled until QGIS/GeoPackage edit-buffer writes are isolated from background
# metric and feedback updates. Core labeling must never risk provider save locks.
AUTO_LIFECYCLE_MONITOR_ENABLED = False


class CanopyLifecycleMonitor:
    """Keep review and learning evidence aligned with QGIS feature mutations."""

    def __init__(self, iface=None):
        self.iface = iface
        self.layer = None
        self.records_by_feature_id = {}
        self.invalidating_feature_ids = set()
        self.chm_layer = None
        self.pending_chm_feature_ids = set()
        self.pending_chm_geometries = {}
        self.chm_update_scheduled = False
        self.connected_signals = []

    def watch(self, layer, chm_layer=None):
        if not AUTO_LIFECYCLE_MONITOR_ENABLED:
            self.disconnect()
            return
        self.chm_layer = chm_layer
        if layer is self.layer:
            self.refresh()
            return
        self.disconnect()
        if layer is None or layer.fields().indexOf("attempt_id") == -1:
            return
        self.layer = layer
        self.refresh()
        self._connect(layer.featureAdded, self._feature_added)
        self._connect(layer.attributeValueChanged, self._attribute_changed)
        self._connect(layer.geometryChanged, self._geometry_changed)
        self._connect(layer.featureDeleted, self._feature_deleted)
        self._connect_optional(layer, "beforeCommitChanges", self._before_commit_changes)
        self._connect_optional(layer, "editCommandEnded", self._edit_command_ended)
        self._connect_optional(layer, "editCommandDestroyed", self._edit_command_ended)

    def refresh(self):
        if self.layer is None:
            return
        self.records_by_feature_id = {}
        for feature in self.layer.getFeatures():
            self._remember(feature)

    def disconnect(self):
        for signal, handler in self.connected_signals:
            try:
                signal.disconnect(handler)
            except Exception:
                pass
        self.connected_signals = []
        self.layer = None
        self.chm_layer = None
        self.records_by_feature_id = {}
        self.invalidating_feature_ids = set()
        self.pending_chm_feature_ids = set()
        self.pending_chm_geometries = {}
        self.chm_update_scheduled = False

    def _connect(self, signal, handler):
        try:
            signal.connect(handler)
            self.connected_signals.append((signal, handler))
        except Exception:
            pass

    def _connect_optional(self, layer, signal_name, handler):
        signal = getattr(layer, signal_name, None)
        if signal is not None:
            self._connect(signal, handler)

    def _feature_added(self, feature_id):
        feature = self._feature(feature_id)
        if feature is None:
            return
        record = canopy_attempt_record_from_feature(self.layer, feature)
        if record is None:
            return
        was_removed = (
            latest_feedback_event_type(feedback_event_store_path(), record.attempt_id)
            == CANOPY_ATTEMPT_REJECTED_REMOVED
        )
        self.records_by_feature_id[feature_id] = record
        if was_removed:
            self._report(
                log_restored_canopy_attempt_from_record(
                    record,
                    note="QGIS deletion undo/restoration observed",
                ),
                "Observed restored canopy and updated learning evidence.",
            )

    def _attribute_changed(self, feature_id, field_index, _value):
        if feature_id in self.invalidating_feature_ids:
            self._refresh_feature(feature_id)
            return
        previous = self.records_by_feature_id.get(feature_id)
        self._refresh_feature(feature_id)
        current = self.records_by_feature_id.get(feature_id)
        if previous is None or current is None:
            return
        status_index = self.layer.fields().indexOf("review_status")
        if field_index == status_index:
            self._handle_review_status_change(feature_id, previous, current)
            return
        field_name = self.layer.fields()[field_index].name()
        if canopy_attribute_change_invalidates_review(field_name, previous.review_status):
            self._invalidate_review(
                feature_id,
                current,
                note=f"Material canopy attribute edited in QGIS: {field_name}",
            )

    def _handle_review_status_change(self, feature_id, previous, current):
        if current.review_status == previous.review_status:
            return
        status = str(current.review_status or "").strip().lower()
        if status in {"accepted", "rejected", "unsure"}:
            feature = self._feature(feature_id)
            if feature is not None:
                self._report(
                    log_reviewed_canopy_attempt(
                        self.layer,
                        feature,
                        status,
                        note="QGIS attribute review-status change observed",
                    ),
                    "Observed canopy review-status change and updated learning evidence.",
                )
        elif status in {"", "unreviewed"} and str(previous.review_status or "").strip().lower() in {
            "accepted",
            "rejected",
            "unsure",
        }:
            self._report(
                log_edited_canopy_attempt_from_record(
                    current,
                    note="QGIS review status reset to unreviewed",
                ),
                "Observed review reset and updated learning evidence.",
            )

    def _geometry_changed(self, feature_id, geometry):
        if self._is_temporary_feature_id(feature_id) or self._has_uncommitted_added_features():
            return
        previous = self.records_by_feature_id.get(feature_id)
        feature = self._feature(feature_id)
        current_geometry = geometry
        try:
            if current_geometry is None or current_geometry.isEmpty():
                current_geometry = feature.geometry() if feature is not None else geometry
        except Exception:
            current_geometry = feature.geometry() if feature is not None else geometry
        self._update_geometry_metrics(feature_id, current_geometry)
        self._schedule_chm_metrics_update(feature_id, current_geometry)
        self._refresh_feature(feature_id)
        current = self.records_by_feature_id.get(feature_id)
        if previous is None or current is None:
            return
        if canopy_geometry_change_invalidates_review(previous.review_status):
            self._invalidate_review(
                feature_id,
                current,
                note="Canopy geometry edited in QGIS",
            )

    def _schedule_chm_metrics_update(self, feature_id, geometry=None):
        if (
            self.chm_layer is None
            or self._is_temporary_feature_id(feature_id)
            or self._has_uncommitted_added_features()
        ):
            return
        self.pending_chm_feature_ids.add(feature_id)
        if geometry is not None:
            try:
                self.pending_chm_geometries[feature_id] = QgsGeometry(geometry)
            except Exception:
                pass
        if self.chm_update_scheduled:
            return
        self.chm_update_scheduled = True
        QTimer.singleShot(250, self._flush_chm_metrics_updates)

    def _edit_command_ended(self, *_args):
        if self.pending_chm_feature_ids:
            QTimer.singleShot(0, self._flush_chm_metrics_updates)

    def _before_commit_changes(self, *_args):
        self.pending_chm_feature_ids = set()
        self.pending_chm_geometries = {}
        self.chm_update_scheduled = False

    def _flush_chm_metrics_updates(self):
        self.chm_update_scheduled = False
        if self._has_uncommitted_added_features():
            self.pending_chm_feature_ids = set()
            self.pending_chm_geometries = {}
            return
        feature_ids = tuple(self.pending_chm_feature_ids)
        geometries = self.pending_chm_geometries
        self.pending_chm_feature_ids = set()
        self.pending_chm_geometries = {}
        for feature_id in feature_ids:
            self._update_chm_metrics(feature_id, geometry=geometries.get(feature_id))

    def _update_chm_metrics(self, feature_id, geometry=None):
        if (
            self.chm_layer is None
            or self._is_temporary_feature_id(feature_id)
            or self._has_uncommitted_added_features()
        ):
            return
        self.invalidating_feature_ids.add(feature_id)
        try:
            result = recalculate_canopy_chm_metrics_by_id(
                self.layer,
                self.chm_layer,
                feature_id,
                geometry=geometry,
            )
        finally:
            self.invalidating_feature_ids.discard(feature_id)
        self._refresh_feature(feature_id)
        if not result.ok:
            self._report(result, "Canopy CHM metrics recalculated.")

    def _update_geometry_metrics(self, feature_id, geometry):
        if self._is_temporary_feature_id(feature_id) or self._has_uncommitted_added_features():
            return
        updates = canopy_geometry_metric_updates(geometry.area())
        if not updates:
            return
        self.invalidating_feature_ids.add(feature_id)
        try:
            for field_name, value in updates.items():
                index = self.layer.fields().indexOf(field_name)
                if index != -1:
                    self.layer.changeAttributeValue(feature_id, index, value)
        finally:
            self.invalidating_feature_ids.discard(feature_id)

    def _invalidate_review(self, feature_id, record, note):
        self._report(
            log_edited_canopy_attempt_from_record(record, note=note),
            "Observed material canopy edit; returned crown to review.",
        )
        reviewed_index = self.layer.fields().indexOf("reviewed")
        status_index = self.layer.fields().indexOf("review_status")
        self.invalidating_feature_ids.add(feature_id)
        try:
            if reviewed_index != -1:
                self.layer.changeAttributeValue(feature_id, reviewed_index, 0)
            if status_index != -1:
                self.layer.changeAttributeValue(feature_id, status_index, "unreviewed")
        finally:
            self.invalidating_feature_ids.discard(feature_id)
            self._refresh_feature(feature_id)

    def _refresh_feature(self, feature_id):
        if self.layer is None:
            return
        feature = self._feature(feature_id)
        if feature is not None:
            self._remember(feature)

    def _remember(self, feature):
        record = canopy_attempt_record_from_feature(self.layer, feature)
        if record is not None:
            self.records_by_feature_id[feature.id()] = record

    def _feature_deleted(self, feature_id):
        record = self.records_by_feature_id.pop(feature_id, None)
        if record is None:
            return
        result = log_removed_canopy_attempt_from_record(
            record,
            note="QGIS feature deletion observed",
        )
        self._report(result, "Observed deleted canopy and updated learning evidence.")

    def _feature(self, feature_id):
        if self.layer is None:
            return None
        return next(
            self.layer.getFeatures(QgsFeatureRequest().setFilterFid(feature_id)),
            None,
        )

    def _is_temporary_feature_id(self, feature_id):
        try:
            return int(feature_id) < 0
        except Exception:
            return False

    def _has_uncommitted_added_features(self):
        if self.layer is None:
            return False
        try:
            edit_buffer = self.layer.editBuffer()
        except Exception:
            return False
        if edit_buffer is None:
            return False
        try:
            return bool(edit_buffer.addedFeatures())
        except Exception:
            return False

    def _report(self, result, success_message):
        if self.iface is None:
            return
        if result.ok:
            self.iface.messageBar().pushInfo("Forest Labeler", success_message)
        else:
            self.iface.messageBar().pushWarning("Forest Labeler", " ".join(result.errors))
