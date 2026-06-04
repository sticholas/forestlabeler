"""Observe all deletion paths on the active Forest Labeler canopy layer."""

from __future__ import annotations

from qgis.core import QgsFeatureRequest

from .canopy_attempt_log import (
    canopy_attempt_record_from_feature,
    feedback_event_store_path,
    log_removed_canopy_attempt_from_record,
    log_restored_canopy_attempt_from_record,
    log_reviewed_canopy_attempt,
)
from ..forest_labeler_core.canopy_attempt_log import CANOPY_ATTEMPT_REJECTED_REMOVED
from ..forest_labeler_core.feedback_event_store import latest_feedback_event_type


class CanopyDeletionMonitor:
    """Keep lifecycle evidence aligned with QGIS feature deletions."""

    def __init__(self, iface=None):
        self.iface = iface
        self.layer = None
        self.records_by_feature_id = {}

    def watch(self, layer):
        if layer is self.layer:
            self.refresh()
            return
        self.disconnect()
        if layer is None or layer.fields().indexOf("attempt_id") == -1:
            return
        self.layer = layer
        self.refresh()
        try:
            layer.featureAdded.connect(self._feature_added)
            layer.attributeValueChanged.connect(self._attribute_changed)
            layer.featureDeleted.connect(self._feature_deleted)
        except Exception:
            self.disconnect()

    def refresh(self):
        if self.layer is None:
            return
        self.records_by_feature_id = {}
        for feature in self.layer.getFeatures():
            self._remember(feature)

    def disconnect(self):
        if self.layer is not None:
            for signal, handler in (
                (self.layer.featureAdded, self._feature_added),
                (self.layer.attributeValueChanged, self._attribute_changed),
                (self.layer.featureDeleted, self._feature_deleted),
            ):
                try:
                    signal.disconnect(handler)
                except Exception:
                    pass
        self.layer = None
        self.records_by_feature_id = {}

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
        previous = self.records_by_feature_id.get(feature_id)
        self._refresh_feature(feature_id)
        current = self.records_by_feature_id.get(feature_id)
        if previous is None or current is None:
            return
        status_index = self.layer.fields().indexOf("review_status")
        if field_index != status_index or current.review_status == previous.review_status:
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

    def _report(self, result, success_message):
        if self.iface is None:
            return
        if result.ok:
            self.iface.messageBar().pushInfo("Forest Labeler", success_message)
        else:
            self.iface.messageBar().pushWarning("Forest Labeler", " ".join(result.errors))
