"""QGIS helpers for canopy review and press-hold tool evaluation."""

from __future__ import annotations

from dataclasses import dataclass

from .canopy_attempt_log import log_removed_canopy_attempt
from ..forest_labeler_core.canopy_review import (
    CANOPY_REVIEW_FILTER_ATTENTION,
    CANOPY_REVIEW_FILTER_UNREVIEWED,
    REVIEW_STATUS_ACCEPTED,
    REVIEW_STATUS_REJECTED,
    REVIEW_STATUS_UNSURE,
    REVIEWED_FLAG_BY_STATUS,
    best_canopy_tool_recommendation,
    canopy_review_status_matches_filter,
    canopy_quality_insight_lines,
    summarize_canopy_reviews,
)


@dataclass(frozen=True)
class CanopyReviewUpdateResult:
    ok: bool
    updated_count: int
    errors: tuple
    warnings: tuple


@dataclass(frozen=True)
class CanopySelectionResult:
    ok: bool
    selected_count: int
    errors: tuple
    warnings: tuple


def mark_selected_canopies(layer, status, note=None):
    errors = []
    warnings = []

    if layer is None:
        errors.append("Select a target canopy polygon layer.")
    elif not layer.isEditable():
        errors.append(f"Turn editing on for '{layer.name()}' before marking review status.")
    if status not in REVIEWED_FLAG_BY_STATUS:
        errors.append("Review status must be accepted, rejected, or unsure.")
    if errors:
        return CanopyReviewUpdateResult(False, 0, tuple(errors), tuple(warnings))

    selected_ids = layer.selectedFeatureIds()
    if not selected_ids:
        return CanopyReviewUpdateResult(
            False,
            0,
            ("Select one or more canopy features to review.",),
            tuple(warnings),
        )

    reviewed_index = layer.fields().indexOf("reviewed")
    status_index = layer.fields().indexOf("review_status")
    note_index = layer.fields().indexOf("review_note")
    missing = [
        name for name, index in (("reviewed", reviewed_index), ("review_status", status_index))
        if index == -1
    ]
    if missing:
        return CanopyReviewUpdateResult(
            False,
            0,
            ("Missing review field(s): " + ", ".join(missing) + ".",),
            tuple(warnings),
        )

    cleaned_note = str(note).strip() if note is not None else ""
    if cleaned_note and note_index == -1:
        warnings.append("Review note was not stored because 'review_note' is missing.")

    updated_count = 0
    for feature_id in selected_ids:
        if not layer.changeAttributeValue(feature_id, reviewed_index, REVIEWED_FLAG_BY_STATUS[status]):
            warnings.append(f"Could not update reviewed flag for feature {feature_id}.")
            continue
        if not layer.changeAttributeValue(feature_id, status_index, status):
            warnings.append(f"Could not update review status for feature {feature_id}.")
            continue
        if cleaned_note and note_index != -1:
            if not layer.changeAttributeValue(feature_id, note_index, cleaned_note):
                warnings.append(f"Could not update review note for feature {feature_id}.")
        updated_count += 1

    layer.triggerRepaint()
    return CanopyReviewUpdateResult(
        ok=updated_count > 0,
        updated_count=updated_count,
        errors=() if updated_count > 0 else ("No selected features were updated.",),
        warnings=tuple(warnings),
    )


def reject_and_remove_selected_canopies(layer, note=None):
    """Log selected canopies as rejected, then remove them from the target layer."""
    errors = []
    warnings = []

    if layer is None:
        errors.append("Select a target canopy polygon layer.")
    elif not layer.isEditable():
        errors.append(f"Turn editing on for '{layer.name()}' before removing rejected canopies.")
    if errors:
        return CanopyReviewUpdateResult(False, 0, tuple(errors), tuple(warnings))

    selected_ids = layer.selectedFeatureIds()
    if not selected_ids:
        return CanopyReviewUpdateResult(
            False,
            0,
            ("Select one or more canopy features to reject and remove.",),
            tuple(warnings),
        )

    feature_by_id = {feature.id(): feature for feature in layer.getFeatures(selected_ids)}
    removed_count = 0
    command = _LayerEditCommand(layer, "Reject and remove Forest Labeler canopy")
    command.begin()
    try:
        for feature_id in selected_ids:
            feature = feature_by_id.get(feature_id)
            if feature is None:
                warnings.append(f"Could not read selected canopy feature {feature_id}.")
                continue
            log_result = log_removed_canopy_attempt(layer, feature, note=note)
            if not log_result.ok:
                warnings.extend(log_result.errors)
                warnings.append(f"Canopy feature {feature_id} was kept because the rejected attempt was not logged.")
                continue
            if not layer.deleteFeature(feature_id):
                warnings.append(f"Could not remove canopy feature {feature_id}.")
                continue
            removed_count += 1
        command.commit()
    except Exception as exc:
        command.rollback()
        return CanopyReviewUpdateResult(
            False,
            removed_count,
            (f"Could not reject and remove selected canopies: {exc}",),
            tuple(warnings),
        )

    layer.triggerRepaint()
    return CanopyReviewUpdateResult(
        ok=removed_count > 0,
        updated_count=removed_count,
        errors=() if removed_count > 0 else ("No selected canopies were removed.",),
        warnings=tuple(warnings),
    )


def summarize_canopy_layer_reviews(layer):
    if layer is None:
        raise ValueError("Select a target canopy polygon layer.")
    return summarize_canopy_reviews(_canopy_review_records(layer))


def canopy_layer_quality_insight_lines(layer, min_reviewed=3):
    if layer is None:
        raise ValueError("Select a target canopy polygon layer.")
    return canopy_quality_insight_lines(_canopy_review_records(layer), min_reviewed=min_reviewed)


def best_canopy_layer_recommendation(layer, min_reviewed=3):
    if layer is None:
        raise ValueError("Select a target canopy polygon layer.")
    return best_canopy_tool_recommendation(_canopy_review_records(layer), min_reviewed=min_reviewed)


def select_canopies_by_review_filter(layer, review_filter):
    if layer is None:
        return CanopySelectionResult(False, 0, ("Select a target canopy polygon layer.",), ())
    if review_filter not in {CANOPY_REVIEW_FILTER_UNREVIEWED, CANOPY_REVIEW_FILTER_ATTENTION}:
        return CanopySelectionResult(False, 0, ("Unknown canopy review filter.",), ())

    reviewed_index = layer.fields().indexOf("reviewed")
    status_index = layer.fields().indexOf("review_status")
    if reviewed_index == -1 and status_index == -1:
        return CanopySelectionResult(
            False,
            0,
            ("Missing review field(s): reviewed or review_status.",),
            (),
        )

    selected_ids = []
    for feature in layer.getFeatures():
        reviewed = feature[reviewed_index] if reviewed_index != -1 else None
        status = feature[status_index] if status_index != -1 else None
        if canopy_review_status_matches_filter(status, reviewed, review_filter):
            selected_ids.append(feature.id())

    layer.selectByIds(selected_ids)
    layer.triggerRepaint()
    return CanopySelectionResult(True, len(selected_ids), (), ())


def _canopy_review_records(layer):
    reviewed_index = layer.fields().indexOf("reviewed")
    status_index = layer.fields().indexOf("review_status")
    mode_index = layer.fields().indexOf("mode")
    tightness_index = layer.fields().indexOf("tightness")

    records = []
    for feature in layer.getFeatures():
        records.append(
            {
                "reviewed": feature[reviewed_index] if reviewed_index != -1 else None,
                "review_status": feature[status_index] if status_index != -1 else None,
                "mode": feature[mode_index] if mode_index != -1 else None,
                "tightness": feature[tightness_index] if tightness_index != -1 else None,
            }
        )
    return records


class _LayerEditCommand:
    def __init__(self, layer, label):
        self.layer = layer
        self.label = label
        self.started = False

    def begin(self):
        if hasattr(self.layer, "beginEditCommand"):
            self.layer.beginEditCommand(self.label)
            self.started = True

    def commit(self):
        if self.started and hasattr(self.layer, "endEditCommand"):
            self.layer.endEditCommand()
            self.started = False

    def rollback(self):
        if self.started and hasattr(self.layer, "destroyEditCommand"):
            self.layer.destroyEditCommand()
            self.started = False
