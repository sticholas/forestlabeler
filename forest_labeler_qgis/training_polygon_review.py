"""Review helpers for selected Training Polygon features."""

from __future__ import annotations

from dataclasses import dataclass


REVIEW_STATUS_ACCEPTED = "accepted"
REVIEW_STATUS_REJECTED = "rejected"
REVIEW_STATUS_UNSURE = "unsure"

REVIEWED_FLAG_BY_STATUS = {
    REVIEW_STATUS_ACCEPTED: 1,
    REVIEW_STATUS_REJECTED: -1,
    REVIEW_STATUS_UNSURE: 0,
}


@dataclass(frozen=True)
class ReviewUpdateResult:
    ok: bool
    updated_count: int
    errors: tuple
    warnings: tuple


def mark_selected_training_polygons(layer, status, note=None):
    """Mark selected Training Polygon features with a review status."""
    errors = []
    warnings = []

    if layer is None:
        errors.append("Select a Training Polygon target layer.")
    elif not layer.isEditable():
        errors.append(f"Turn editing on for '{layer.name()}' before marking review status.")

    if status not in REVIEWED_FLAG_BY_STATUS:
        errors.append("Review status must be accepted, rejected, or unsure.")

    if errors:
        return ReviewUpdateResult(False, 0, tuple(errors), tuple(warnings))

    selected_ids = layer.selectedFeatureIds()
    if not selected_ids:
        return ReviewUpdateResult(
            False,
            0,
            ("Select one or more Training Polygon features to review.",),
            tuple(warnings),
        )

    reviewed_index = layer.fields().indexOf("reviewed")
    status_index = layer.fields().indexOf("review_status")
    note_index = layer.fields().indexOf("review_note")
    missing = [
        field_name
        for field_name, field_index in (
            ("reviewed", reviewed_index),
            ("review_status", status_index),
        )
        if field_index == -1
    ]
    if missing:
        return ReviewUpdateResult(
            False,
            0,
            ("Missing review field(s): " + ", ".join(missing) + ". Use Add Metadata Fields first.",),
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
    return ReviewUpdateResult(
        ok=updated_count > 0,
        updated_count=updated_count,
        errors=() if updated_count > 0 else ("No selected features were updated.",),
        warnings=tuple(warnings),
    )
