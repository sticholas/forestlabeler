"""Feedback records and summaries for future learning loops."""

from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass


RATING_GOOD = "good"
RATING_ACCEPTABLE = "acceptable_after_edit"
RATING_BAD = "bad"
RATING_UNCERTAIN = "uncertain"

VALID_RATINGS = {
    RATING_GOOD,
    RATING_ACCEPTABLE,
    RATING_BAD,
    RATING_UNCERTAIN,
}


@dataclass(frozen=True)
class FeedbackRecord:
    workflow: str
    canopy_mode: str | None
    crown_tightness: int | None
    rating: str
    correction_reason: str | None = None


@dataclass(frozen=True)
class FeedbackBucket:
    workflow: str
    canopy_mode: str | None
    crown_tightness: int | None
    total: int
    good: int
    acceptable_after_edit: int
    bad: int
    uncertain: int

    @property
    def positive_rate(self):
        if self.total == 0:
            return 0.0
        return (self.good + self.acceptable_after_edit) / self.total


def validate_feedback_record(record):
    """Return validation errors for a feedback record."""
    errors = []
    if not record.workflow:
        errors.append("workflow is required")
    if record.rating not in VALID_RATINGS:
        errors.append("rating must be one of: " + ", ".join(sorted(VALID_RATINGS)))
    if record.crown_tightness is not None and not 1 <= int(record.crown_tightness) <= 21:
        errors.append("crown_tightness must be between 1 and 21")
    return tuple(errors)


def summarize_feedback(records):
    """Summarize feedback by workflow, canopy mode, and crown tightness."""
    grouped = defaultdict(list)
    for record in records:
        errors = validate_feedback_record(record)
        if errors:
            raise ValueError("; ".join(errors))
        key = (record.workflow, record.canopy_mode, record.crown_tightness)
        grouped[key].append(record)

    summaries = []
    for (workflow, canopy_mode, crown_tightness), bucket_records in grouped.items():
        ratings = [record.rating for record in bucket_records]
        summaries.append(
            FeedbackBucket(
                workflow=workflow,
                canopy_mode=canopy_mode,
                crown_tightness=crown_tightness,
                total=len(bucket_records),
                good=ratings.count(RATING_GOOD),
                acceptable_after_edit=ratings.count(RATING_ACCEPTABLE),
                bad=ratings.count(RATING_BAD),
                uncertain=ratings.count(RATING_UNCERTAIN),
            )
        )

    return sorted(
        summaries,
        key=lambda item: (
            item.workflow,
            item.canopy_mode or "",
            item.crown_tightness if item.crown_tightness is not None else -1,
        ),
    )


def best_feedback_bucket(records, min_samples=3):
    """Return the highest positive-rate feedback bucket with enough samples."""
    eligible = [bucket for bucket in summarize_feedback(records) if bucket.total >= min_samples]
    if not eligible:
        return None
    return max(eligible, key=lambda bucket: (bucket.positive_rate, bucket.total))
