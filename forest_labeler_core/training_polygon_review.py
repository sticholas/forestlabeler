"""Training Polygon review summaries for quality reporting."""

from __future__ import annotations

from dataclasses import dataclass


REVIEW_STATUS_ACCEPTED = "accepted"
REVIEW_STATUS_REJECTED = "rejected"
REVIEW_STATUS_UNSURE = "unsure"
REVIEW_STATUS_UNREVIEWED = "unreviewed"

REVIEWED_FLAG_BY_STATUS = {
    REVIEW_STATUS_ACCEPTED: 1,
    REVIEW_STATUS_REJECTED: -1,
    REVIEW_STATUS_UNSURE: 0,
    REVIEW_STATUS_UNREVIEWED: 0,
}


@dataclass(frozen=True)
class TrainingPolygonReviewSummary:
    total: int
    accepted: int
    rejected: int
    unsure: int
    unreviewed: int

    @property
    def reviewed_total(self):
        return self.accepted + self.rejected + self.unsure

    @property
    def accepted_rate(self):
        if self.reviewed_total == 0:
            return 0.0
        return self.accepted / self.reviewed_total

    @property
    def needs_attention(self):
        return self.rejected + self.unsure


@dataclass(frozen=True)
class TrainingPolygonReviewBucket:
    label: str
    summary: TrainingPolygonReviewSummary


def normalize_review_status(status, reviewed=None):
    """Normalize layer values into a known Training Polygon review status."""
    status_text = str(status or "").strip().lower()
    if status_text in {
        REVIEW_STATUS_ACCEPTED,
        REVIEW_STATUS_REJECTED,
        REVIEW_STATUS_UNSURE,
        REVIEW_STATUS_UNREVIEWED,
    }:
        return status_text

    try:
        reviewed_value = int(reviewed)
    except (TypeError, ValueError):
        return REVIEW_STATUS_UNREVIEWED

    if reviewed_value > 0:
        return REVIEW_STATUS_ACCEPTED
    if reviewed_value < 0:
        return REVIEW_STATUS_REJECTED
    return REVIEW_STATUS_UNREVIEWED


def summarize_training_polygon_reviews(records):
    """Summarize review statuses from iterable records."""
    counts = {
        REVIEW_STATUS_ACCEPTED: 0,
        REVIEW_STATUS_REJECTED: 0,
        REVIEW_STATUS_UNSURE: 0,
        REVIEW_STATUS_UNREVIEWED: 0,
    }
    total = 0
    for record in records:
        total += 1
        if isinstance(record, dict):
            status = record.get("review_status")
            reviewed = record.get("reviewed")
        else:
            status = getattr(record, "review_status", None)
            reviewed = getattr(record, "reviewed", None)
        counts[normalize_review_status(status, reviewed)] += 1

    return TrainingPolygonReviewSummary(
        total=total,
        accepted=counts[REVIEW_STATUS_ACCEPTED],
        rejected=counts[REVIEW_STATUS_REJECTED],
        unsure=counts[REVIEW_STATUS_UNSURE],
        unreviewed=counts[REVIEW_STATUS_UNREVIEWED],
    )


def summarize_training_polygon_reviews_by_key(records, key_fields):
    """Summarize reviews by a tuple of record fields."""
    grouped = {}
    for record in records:
        key = _record_key(record, key_fields)
        grouped.setdefault(key, []).append(record)

    buckets = []
    for key, bucket_records in grouped.items():
        buckets.append(
            TrainingPolygonReviewBucket(
                label=_format_bucket_label(key_fields, key),
                summary=summarize_training_polygon_reviews(bucket_records),
            )
        )
    return sorted(buckets, key=lambda item: item.label)


def training_polygon_quality_insight_lines(records, min_reviewed=3):
    """Return concise pattern insights once enough reviewed polygons exist."""
    buckets = [
        bucket
        for bucket in summarize_training_polygon_reviews_by_key(records, ("shape", "side_lengths"))
        if bucket.summary.reviewed_total >= min_reviewed
    ]
    if not buckets:
        return (
            f"Pattern insights need at least {min_reviewed} reviewed polygons per shape/side pattern.",
        )

    best = max(
        buckets,
        key=lambda bucket: (
            bucket.summary.accepted_rate,
            bucket.summary.reviewed_total,
            -bucket.summary.needs_attention,
        ),
    )
    attention = max(
        buckets,
        key=lambda bucket: (
            bucket.summary.needs_attention,
            -bucket.summary.accepted_rate,
            bucket.summary.reviewed_total,
        ),
    )
    return (
        "Best pattern: {label} | {accepted_pct}% accepted across {reviewed} reviewed.".format(
            label=best.label,
            accepted_pct=round(best.summary.accepted_rate * 100.0, 1),
            reviewed=best.summary.reviewed_total,
        ),
        "Watch pattern: {label} | {attention} need attention across {reviewed} reviewed.".format(
            label=attention.label,
            attention=attention.summary.needs_attention,
            reviewed=attention.summary.reviewed_total,
        ),
    )


def format_training_polygon_review_summary(summary):
    """Return short human-readable lines for the dock status panel."""
    accepted_pct = round(summary.accepted_rate * 100.0, 1)
    return (
        f"Total polygons: {summary.total}",
        f"Reviewed: {summary.reviewed_total} | Unreviewed: {summary.unreviewed}",
        f"Accepted: {summary.accepted} ({accepted_pct}%)",
        f"Needs attention: {summary.needs_attention} "
        f"({summary.rejected} rejected, {summary.unsure} unsure)",
    )


def _record_value(record, field_name):
    if isinstance(record, dict):
        return record.get(field_name)
    return getattr(record, field_name, None)


def _record_key(record, key_fields):
    return tuple(_record_value(record, field_name) for field_name in key_fields)


def _format_bucket_label(key_fields, key):
    parts = []
    for field_name, value in zip(key_fields, key):
        cleaned = str(value or "").strip()
        if cleaned:
            parts.append(f"{field_name}={cleaned}")
    return " | ".join(parts) if parts else "unspecified"
