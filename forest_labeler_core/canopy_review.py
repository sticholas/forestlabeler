"""Canopy review summaries for evaluating press-hold tool settings."""

from __future__ import annotations

from dataclasses import dataclass


REVIEW_STATUS_ACCEPTED = "accepted"
REVIEW_STATUS_REJECTED = "rejected"
REVIEW_STATUS_UNSURE = "unsure"
REVIEW_STATUS_UNREVIEWED = "unreviewed"
CANOPY_REVIEW_FILTER_UNREVIEWED = "unreviewed"
CANOPY_REVIEW_FILTER_ATTENTION = "attention"

REVIEWED_FLAG_BY_STATUS = {
    REVIEW_STATUS_ACCEPTED: 1,
    REVIEW_STATUS_REJECTED: -1,
    REVIEW_STATUS_UNSURE: 0,
    REVIEW_STATUS_UNREVIEWED: 0,
}


@dataclass(frozen=True)
class CanopyReviewSummary:
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
class CanopyReviewBucket:
    key: tuple
    label: str
    summary: CanopyReviewSummary


@dataclass(frozen=True)
class CanopyToolRecommendation:
    canopy_mode: str
    crown_tightness: int | None
    accepted_rate: float
    reviewed_total: int


def normalize_canopy_review_status(status, reviewed=None):
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


def canopy_review_status_matches_filter(status, reviewed, review_filter):
    normalized = normalize_canopy_review_status(status, reviewed)
    if review_filter == CANOPY_REVIEW_FILTER_UNREVIEWED:
        return normalized == REVIEW_STATUS_UNREVIEWED
    if review_filter == CANOPY_REVIEW_FILTER_ATTENTION:
        return normalized in {REVIEW_STATUS_REJECTED, REVIEW_STATUS_UNSURE}
    raise ValueError("Unknown canopy review filter: " + str(review_filter))


def summarize_canopy_reviews(records):
    counts = {
        REVIEW_STATUS_ACCEPTED: 0,
        REVIEW_STATUS_REJECTED: 0,
        REVIEW_STATUS_UNSURE: 0,
        REVIEW_STATUS_UNREVIEWED: 0,
    }
    total = 0
    for record in records:
        total += 1
        counts[
            normalize_canopy_review_status(
                _record_value(record, "review_status"),
                _record_value(record, "reviewed"),
            )
        ] += 1
    return CanopyReviewSummary(
        total=total,
        accepted=counts[REVIEW_STATUS_ACCEPTED],
        rejected=counts[REVIEW_STATUS_REJECTED],
        unsure=counts[REVIEW_STATUS_UNSURE],
        unreviewed=counts[REVIEW_STATUS_UNREVIEWED],
    )


def summarize_canopy_reviews_by_tool(records):
    grouped = {}
    for record in records:
        key = (_record_value(record, "mode"), _record_value(record, "tightness"))
        grouped.setdefault(key, []).append(record)

    buckets = []
    for key, bucket_records in grouped.items():
        buckets.append(
            CanopyReviewBucket(
                key=key,
                label=_format_tool_label(key),
                summary=summarize_canopy_reviews(bucket_records),
            )
        )
    return sorted(buckets, key=lambda bucket: bucket.label)


def best_canopy_tool_recommendation(records, min_reviewed=3):
    eligible = [
        bucket for bucket in summarize_canopy_reviews_by_tool(records)
        if bucket.summary.reviewed_total >= min_reviewed
    ]
    if not eligible:
        return None
    best = max(
        eligible,
        key=lambda bucket: (
            bucket.summary.accepted_rate,
            bucket.summary.reviewed_total,
            -bucket.summary.needs_attention,
        ),
    )
    mode, tightness = best.key
    return CanopyToolRecommendation(
        canopy_mode=str(mode or ""),
        crown_tightness=_int_or_none(tightness),
        accepted_rate=best.summary.accepted_rate,
        reviewed_total=best.summary.reviewed_total,
    )


def canopy_quality_insight_lines(records, min_reviewed=3):
    eligible = [
        bucket for bucket in summarize_canopy_reviews_by_tool(records)
        if bucket.summary.reviewed_total >= min_reviewed
    ]
    if not eligible:
        return (
            f"Canopy tool insights need at least {min_reviewed} reviewed crowns per mode/tightness setting.",
        )

    best = max(
        eligible,
        key=lambda bucket: (
            bucket.summary.accepted_rate,
            bucket.summary.reviewed_total,
            -bucket.summary.needs_attention,
        ),
    )
    attention = max(
        eligible,
        key=lambda bucket: (
            bucket.summary.needs_attention,
            -bucket.summary.accepted_rate,
            bucket.summary.reviewed_total,
        ),
    )
    return (
        "Best canopy tool: {label} | {accepted_pct}% accepted across {reviewed} reviewed.".format(
            label=best.label,
            accepted_pct=round(best.summary.accepted_rate * 100.0, 1),
            reviewed=best.summary.reviewed_total,
        ),
        "Watch canopy tool: {label} | {attention} need attention across {reviewed} reviewed.".format(
            label=attention.label,
            attention=attention.summary.needs_attention,
            reviewed=attention.summary.reviewed_total,
        ),
    )


def format_canopy_review_summary(summary):
    accepted_pct = round(summary.accepted_rate * 100.0, 1)
    return (
        f"Total canopies: {summary.total}",
        f"Reviewed: {summary.reviewed_total} | Unreviewed: {summary.unreviewed}",
        f"Accepted: {summary.accepted} ({accepted_pct}%)",
        f"Needs attention: {summary.needs_attention} "
        f"({summary.rejected} rejected, {summary.unsure} unsure)",
    )


def _record_value(record, field_name):
    if isinstance(record, dict):
        return record.get(field_name)
    return getattr(record, field_name, None)


def _format_tool_label(key):
    mode, tightness = key
    mode_text = str(mode or "unspecified")
    tightness_text = str(tightness) if tightness not in (None, "") else "unspecified"
    return f"mode={mode_text} | tightness={tightness_text}"


def _int_or_none(value):
    try:
        return int(value)
    except (TypeError, ValueError):
        return None
