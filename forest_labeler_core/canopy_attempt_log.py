"""Canopy attempt log records for learning from kept and removed crowns."""

from __future__ import annotations

from dataclasses import dataclass, fields


CANOPY_ATTEMPT_CREATED = "created"
CANOPY_ATTEMPT_REJECTED_REMOVED = "rejected_removed"


@dataclass(frozen=True)
class CanopyAttemptLogRecord:
    timestamp_utc: str
    event: str
    feature_id: int | None
    layer_name: str
    canopy_mode: str
    crown_tightness: int | None
    seed_radius_m: float | None
    area_m2: float | None
    apex_height_m: float | None
    refined: int | None
    chm_id: str | None
    ortho_id: str | None
    species: str | None
    review_status: str | None
    note: str | None = None


def canopy_attempt_log_fieldnames():
    return [field.name for field in fields(CanopyAttemptLogRecord)]


def canopy_attempt_log_row(record):
    """Return a CSV-safe row dict for a canopy attempt record."""
    row = {}
    for field_name in canopy_attempt_log_fieldnames():
        value = getattr(record, field_name)
        row[field_name] = "" if value is None else value
    return row
