"""Canopy attempt log records for learning from kept and removed crowns."""

from __future__ import annotations

from dataclasses import dataclass, fields
from uuid import uuid4


CANOPY_ATTEMPT_CREATED = "created"
CANOPY_ATTEMPT_REJECTED_REMOVED = "rejected_removed"
CANOPY_ATTEMPT_ACCEPTED = "accepted"
CANOPY_ATTEMPT_REJECTED = "rejected"
CANOPY_ATTEMPT_UNSURE = "unsure"
CANOPY_ATTEMPT_RESTORED = "restored"
CANOPY_ATTEMPT_EDITED = "edited"


@dataclass(frozen=True)
class CanopyAttemptLogRecord:
    attempt_id: str
    timestamp_utc: str
    event: str
    project_id: str | None
    project_file: str | None
    layer_id: str | None
    layer_name: str
    canopy_fid: int | None
    qgis_feature_id: int | None
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


def new_canopy_attempt_id():
    """Return a globally unique ID for linking canopy features to feedback logs."""
    return f"canopy-{uuid4().hex}"


def canopy_attempt_log_fieldnames():
    return [field.name for field in fields(CanopyAttemptLogRecord)]


def canopy_attempt_log_row(record):
    """Return a CSV-safe row dict for a canopy attempt record."""
    row = {}
    for field_name in canopy_attempt_log_fieldnames():
        value = getattr(record, field_name)
        row[field_name] = "" if value is None else value
    return row
