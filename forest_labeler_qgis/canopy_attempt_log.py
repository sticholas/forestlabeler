"""QGIS-facing canopy attempt logging."""

from __future__ import annotations

import csv
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path

from qgis.core import QgsProject

from ..forest_labeler_core.canopy_attempt_log import (
    CANOPY_ATTEMPT_CREATED,
    CANOPY_ATTEMPT_REJECTED_REMOVED,
    CanopyAttemptLogRecord,
    canopy_attempt_log_fieldnames,
    canopy_attempt_log_row,
)


@dataclass(frozen=True)
class CanopyAttemptLogResult:
    ok: bool
    path: str | None
    errors: tuple
    warnings: tuple


def log_created_canopy_attempt(request, creation_result):
    """Log a generated canopy attempt after a successful feature write."""
    if not creation_result.ok or creation_result.write_result is None:
        return CanopyAttemptLogResult(True, None, (), ())

    write_result = creation_result.write_result
    values = write_result.attribute_plan.values if write_result.attribute_plan else {}
    return append_canopy_attempt_log(
        CanopyAttemptLogRecord(
            timestamp_utc=_utc_now(),
            event=CANOPY_ATTEMPT_CREATED,
            feature_id=creation_result.feature_id,
            layer_name=request.target_layer.name() if request.target_layer is not None else "",
            canopy_mode=request.canopy_mode,
            crown_tightness=request.crown_tightness,
            seed_radius_m=request.seed_radius_m,
            area_m2=values.get("area_m2"),
            apex_height_m=request.apex_height_m,
            refined=request.refined,
            chm_id=request.chm_id,
            ortho_id=request.ortho_id,
            species=values.get("species"),
            review_status=values.get("review_status"),
        )
    )


def log_removed_canopy_attempt(layer, feature, note=None):
    """Log a rejected canopy before it is removed from the clean target layer."""
    fields = layer.fields()

    def attr(field_name):
        index = fields.indexOf(field_name)
        return feature[index] if index != -1 else None

    return append_canopy_attempt_log(
        CanopyAttemptLogRecord(
            timestamp_utc=_utc_now(),
            event=CANOPY_ATTEMPT_REJECTED_REMOVED,
            feature_id=feature.id(),
            layer_name=layer.name(),
            canopy_mode=attr("mode"),
            crown_tightness=attr("tightness"),
            seed_radius_m=attr("radius_m"),
            area_m2=attr("area_m2"),
            apex_height_m=attr("apex_h"),
            refined=attr("refined"),
            chm_id=attr("chm_id"),
            ortho_id=attr("ortho_id"),
            species=attr("species"),
            review_status="rejected",
            note=note,
        )
    )


def append_canopy_attempt_log(record):
    path = _attempt_log_path()
    try:
        path.parent.mkdir(parents=True, exist_ok=True)
        file_exists = path.exists()
        with path.open("a", newline="", encoding="utf-8") as handle:
            writer = csv.DictWriter(handle, fieldnames=canopy_attempt_log_fieldnames())
            if not file_exists:
                writer.writeheader()
            writer.writerow(canopy_attempt_log_row(record))
        return CanopyAttemptLogResult(True, str(path), (), ())
    except Exception as exc:
        return CanopyAttemptLogResult(False, str(path), (f"Could not write canopy attempt log: {exc}",), ())


def _attempt_log_path():
    project = QgsProject.instance()
    home_path = Path(project.homePath()) if project.homePath() else None
    if home_path is None or str(home_path) == ".":
        file_name = project.fileName()
        home_path = Path(file_name).parent if file_name else Path.home()
    return home_path / "forest_labeler_canopy_attempts.csv"


def _utc_now():
    return datetime.now(timezone.utc).isoformat(timespec="seconds")
