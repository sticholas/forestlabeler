"""QGIS-facing canopy attempt logging."""

from __future__ import annotations

import csv
import os
import shutil
from dataclasses import dataclass
from dataclasses import replace
from datetime import datetime, timezone
from pathlib import Path

from qgis.core import QgsExpressionContextUtils, QgsProject

from ..forest_labeler_core.canopy_attempt_log import (
    CANOPY_ATTEMPT_ACCEPTED,
    CANOPY_ATTEMPT_CREATED,
    CANOPY_ATTEMPT_EDITED,
    CANOPY_ATTEMPT_REJECTED,
    CANOPY_ATTEMPT_REJECTED_REMOVED,
    CANOPY_ATTEMPT_RESTORED,
    CANOPY_ATTEMPT_UNSURE,
    CanopyAttemptLogRecord,
    canopy_attempt_log_fieldnames,
    new_canopy_attempt_id,
)
from ..forest_labeler_core.feedback_event_store import (
    append_feedback_event,
    feedback_event_export_rows,
    latest_feedback_event_type,
)
from ..forest_labeler_core.project_storage import (
    LEGACY_PROJECT_STORAGE_FOLDER,
    project_storage_folder_name,
)


@dataclass(frozen=True)
class CanopyAttemptLogResult:
    ok: bool
    path: str | None
    errors: tuple
    warnings: tuple


PROJECT_ID_VARIABLE = "forest_labeler_project_id"


def log_created_canopy_attempt(request, creation_result):
    """Log a generated canopy attempt after a successful feature write."""
    if not creation_result.ok or creation_result.write_result is None:
        return CanopyAttemptLogResult(True, None, (), ())

    record = created_canopy_attempt_record(request, creation_result)
    return append_canopy_attempt_log(record)


def created_canopy_attempt_record(request, creation_result):
    """Build the created-attempt record for logging and deletion monitoring."""
    write_result = creation_result.write_result
    values = write_result.attribute_plan.values if write_result.attribute_plan else {}
    return CanopyAttemptLogRecord(
        attempt_id=values.get("attempt_id") or request.attempt_id or new_canopy_attempt_id(),
        timestamp_utc=_utc_now(),
        event=CANOPY_ATTEMPT_CREATED,
        project_id=_project_id(),
        project_file=_project_file(),
        layer_id=request.target_layer.id() if request.target_layer is not None else "",
        layer_name=request.target_layer.name() if request.target_layer is not None else "",
        canopy_fid=values.get("fid"),
        qgis_feature_id=creation_result.feature_id,
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


def log_removed_canopy_attempt(layer, feature, note=None):
    """Log a rejected canopy before it is removed from the clean target layer."""
    fields = layer.fields()

    def attr(field_name):
        index = fields.indexOf(field_name)
        return feature[index] if index != -1 else None

    return append_canopy_attempt_log(
        CanopyAttemptLogRecord(
            attempt_id=attr("attempt_id") or new_canopy_attempt_id(),
            timestamp_utc=_utc_now(),
            event=CANOPY_ATTEMPT_REJECTED_REMOVED,
            project_id=_project_id(),
            project_file=_project_file(),
            layer_id=layer.id() if layer is not None else "",
            layer_name=layer.name(),
            canopy_fid=attr("fid"),
            qgis_feature_id=feature.id(),
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


def log_reviewed_canopy_attempt(layer, feature, status, note=None):
    """Log an accepted, rejected, or unsure review lifecycle event."""
    event_by_status = {
        "accepted": CANOPY_ATTEMPT_ACCEPTED,
        "rejected": CANOPY_ATTEMPT_REJECTED,
        "unsure": CANOPY_ATTEMPT_UNSURE,
    }
    event = event_by_status.get(str(status or "").strip().lower())
    if event is None:
        return CanopyAttemptLogResult(
            False,
            None,
            ("Canopy review event must be accepted, rejected, or unsure.",),
            (),
        )
    fields = layer.fields()

    def attr(field_name):
        index = fields.indexOf(field_name)
        return feature[index] if index != -1 else None

    attempt_id = attr("attempt_id")
    event_store_path = feedback_event_store_path()
    if attempt_id and latest_feedback_event_type(event_store_path, attempt_id) == event:
        return CanopyAttemptLogResult(True, str(event_store_path), (), ())

    return append_canopy_attempt_log(
        CanopyAttemptLogRecord(
            attempt_id=attempt_id or new_canopy_attempt_id(),
            timestamp_utc=_utc_now(),
            event=event,
            project_id=_project_id(),
            project_file=_project_file(),
            layer_id=layer.id() if layer is not None else "",
            layer_name=layer.name(),
            canopy_fid=attr("fid"),
            qgis_feature_id=feature.id(),
            canopy_mode=attr("mode"),
            crown_tightness=attr("tightness"),
            seed_radius_m=attr("radius_m"),
            area_m2=attr("area_m2"),
            apex_height_m=attr("apex_h"),
            refined=attr("refined"),
            chm_id=attr("chm_id"),
            ortho_id=attr("ortho_id"),
            species=attr("species"),
            review_status=event,
            note=note,
        )
    )


def log_removed_canopy_attempt_from_record(record, note=None):
    """Log a rejected/removal event from a cached created-attempt record."""
    event_store_path = feedback_event_store_path()
    if latest_feedback_event_type(event_store_path, record.attempt_id) == CANOPY_ATTEMPT_REJECTED_REMOVED:
        return CanopyAttemptLogResult(True, str(event_store_path), (), ())
    return append_canopy_attempt_log(
        CanopyAttemptLogRecord(
            attempt_id=record.attempt_id,
            timestamp_utc=_utc_now(),
            event=CANOPY_ATTEMPT_REJECTED_REMOVED,
            project_id=record.project_id,
            project_file=record.project_file,
            layer_id=record.layer_id,
            layer_name=record.layer_name,
            canopy_fid=record.canopy_fid,
            qgis_feature_id=record.qgis_feature_id,
            canopy_mode=record.canopy_mode,
            crown_tightness=record.crown_tightness,
            seed_radius_m=record.seed_radius_m,
            area_m2=record.area_m2,
            apex_height_m=record.apex_height_m,
            refined=record.refined,
            chm_id=record.chm_id,
            ortho_id=record.ortho_id,
            species=record.species,
            review_status="rejected",
            note=note,
        )
    )


def log_restored_canopy_attempt_from_record(record, note=None):
    """Record that QGIS restored a previously deleted canopy."""
    status = str(record.review_status or "").strip().lower()
    event = {
        "accepted": CANOPY_ATTEMPT_ACCEPTED,
        "rejected": CANOPY_ATTEMPT_REJECTED,
        "unsure": CANOPY_ATTEMPT_UNSURE,
    }.get(status, CANOPY_ATTEMPT_RESTORED)
    return append_canopy_attempt_log(
        replace(
            record,
            timestamp_utc=_utc_now(),
            event=event,
            note=note,
        )
    )


def log_edited_canopy_attempt_from_record(record, note=None):
    """Record a material edit that makes an earlier review stale."""
    return append_canopy_attempt_log(
        replace(
            record,
            timestamp_utc=_utc_now(),
            event=CANOPY_ATTEMPT_EDITED,
            review_status="unreviewed",
            note=note,
        )
    )


def canopy_attempt_record_from_feature(layer, feature, event=CANOPY_ATTEMPT_CREATED):
    """Build a stable lifecycle snapshot from an existing Forest Labeler crown."""
    fields = layer.fields()

    def attr(field_name):
        index = fields.indexOf(field_name)
        return feature[index] if index != -1 else None

    attempt_id = attr("attempt_id")
    if not attempt_id:
        return None
    return CanopyAttemptLogRecord(
        attempt_id=str(attempt_id),
        timestamp_utc=_utc_now(),
        event=event,
        project_id=_project_id(),
        project_file=_project_file(),
        layer_id=layer.id(),
        layer_name=layer.name(),
        canopy_fid=attr("fid"),
        qgis_feature_id=feature.id(),
        canopy_mode=attr("mode"),
        crown_tightness=attr("tightness"),
        seed_radius_m=attr("radius_m"),
        area_m2=attr("area_m2"),
        apex_height_m=attr("apex_h"),
        refined=attr("refined"),
        chm_id=attr("chm_id"),
        ortho_id=attr("ortho_id"),
        species=attr("species"),
        review_status=attr("review_status"),
    )


def append_canopy_attempt_log(record):
    event_store_path = feedback_event_store_path()
    event_store_result = append_feedback_event(event_store_path, record)
    if not event_store_result.ok:
        return CanopyAttemptLogResult(
            False,
            event_store_result.path,
            event_store_result.errors,
            (),
        )

    return CanopyAttemptLogResult(
        True,
        event_store_result.path,
        (),
        (),
    )


def export_canopy_attempt_csv(path=None):
    """Export a readable CSV snapshot from the durable project event store."""
    export_path = Path(path) if path is not None else canopy_attempt_csv_export_path()
    try:
        export_path.parent.mkdir(parents=True, exist_ok=True)
        rows = feedback_event_export_rows(feedback_event_store_path())
        with export_path.open("w", newline="", encoding="utf-8") as handle:
            writer = csv.DictWriter(handle, fieldnames=canopy_attempt_log_fieldnames())
            writer.writeheader()
            for row in rows:
                writer.writerow(
                    {
                        field: "" if row.get(field) is None else row.get(field)
                        for field in canopy_attempt_log_fieldnames()
                    }
                )
        return CanopyAttemptLogResult(True, str(export_path), (), (f"Exported {len(rows)} canopy event row(s).",))
    except Exception as exc:
        return CanopyAttemptLogResult(False, str(export_path), (f"Could not write canopy attempt CSV export: {exc}",), ())


def canopy_attempt_csv_export_path():
    return _project_feedback_directory() / "forest_labeler_canopy_attempts.csv"


def feedback_event_store_path():
    path = _project_feedback_directory() / "forest_labeler_feedback.sqlite3"
    _copy_legacy_feedback_store(path)
    return path


def _project_feedback_directory():
    directory = _project_home_directory() / project_storage_folder_name(_project_file_name())
    _migrate_legacy_feedback_directory(directory)
    return directory


def _project_home_directory():
    project = QgsProject.instance()
    home_path = Path(project.homePath()) if project.homePath() else None
    if home_path is None or str(home_path) == ".":
        file_name = project.fileName()
        home_path = Path(file_name).parent if file_name else Path.home()
    return home_path


def _project_file_name():
    try:
        file_name = QgsProject.instance().fileName()
    except Exception:
        return ""
    return Path(file_name).name if file_name else ""


def _migrate_legacy_feedback_directory(new_directory):
    legacy_directory = _project_home_directory() / LEGACY_PROJECT_STORAGE_FOLDER
    try:
        if not legacy_directory.exists() or legacy_directory == new_directory:
            return
        if not new_directory.exists():
            os.replace(str(legacy_directory), str(new_directory))
            return
        migrated_all = True
        for legacy_child in legacy_directory.iterdir():
            target = new_directory / legacy_child.name
            if target.exists():
                migrated_all = False
                continue
            if legacy_child.is_dir():
                shutil.copytree(str(legacy_child), str(target))
            else:
                shutil.copy2(str(legacy_child), str(target))
        if migrated_all:
            shutil.rmtree(str(legacy_directory))
    except Exception:
        pass


def _copy_legacy_feedback_store(new_path):
    legacy_path = _project_home_directory() / "forest_labeler_feedback.sqlite3"
    try:
        if legacy_path.exists() and not new_path.exists():
            new_path.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(str(legacy_path), str(new_path))
    except Exception:
        pass


def _project_id():
    project = QgsProject.instance()
    try:
        project_id = QgsExpressionContextUtils.projectScope(project).variable(PROJECT_ID_VARIABLE)
        if project_id:
            return str(project_id)
        project_id = new_canopy_attempt_id().replace("canopy-", "project-", 1)
        QgsExpressionContextUtils.setProjectVariable(project, PROJECT_ID_VARIABLE, project_id)
        return project_id
    except Exception:
        return None


def _project_file():
    try:
        return QgsProject.instance().fileName() or None
    except Exception:
        return None


def _utc_now():
    return datetime.now(timezone.utc).isoformat(timespec="microseconds")
