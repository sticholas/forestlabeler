"""Durable SQLite event storage for Forest Labeler feedback."""

from __future__ import annotations

import hashlib
import sqlite3
from dataclasses import dataclass
from pathlib import Path

from .canopy_attempt_log import (
    CANOPY_ATTEMPT_ACCEPTED,
    CANOPY_ATTEMPT_EDITED,
    CANOPY_ATTEMPT_REJECTED,
    CANOPY_ATTEMPT_REJECTED_REMOVED,
    CANOPY_ATTEMPT_RESTORED,
    CANOPY_ATTEMPT_UNSURE,
    CanopyAttemptLogRecord,
)
from .learning_scopes import RecommendationEvidence


SCHEMA_VERSION = 1


@dataclass(frozen=True)
class FeedbackEventStoreResult:
    ok: bool
    inserted: bool
    path: str
    errors: tuple


def append_feedback_event(path, record: CanopyAttemptLogRecord):
    """Persist one immutable lifecycle event and its stable attempt context."""
    database_path = Path(path)
    try:
        database_path.parent.mkdir(parents=True, exist_ok=True)
        with sqlite3.connect(str(database_path)) as connection:
            _initialize_schema(connection)
            _upsert_attempt(connection, record)
            inserted = _insert_event(connection, record)
        return FeedbackEventStoreResult(True, inserted, str(database_path), ())
    except Exception as exc:
        return FeedbackEventStoreResult(
            False,
            False,
            str(database_path),
            (f"Could not write Forest Labeler feedback event store: {exc}",),
        )


def feedback_event_id(record: CanopyAttemptLogRecord):
    """Return a deterministic ID for one immutable lifecycle event."""
    identity = "|".join(
        (
            str(record.attempt_id),
            str(record.timestamp_utc),
            str(record.event),
            str(record.note or ""),
            str(record.review_status or ""),
        )
    )
    return hashlib.sha256(identity.encode("utf-8")).hexdigest()


def recommendation_evidence_from_event_store(path, scope, context, source_label=None):
    """Return reviewed canopy-tool evidence grouped by mode and tightness."""
    database_path = Path(path)
    if not database_path.exists():
        return ()

    with sqlite3.connect(str(database_path)) as connection:
        rows = connection.execute(
            """
            SELECT
                attempts.attempt_id,
                attempts.canopy_mode,
                attempts.crown_tightness,
                events.event_type
            FROM attempts
            JOIN events ON events.attempt_id = attempts.attempt_id
            WHERE events.event_type IN (?, ?, ?, ?, ?, ?)
            ORDER BY events.timestamp_utc, events.rowid
            """,
            (
                CANOPY_ATTEMPT_ACCEPTED,
                CANOPY_ATTEMPT_EDITED,
                CANOPY_ATTEMPT_REJECTED,
                CANOPY_ATTEMPT_UNSURE,
                CANOPY_ATTEMPT_REJECTED_REMOVED,
                CANOPY_ATTEMPT_RESTORED,
            ),
        ).fetchall()

    latest_by_attempt = {}
    for attempt_id, canopy_mode, crown_tightness, event_type in rows:
        latest_by_attempt[attempt_id] = (canopy_mode, crown_tightness, event_type)

    grouped = {}
    for canopy_mode, crown_tightness, event_type in latest_by_attempt.values():
        if event_type in {CANOPY_ATTEMPT_EDITED, CANOPY_ATTEMPT_RESTORED}:
            continue
        key = (str(canopy_mode or ""), _int_or_zero(crown_tightness))
        bucket = grouped.setdefault(key, {"reviewed": 0, "accepted": 0, "rejected": 0})
        bucket["reviewed"] += 1
        if event_type == CANOPY_ATTEMPT_ACCEPTED:
            bucket["accepted"] += 1
        elif event_type in {CANOPY_ATTEMPT_REJECTED, CANOPY_ATTEMPT_REJECTED_REMOVED}:
            bucket["rejected"] += 1

    return tuple(
        RecommendationEvidence(
            scope=scope,
            canopy_mode=canopy_mode,
            crown_tightness=crown_tightness,
            reviewed_total=summary["reviewed"],
            accepted_rate=summary["accepted"] / summary["reviewed"],
            context=context,
            source_label=source_label,
            accepted_total=summary["accepted"],
            rejected_total=summary["rejected"],
        )
        for (canopy_mode, crown_tightness), summary in sorted(grouped.items())
    )


def latest_feedback_event_type(path, attempt_id):
    """Return the latest persisted lifecycle event for one canopy attempt."""
    database_path = Path(path)
    if not database_path.exists() or not attempt_id:
        return None

    with sqlite3.connect(str(database_path)) as connection:
        _initialize_schema(connection)
        row = connection.execute(
            """
            SELECT event_type
            FROM events
            WHERE attempt_id = ?
            ORDER BY timestamp_utc DESC, rowid DESC
            LIMIT 1
            """,
            (_sqlite_value(attempt_id),),
        ).fetchone()
    return row[0] if row is not None else None


def _initialize_schema(connection):
    connection.execute("PRAGMA foreign_keys = ON")
    connection.execute(
        """
        CREATE TABLE IF NOT EXISTS schema_version (
            version INTEGER NOT NULL
        )
        """
    )
    current_version = connection.execute(
        "SELECT version FROM schema_version ORDER BY version DESC LIMIT 1"
    ).fetchone()
    if current_version is None:
        connection.execute("INSERT INTO schema_version(version) VALUES (?)", (SCHEMA_VERSION,))
    elif int(current_version[0]) > SCHEMA_VERSION:
        raise ValueError(
            f"Feedback database schema version {current_version[0]} is newer than supported version {SCHEMA_VERSION}."
        )

    connection.execute(
        """
        CREATE TABLE IF NOT EXISTS attempts (
            attempt_id TEXT PRIMARY KEY,
            project_id TEXT,
            project_file TEXT,
            layer_id TEXT,
            layer_name TEXT NOT NULL,
            canopy_fid INTEGER,
            qgis_feature_id INTEGER,
            canopy_mode TEXT,
            crown_tightness INTEGER,
            seed_radius_m REAL,
            area_m2 REAL,
            apex_height_m REAL,
            refined INTEGER,
            chm_id TEXT,
            ortho_id TEXT,
            species TEXT,
            created_at_utc TEXT NOT NULL
        )
        """
    )
    connection.execute(
        """
        CREATE TABLE IF NOT EXISTS events (
            event_id TEXT PRIMARY KEY,
            attempt_id TEXT NOT NULL,
            timestamp_utc TEXT NOT NULL,
            event_type TEXT NOT NULL,
            review_status TEXT,
            note TEXT,
            FOREIGN KEY(attempt_id) REFERENCES attempts(attempt_id)
        )
        """
    )
    connection.execute("CREATE INDEX IF NOT EXISTS idx_events_attempt_id ON events(attempt_id)")
    connection.execute("CREATE INDEX IF NOT EXISTS idx_events_type ON events(event_type)")
    connection.execute("CREATE INDEX IF NOT EXISTS idx_events_timestamp ON events(timestamp_utc)")


def _upsert_attempt(connection, record):
    connection.execute(
        """
        INSERT INTO attempts (
            attempt_id, project_id, project_file, layer_id, layer_name,
            canopy_fid, qgis_feature_id, canopy_mode, crown_tightness,
            seed_radius_m, area_m2, apex_height_m, refined, chm_id,
            ortho_id, species, created_at_utc
        ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        ON CONFLICT(attempt_id) DO UPDATE SET
            project_id = COALESCE(excluded.project_id, attempts.project_id),
            project_file = COALESCE(excluded.project_file, attempts.project_file),
            layer_id = COALESCE(excluded.layer_id, attempts.layer_id),
            layer_name = COALESCE(excluded.layer_name, attempts.layer_name),
            canopy_fid = COALESCE(excluded.canopy_fid, attempts.canopy_fid),
            qgis_feature_id = COALESCE(excluded.qgis_feature_id, attempts.qgis_feature_id),
            canopy_mode = COALESCE(excluded.canopy_mode, attempts.canopy_mode),
            crown_tightness = COALESCE(excluded.crown_tightness, attempts.crown_tightness),
            seed_radius_m = COALESCE(excluded.seed_radius_m, attempts.seed_radius_m),
            area_m2 = COALESCE(excluded.area_m2, attempts.area_m2),
            apex_height_m = COALESCE(excluded.apex_height_m, attempts.apex_height_m),
            refined = COALESCE(excluded.refined, attempts.refined),
            chm_id = COALESCE(excluded.chm_id, attempts.chm_id),
            ortho_id = COALESCE(excluded.ortho_id, attempts.ortho_id),
            species = COALESCE(excluded.species, attempts.species)
        """,
        _sqlite_values(
            record.attempt_id,
            record.project_id,
            record.project_file,
            record.layer_id,
            record.layer_name,
            record.canopy_fid,
            record.qgis_feature_id,
            record.canopy_mode,
            record.crown_tightness,
            record.seed_radius_m,
            record.area_m2,
            record.apex_height_m,
            record.refined,
            record.chm_id,
            record.ortho_id,
            record.species,
            record.timestamp_utc,
        ),
    )


def _insert_event(connection, record):
    cursor = connection.execute(
        """
        INSERT OR IGNORE INTO events (
            event_id, attempt_id, timestamp_utc, event_type, review_status, note
        ) VALUES (?, ?, ?, ?, ?, ?)
        """,
        _sqlite_values(
            feedback_event_id(record),
            record.attempt_id,
            record.timestamp_utc,
            record.event,
            record.review_status,
            record.note,
        ),
    )
    return cursor.rowcount > 0


def _sqlite_values(*values):
    return tuple(_sqlite_value(value) for value in values)


def _sqlite_value(value):
    """Convert QGIS/PyQt wrapper values into SQLite-supported native values."""
    if value is None or isinstance(value, (str, int, float, bytes)):
        return value

    try:
        if hasattr(value, "isNull") and value.isNull():
            return None
    except Exception:
        pass

    try:
        if hasattr(value, "isValid") and not value.isValid():
            return None
    except Exception:
        pass

    try:
        if hasattr(value, "value"):
            unwrapped = value.value()
            if unwrapped is not value:
                return _sqlite_value(unwrapped)
    except Exception:
        pass

    return str(value)


def _int_or_zero(value):
    try:
        return int(value)
    except (TypeError, ValueError):
        return 0
