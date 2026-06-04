import sqlite3
import tempfile
import unittest
from dataclasses import replace
from pathlib import Path

from forest_labeler_core.canopy_attempt_log import (
    CANOPY_ATTEMPT_CREATED,
    CANOPY_ATTEMPT_REJECTED_REMOVED,
    CanopyAttemptLogRecord,
)
from forest_labeler_core.feedback_event_store import (
    SCHEMA_VERSION,
    append_feedback_event,
    feedback_event_id,
    recommendation_evidence_from_event_store,
)
from forest_labeler_core.learning_scopes import LearningContext, SCOPE_PROJECT


class FeedbackEventStoreTest(unittest.TestCase):
    def setUp(self):
        self.temp_directory = tempfile.TemporaryDirectory()
        self.database_path = Path(self.temp_directory.name) / "forest_labeler_feedback.sqlite3"
        self.created_record = CanopyAttemptLogRecord(
            attempt_id="canopy-abc123",
            timestamp_utc="2026-06-04T00:00:00+00:00",
            event=CANOPY_ATTEMPT_CREATED,
            project_id="project-001",
            project_file="project.qgz",
            layer_id="layer-001",
            layer_name="training_canopies",
            canopy_fid=12,
            qgis_feature_id=-3,
            canopy_mode="DENSE",
            crown_tightness=11,
            seed_radius_m=5.3,
            area_m2=43.58,
            apex_height_m=5.69,
            refined=1,
            chm_id="chm.tif",
            ortho_id="ortho.tif",
            species="Unprocessed",
            review_status="unreviewed",
        )

    def tearDown(self):
        self.temp_directory.cleanup()

    def test_append_creates_versioned_schema_and_linked_event(self):
        result = append_feedback_event(self.database_path, self.created_record)

        self.assertTrue(result.ok)
        self.assertTrue(result.inserted)
        with sqlite3.connect(self.database_path) as connection:
            self.assertEqual(connection.execute("SELECT version FROM schema_version").fetchone()[0], SCHEMA_VERSION)
            self.assertEqual(connection.execute("SELECT COUNT(*) FROM attempts").fetchone()[0], 1)
            self.assertEqual(connection.execute("SELECT COUNT(*) FROM events").fetchone()[0], 1)
            self.assertEqual(
                connection.execute("SELECT event_type FROM events").fetchone()[0],
                CANOPY_ATTEMPT_CREATED,
            )

    def test_duplicate_event_is_idempotent(self):
        first = append_feedback_event(self.database_path, self.created_record)
        second = append_feedback_event(self.database_path, self.created_record)

        self.assertTrue(first.inserted)
        self.assertFalse(second.inserted)
        with sqlite3.connect(self.database_path) as connection:
            self.assertEqual(connection.execute("SELECT COUNT(*) FROM events").fetchone()[0], 1)

    def test_rejection_adds_second_event_to_same_attempt(self):
        rejected = replace(
            self.created_record,
            timestamp_utc="2026-06-04T00:01:00+00:00",
            event=CANOPY_ATTEMPT_REJECTED_REMOVED,
            review_status="rejected",
            note="QGIS undo/delete observed",
        )

        append_feedback_event(self.database_path, self.created_record)
        append_feedback_event(self.database_path, rejected)

        with sqlite3.connect(self.database_path) as connection:
            self.assertEqual(connection.execute("SELECT COUNT(*) FROM attempts").fetchone()[0], 1)
            self.assertEqual(connection.execute("SELECT COUNT(*) FROM events").fetchone()[0], 2)

    def test_event_identity_is_stable_across_timestamps(self):
        later_duplicate = replace(self.created_record, timestamp_utc="2026-06-04T00:05:00+00:00")

        self.assertEqual(feedback_event_id(self.created_record), feedback_event_id(later_duplicate))

    def test_recommendation_evidence_uses_latest_review_event(self):
        accepted = replace(
            self.created_record,
            event="accepted",
            review_status="accepted",
            timestamp_utc="2026-06-04T00:01:00+00:00",
        )
        rejected = replace(
            self.created_record,
            event="rejected",
            review_status="rejected",
            timestamp_utc="2026-06-04T00:02:00+00:00",
        )
        append_feedback_event(self.database_path, self.created_record)
        append_feedback_event(self.database_path, accepted)
        append_feedback_event(self.database_path, rejected)

        evidence = recommendation_evidence_from_event_store(
            self.database_path,
            scope=SCOPE_PROJECT,
            context=LearningContext("label_canopy", "canopy-v1"),
        )

        self.assertEqual(len(evidence), 1)
        self.assertEqual(evidence[0].reviewed_total, 1)
        self.assertEqual(evidence[0].accepted_rate, 0.0)

    def test_qvariant_like_values_are_normalized_before_sqlite_write(self):
        wrapped_record = replace(
            self.created_record,
            species=FakeQVariant("Unprocessed"),
            chm_id=FakeQVariant(None),
            crown_tightness=FakeQVariant(17),
        )

        result = append_feedback_event(self.database_path, wrapped_record)

        self.assertTrue(result.ok)
        with sqlite3.connect(self.database_path) as connection:
            row = connection.execute(
                "SELECT species, chm_id, crown_tightness FROM attempts"
            ).fetchone()
        self.assertEqual(row, ("Unprocessed", None, 17))


class FakeQVariant:
    def __init__(self, value):
        self._value = value

    def isNull(self):
        return self._value is None

    def isValid(self):
        return True

    def value(self):
        return self._value


if __name__ == "__main__":
    unittest.main()
