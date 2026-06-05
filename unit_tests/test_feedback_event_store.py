import sqlite3
import tempfile
import unittest
from dataclasses import replace
from pathlib import Path

from forest_labeler_core.canopy_attempt_log import (
    CANOPY_ATTEMPT_CREATED,
    CANOPY_ATTEMPT_EDITED,
    CANOPY_ATTEMPT_REJECTED_REMOVED,
    CANOPY_ATTEMPT_RESTORED,
    CanopyAttemptLogRecord,
)
from forest_labeler_core.feedback_event_store import (
    SCHEMA_VERSION,
    append_feedback_event,
    feedback_event_export_rows,
    feedback_event_id,
    inspect_feedback_event_store,
    latest_feedback_event_type,
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
        self.assertEqual(
            latest_feedback_event_type(self.database_path, self.created_record.attempt_id),
            CANOPY_ATTEMPT_REJECTED_REMOVED,
        )

    def test_exports_event_rows_with_attempt_context(self):
        rejected = replace(
            self.created_record,
            timestamp_utc="2026-06-04T00:01:00+00:00",
            event=CANOPY_ATTEMPT_REJECTED_REMOVED,
            review_status="rejected",
            note="manual cleanup",
        )
        append_feedback_event(self.database_path, self.created_record)
        append_feedback_event(self.database_path, rejected)

        rows = feedback_event_export_rows(self.database_path)

        self.assertEqual(len(rows), 2)
        self.assertEqual(rows[0]["event"], CANOPY_ATTEMPT_CREATED)
        self.assertEqual(rows[1]["event"], CANOPY_ATTEMPT_REJECTED_REMOVED)
        self.assertEqual(rows[1]["attempt_id"], "canopy-abc123")
        self.assertEqual(rows[1]["canopy_mode"], "DENSE")
        self.assertEqual(rows[1]["note"], "manual cleanup")

    def test_inspection_summary_reports_events_and_latest_states(self):
        accepted = replace(
            self.created_record,
            timestamp_utc="2026-06-04T00:01:00+00:00",
            event="accepted",
            review_status="accepted",
        )
        append_feedback_event(self.database_path, self.created_record)
        append_feedback_event(self.database_path, accepted)

        summary = inspect_feedback_event_store(self.database_path)

        self.assertTrue(summary.exists)
        self.assertEqual(summary.health_status, "ok")
        self.assertEqual(summary.health_checks, ())
        self.assertEqual(summary.attempt_total, 1)
        self.assertEqual(summary.event_total, 2)
        self.assertIn(("accepted", 1), summary.event_counts)
        self.assertIn(("accepted", 1), summary.latest_state_counts)
        self.assertIn(("DENSE / tightness 11", 1), summary.recommended_setting_counts)

    def test_inspection_summary_flags_crowns_needing_review(self):
        edited = replace(
            self.created_record,
            timestamp_utc="2026-06-04T00:01:00+00:00",
            event=CANOPY_ATTEMPT_EDITED,
            review_status="unreviewed",
        )
        append_feedback_event(self.database_path, self.created_record)
        append_feedback_event(self.database_path, edited)

        summary = inspect_feedback_event_store(self.database_path)

        self.assertEqual(summary.health_status, "attention")
        self.assertIn("1 crown(s) need review after edit or restoration.", summary.health_checks)
        self.assertIn((CANOPY_ATTEMPT_EDITED, 1), summary.latest_state_counts)

    def test_event_identity_distinguishes_repeated_lifecycle_transitions(self):
        later_duplicate = replace(self.created_record, timestamp_utc="2026-06-04T00:05:00+00:00")

        self.assertNotEqual(feedback_event_id(self.created_record), feedback_event_id(later_duplicate))

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
        self.assertEqual(evidence[0].accepted_total, 0)
        self.assertEqual(evidence[0].rejected_total, 1)

    def test_removed_after_accept_no_longer_counts_as_accepted_support(self):
        accepted = replace(
            self.created_record,
            event="accepted",
            review_status="accepted",
            timestamp_utc="2026-06-04T00:01:00+00:00",
        )
        removed = replace(
            self.created_record,
            event=CANOPY_ATTEMPT_REJECTED_REMOVED,
            review_status="rejected",
            timestamp_utc="2026-06-04T00:02:00+00:00",
            note="Ctrl+Z quick reject",
        )
        append_feedback_event(self.database_path, self.created_record)
        append_feedback_event(self.database_path, accepted)
        append_feedback_event(self.database_path, removed)

        evidence = recommendation_evidence_from_event_store(
            self.database_path,
            scope=SCOPE_PROJECT,
            context=LearningContext("label_canopy", "canopy-v1"),
        )

        self.assertEqual(evidence[0].reviewed_total, 1)
        self.assertEqual(evidence[0].accepted_total, 0)
        self.assertEqual(evidence[0].rejected_total, 1)
        self.assertEqual(evidence[0].accepted_rate, 0.0)

    def test_repeated_remove_after_reaccept_is_not_collapsed(self):
        first_removed = replace(
            self.created_record,
            event=CANOPY_ATTEMPT_REJECTED_REMOVED,
            review_status="rejected",
            timestamp_utc="2026-06-04T00:01:00+00:00",
            note="Ctrl+Z quick reject",
        )
        accepted = replace(
            self.created_record,
            event="accepted",
            review_status="accepted",
            timestamp_utc="2026-06-04T00:02:00+00:00",
        )
        second_removed = replace(
            first_removed,
            timestamp_utc="2026-06-04T00:03:00+00:00",
        )
        for record in (self.created_record, first_removed, accepted, second_removed):
            append_feedback_event(self.database_path, record)

        with sqlite3.connect(self.database_path) as connection:
            event_count = connection.execute("SELECT COUNT(*) FROM events").fetchone()[0]
        evidence = recommendation_evidence_from_event_store(
            self.database_path,
            scope=SCOPE_PROJECT,
            context=LearningContext("label_canopy", "canopy-v1"),
        )

        self.assertEqual(event_count, 4)
        self.assertEqual(evidence[0].accepted_total, 0)
        self.assertEqual(evidence[0].rejected_total, 1)

    def test_restored_unreviewed_crown_no_longer_counts_as_rejected(self):
        removed = replace(
            self.created_record,
            event=CANOPY_ATTEMPT_REJECTED_REMOVED,
            review_status="rejected",
            timestamp_utc="2026-06-04T00:01:00+00:00",
        )
        restored = replace(
            self.created_record,
            event=CANOPY_ATTEMPT_RESTORED,
            review_status="unreviewed",
            timestamp_utc="2026-06-04T00:02:00+00:00",
        )
        for record in (self.created_record, removed, restored):
            append_feedback_event(self.database_path, record)

        evidence = recommendation_evidence_from_event_store(
            self.database_path,
            scope=SCOPE_PROJECT,
            context=LearningContext("label_canopy", "canopy-v1"),
        )

        self.assertEqual(evidence, ())

    def test_material_edit_invalidates_previous_acceptance(self):
        accepted = replace(
            self.created_record,
            event="accepted",
            review_status="accepted",
            timestamp_utc="2026-06-04T00:01:00+00:00",
        )
        edited = replace(
            self.created_record,
            event=CANOPY_ATTEMPT_EDITED,
            review_status="unreviewed",
            timestamp_utc="2026-06-04T00:02:00+00:00",
        )
        for record in (self.created_record, accepted, edited):
            append_feedback_event(self.database_path, record)

        evidence = recommendation_evidence_from_event_store(
            self.database_path,
            scope=SCOPE_PROJECT,
            context=LearningContext("label_canopy", "canopy-v1"),
        )

        self.assertEqual(evidence, ())

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
