import tempfile
import unittest
from dataclasses import replace
from pathlib import Path

from forest_labeler_core.canopy_attempt_log import CanopyAttemptLogRecord
from forest_labeler_core.canopy_attempt_log import CANOPY_ATTEMPT_REJECTED_REMOVED
from forest_labeler_core.canopy_recommendations import (
    UNIVERSAL_CANOPY_MODE,
    UNIVERSAL_CROWN_TIGHTNESS,
    canopy_recommendation_lab,
    recommend_canopy_setting,
)
from forest_labeler_core.feedback_event_store import append_feedback_event
from forest_labeler_core.learning_scopes import SCOPE_PROJECT, SCOPE_UNIVERSAL


class CanopyRecommendationsTest(unittest.TestCase):
    def setUp(self):
        self.temp_directory = tempfile.TemporaryDirectory()
        self.database_path = Path(self.temp_directory.name) / "feedback.sqlite3"

    def tearDown(self):
        self.temp_directory.cleanup()

    def test_new_user_receives_universal_baseline(self):
        recommendation = recommend_canopy_setting(self.database_path)

        self.assertEqual(recommendation.evidence.scope, SCOPE_UNIVERSAL)
        self.assertEqual(recommendation.evidence.canopy_mode, UNIVERSAL_CANOPY_MODE)
        self.assertEqual(recommendation.evidence.crown_tightness, UNIVERSAL_CROWN_TIGHTNESS)

    def test_project_reviews_override_universal_baseline(self):
        for index in range(3):
            created = self._record(
                attempt_id=f"canopy-{index}",
                event="created",
                timestamp=f"2026-06-04T00:0{index}:00+00:00",
            )
            accepted = replace(
                created,
                event="accepted",
                review_status="accepted",
                timestamp_utc=f"2026-06-04T01:0{index}:00+00:00",
            )
            append_feedback_event(self.database_path, created)
            append_feedback_event(self.database_path, accepted)

        recommendation = recommend_canopy_setting(self.database_path, min_reviewed=3)

        self.assertEqual(recommendation.evidence.scope, SCOPE_PROJECT)
        self.assertEqual(recommendation.evidence.canopy_mode, "DENSE")
        self.assertEqual(recommendation.evidence.crown_tightness, 17)
        self.assertIn("this project", recommendation.explanation)
        self.assertIn("3 accepted, 0 rejected or removed", recommendation.explanation)

    def test_removed_accepted_crown_reduces_recommendation_support(self):
        for index in range(3):
            created = self._record(
                attempt_id=f"canopy-{index}",
                event="created",
                timestamp=f"2026-06-04T00:0{index}:00+00:00",
            )
            accepted = replace(
                created,
                event="accepted",
                review_status="accepted",
                timestamp_utc=f"2026-06-04T01:0{index}:00+00:00",
            )
            append_feedback_event(self.database_path, created)
            append_feedback_event(self.database_path, accepted)
            if index == 2:
                append_feedback_event(
                    self.database_path,
                    replace(
                        created,
                        event=CANOPY_ATTEMPT_REJECTED_REMOVED,
                        review_status="rejected",
                        timestamp_utc="2026-06-04T02:00:00+00:00",
                    ),
                )

        recommendation = recommend_canopy_setting(self.database_path, min_reviewed=3)

        self.assertEqual(recommendation.evidence.accepted_total, 2)
        self.assertEqual(recommendation.evidence.rejected_total, 1)
        self.assertAlmostEqual(recommendation.evidence.accepted_rate, 2 / 3)
        self.assertIn("2 accepted, 1 rejected or removed", recommendation.explanation)

    def test_recommendation_lab_ranks_and_marks_eligible_settings(self):
        self._append_reviewed_setting("DENSE", 17, accepted_count=4, rejected_count=0)
        self._append_reviewed_setting("MIXED", 11, accepted_count=2, rejected_count=2)

        lab = canopy_recommendation_lab(self.database_path, min_reviewed=3)

        self.assertTrue(lab.ready_for_project_recommendations)
        self.assertIn("DENSE at tightness 17", lab.next_action)
        self.assertEqual(lab.assessments[0].evidence.canopy_mode, "DENSE")
        self.assertTrue(lab.assessments[0].eligible)
        self.assertEqual(lab.assessments[0].confidence, "low")

    def test_recommendation_lab_explains_how_to_unlock_project_evidence(self):
        self._append_reviewed_setting("SPARSE", 5, accepted_count=2, rejected_count=0)

        lab = canopy_recommendation_lab(self.database_path, min_reviewed=3)

        self.assertFalse(lab.ready_for_project_recommendations)
        self.assertIn("Review 1 more canopy crown", lab.next_action)
        self.assertFalse(lab.assessments[0].eligible)

    def _record(self, attempt_id, event, timestamp):
        return CanopyAttemptLogRecord(
            attempt_id=attempt_id,
            timestamp_utc=timestamp,
            event=event,
            project_id="project-001",
            project_file="project.qgz",
            layer_id="layer-001",
            layer_name="training_canopies",
            canopy_fid=None,
            qgis_feature_id=None,
            canopy_mode="DENSE",
            crown_tightness=17,
            seed_radius_m=5.0,
            area_m2=40.0,
            apex_height_m=7.0,
            refined=1,
            chm_id="chm.tif",
            ortho_id="ortho.tif",
            species="Unprocessed",
            review_status="unreviewed",
        )

    def _append_reviewed_setting(self, mode, tightness, accepted_count, rejected_count):
        index = 0
        for status, count in (("accepted", accepted_count), ("rejected", rejected_count)):
            for _ in range(count):
                attempt_id = f"{mode}-{tightness}-{status}-{index}"
                created = replace(
                    self._record(
                        attempt_id=attempt_id,
                        event="created",
                        timestamp=f"2026-06-04T00:{index:02d}:00+00:00",
                    ),
                    canopy_mode=mode,
                    crown_tightness=tightness,
                )
                reviewed = replace(
                    created,
                    event=status,
                    review_status=status,
                    timestamp_utc=f"2026-06-04T01:{index:02d}:00+00:00",
                )
                append_feedback_event(self.database_path, created)
                append_feedback_event(self.database_path, reviewed)
                index += 1


if __name__ == "__main__":
    unittest.main()
