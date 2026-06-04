import tempfile
import unittest
from dataclasses import replace
from pathlib import Path

from forest_labeler_core.canopy_attempt_log import CanopyAttemptLogRecord
from forest_labeler_core.canopy_recommendations import (
    UNIVERSAL_CANOPY_MODE,
    UNIVERSAL_CROWN_TIGHTNESS,
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


if __name__ == "__main__":
    unittest.main()
