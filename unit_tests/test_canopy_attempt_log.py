import unittest

from forest_labeler_core.canopy_attempt_log import (
    CANOPY_ATTEMPT_CREATED,
    CanopyAttemptLogRecord,
    canopy_attempt_log_fieldnames,
    canopy_attempt_log_row,
)


class CanopyAttemptLogTest(unittest.TestCase):
    def test_canopy_attempt_log_row_is_csv_safe(self):
        record = CanopyAttemptLogRecord(
            attempt_id="canopy-abc123",
            timestamp_utc="2026-06-01T00:00:00+00:00",
            event=CANOPY_ATTEMPT_CREATED,
            project_id="project-001",
            project_file="X:/project/forest.qgz",
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
            chm_id=None,
            ortho_id="X:/ortho.tif",
            species="Unprocessed",
            review_status="unreviewed",
        )

        row = canopy_attempt_log_row(record)

        self.assertEqual(row["attempt_id"], "canopy-abc123")
        self.assertEqual(row["canopy_fid"], 12)
        self.assertEqual(row["qgis_feature_id"], -3)
        self.assertEqual(row["chm_id"], "")
        self.assertEqual(row["ortho_id"], "X:/ortho.tif")
        self.assertEqual(canopy_attempt_log_fieldnames()[0], "attempt_id")


if __name__ == "__main__":
    unittest.main()
