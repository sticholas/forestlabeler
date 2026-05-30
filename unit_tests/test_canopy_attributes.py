import unittest

from forest_labeler_core.canopy_attributes import (
    CanopyAttributeInputs,
    build_canopy_attribute_plan,
    next_numeric_fid,
)


class CanopyAttributeTest(unittest.TestCase):
    def test_builds_attribute_plan_for_available_fields(self):
        plan = build_canopy_attribute_plan(
            CanopyAttributeInputs(
                next_fid=7,
                seed_radius_m=3.456,
                geometry_area_m2=41.987,
                apex_height_m=12.345,
                canopy_mode="MIXED",
                crown_tightness=11,
                species="MAM",
                reviewed=0,
                review_status="unreviewed",
                refined=1,
                chm_id="X:/rasters/chm.tif",
                ortho_id="X:/imagery/ortho.tif",
            ),
            available_fields={
                "fid",
                "radius_m",
                "diam_m",
                "area_m2",
                "apex_h",
                "mode",
                "tightness",
                "num_trees",
                "species",
                "reviewed",
                "review_status",
                "refined",
                "chm_id",
                "ortho_id",
            },
        )

        self.assertEqual(plan.values["fid"], 7)
        self.assertEqual(plan.values["radius_m"], 3.46)
        self.assertEqual(plan.values["diam_m"], 6.91)
        self.assertEqual(plan.values["area_m2"], 41.99)
        self.assertEqual(plan.values["apex_h"], 12.35)
        self.assertEqual(plan.values["tightness"], 11)
        self.assertEqual(plan.values["num_trees"], 1)
        self.assertEqual(plan.values["species"], "MAM")
        self.assertEqual(plan.values["review_status"], "unreviewed")
        self.assertEqual(plan.values["chm_id"], "X:/rasters/chm.tif")
        self.assertEqual(plan.values["ortho_id"], "X:/imagery/ortho.tif")
        self.assertEqual(plan.skipped_fields, ())

    def test_records_skipped_optional_fields(self):
        plan = build_canopy_attribute_plan(
            CanopyAttributeInputs(
                next_fid=None,
                seed_radius_m=2,
                geometry_area_m2=10,
                apex_height_m=None,
                canopy_mode="DENSE",
                species=None,
            ),
            available_fields={"species", "mode"},
        )

        self.assertEqual(plan.values, {"mode": "DENSE", "species": None})
        self.assertIn("radius_m", plan.skipped_fields)
        self.assertIn("fid", plan.skipped_fields)

    def test_next_numeric_fid_ignores_blank_and_invalid_values(self):
        self.assertEqual(next_numeric_fid([None, "", "abc", 1, "4", 3]), 5)
        self.assertEqual(next_numeric_fid([]), 1)


if __name__ == "__main__":
    unittest.main()
