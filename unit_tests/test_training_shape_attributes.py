import unittest

from forest_labeler_core.training_shape_attributes import (
    TrainingShapeAttributeInputs,
    build_training_shape_attribute_plan,
)


class TrainingShapeAttributeTest(unittest.TestCase):
    def test_builds_attribute_plan_for_available_fields(self):
        plan = build_training_shape_attribute_plan(
            TrainingShapeAttributeInputs(
                next_fid=12,
                segment_length_m=25.678,
                vertex_count=6,
                shape_name="hexagon",
                angle_deg=33.333,
                geometry_area_m2=1624.567,
                ortho_id="X:/imagery/ortho.tif",
            ),
            available_fields={
                "fid",
                "segment_m",
                "side_m",
                "nodes",
                "vertices",
                "shape",
                "angle",
                "area_m2",
                "ortho_id",
            },
        )

        self.assertEqual(plan.values["fid"], 12)
        self.assertEqual(plan.values["segment_m"], 25.68)
        self.assertEqual(plan.values["side_m"], 25.68)
        self.assertEqual(plan.values["nodes"], 6)
        self.assertEqual(plan.values["vertices"], 6)
        self.assertEqual(plan.values["shape"], "hexagon")
        self.assertEqual(plan.values["angle"], 33.33)
        self.assertEqual(plan.values["area_m2"], 1624.57)
        self.assertEqual(plan.values["ortho_id"], "X:/imagery/ortho.tif")

    def test_records_skipped_optional_fields(self):
        plan = build_training_shape_attribute_plan(
            TrainingShapeAttributeInputs(
                next_fid=None,
                segment_length_m=100,
                vertex_count=4,
                shape_name="square",
                angle_deg=0,
                geometry_area_m2=10000,
            ),
            available_fields={"shape"},
        )

        self.assertEqual(plan.values, {"shape": "square"})
        self.assertIn("segment_m", plan.skipped_fields)
        self.assertIn("fid", plan.skipped_fields)


if __name__ == "__main__":
    unittest.main()
