import unittest

from forest_labeler_core.training_shape_attributes import (
    TRAINING_POLYGON_FIELD_SPECS,
    TRAINING_POLYGON_RECOMMENDED_FIELDS,
    TrainingShapeAttributeInputs,
    build_training_shape_attribute_plan,
)


class TrainingShapeAttributeTest(unittest.TestCase):
    def test_recommended_fields_follow_schema_specs(self):
        self.assertEqual(
            TRAINING_POLYGON_RECOMMENDED_FIELDS,
            tuple(field_spec.name for field_spec in TRAINING_POLYGON_FIELD_SPECS),
        )
        field_types = {
            field_spec.name: field_spec.value_type for field_spec in TRAINING_POLYGON_FIELD_SPECS
        }
        self.assertNotIn("fid", field_types)
        self.assertEqual(field_types["area_m2"], "double")
        self.assertEqual(field_types["review_status"], "string")

    def test_builds_attribute_plan_for_available_fields(self):
        plan = build_training_shape_attribute_plan(
            TrainingShapeAttributeInputs(
                next_fid=12,
                segment_length_m=25.678,
                side_lengths_label="25.678, 25.678, 25.678, 25.678, 25.678, 25.678",
                vertex_count=6,
                shape_name="hexagon",
                angle_deg=33.333,
                geometry_area_m2=1624.567,
                ortho_id="X:/imagery/ortho.tif",
                plot_area="North",
                landcover_summary={
                    "Detailed_L_count": 2,
                    "Detailed_L_majority": "Dry Forest",
                    "Detailed_L_majority_pct": 72.5,
                    "Detailed_L_other_pct": 0.0,
                },
            ),
            available_fields={
                "segment_m",
                "side_m",
                "side_lengths",
                "nodes",
                "vertices",
                "shape",
                "angle",
                "area_m2",
                "ortho_id",
                "plot_area",
                "Detailed_L_count",
                "Detailed_L_majority",
                "Detailed_L_majority_pct",
                "Detailed_L_other_pct",
                "reviewed",
                "review_status",
            },
        )

        self.assertNotIn("fid", plan.values)
        self.assertEqual(plan.values["segment_m"], 25.68)
        self.assertEqual(plan.values["side_m"], 25.68)
        self.assertEqual(plan.values["side_lengths"], "25.678, 25.678, 25.678, 25.678, 25.678, 25.678")
        self.assertEqual(plan.values["nodes"], 6)
        self.assertEqual(plan.values["vertices"], 6)
        self.assertEqual(plan.values["shape"], "hexagon")
        self.assertEqual(plan.values["angle"], 33.33)
        self.assertEqual(plan.values["area_m2"], 1624.57)
        self.assertEqual(plan.values["ortho_id"], "X:/imagery/ortho.tif")
        self.assertEqual(plan.values["plot_area"], "North")
        self.assertEqual(plan.values["Detailed_L_count"], 2)
        self.assertEqual(plan.values["Detailed_L_majority"], "Dry Forest")
        self.assertEqual(plan.values["Detailed_L_majority_pct"], 72.5)
        self.assertEqual(plan.values["Detailed_L_other_pct"], 0.0)
        self.assertEqual(plan.values["reviewed"], 0)
        self.assertEqual(plan.values["review_status"], "unreviewed")

    def test_records_skipped_optional_fields(self):
        plan = build_training_shape_attribute_plan(
            TrainingShapeAttributeInputs(
                next_fid=None,
                segment_length_m=100,
                side_lengths_label="100, 100, 100, 100",
                vertex_count=4,
                shape_name="square",
                angle_deg=0,
                geometry_area_m2=10000,
            ),
            available_fields={"shape"},
        )

        self.assertEqual(plan.values, {"shape": "square"})
        self.assertIn("segment_m", plan.skipped_fields)
        self.assertNotIn("fid", plan.skipped_fields)


if __name__ == "__main__":
    unittest.main()
