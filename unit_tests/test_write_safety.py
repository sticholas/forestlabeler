import unittest

from forest_labeler_core.write_safety import (
    WritePreflightInputs,
    validate_feature_write_preflight,
)


class WriteSafetyTest(unittest.TestCase):
    def test_blocks_missing_layer_and_empty_geometry(self):
        result = validate_feature_write_preflight(
            WritePreflightInputs(
                layer_label="target canopy polygon layer",
                layer_name=None,
                layer_selected=False,
                require_editable=True,
                is_editable=False,
                geometry_present=False,
                geometry_empty=True,
            )
        )

        self.assertFalse(result.ok)
        self.assertIn("Select a target canopy polygon layer.", result.errors)
        self.assertIn("Generated geometry is empty and cannot be written.", result.errors)

    def test_blocks_non_editable_layer_when_required(self):
        result = validate_feature_write_preflight(
            WritePreflightInputs(
                layer_label="target canopy polygon layer",
                layer_name="canopies",
                layer_selected=True,
                require_editable=True,
                is_editable=False,
                geometry_present=True,
                geometry_empty=False,
                geometry_valid=True,
            )
        )

        self.assertEqual(
            result.errors,
            ("'canopies' must be in edit mode before adding features.",),
        )

    def test_blocks_invalid_geometry(self):
        result = validate_feature_write_preflight(
            WritePreflightInputs(
                layer_label="target canopy polygon layer",
                layer_name="canopies",
                layer_selected=True,
                require_editable=True,
                is_editable=True,
                geometry_present=True,
                geometry_empty=False,
                geometry_valid=False,
            )
        )

        self.assertEqual(result.errors, ("Generated geometry is invalid and cannot be written safely.",))

    def test_warns_when_geometry_validity_is_unknown(self):
        result = validate_feature_write_preflight(
            WritePreflightInputs(
                layer_label="target canopy polygon layer",
                layer_name="canopies",
                layer_selected=True,
                require_editable=True,
                is_editable=True,
                geometry_present=True,
                geometry_empty=False,
                geometry_valid=None,
            )
        )

        self.assertTrue(result.ok)
        self.assertEqual(result.warnings, ("Geometry validity could not be confirmed before writing.",))


if __name__ == "__main__":
    unittest.main()
