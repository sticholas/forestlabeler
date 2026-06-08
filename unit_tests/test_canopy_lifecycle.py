import unittest

from forest_labeler_core.canopy_lifecycle import (
    canopy_attribute_change_invalidates_review,
    canopy_geometry_change_invalidates_review,
)


class CanopyLifecycleTest(unittest.TestCase):
    def test_geometry_edit_invalidates_reviewed_crown(self):
        self.assertTrue(canopy_geometry_change_invalidates_review("accepted"))
        self.assertTrue(canopy_geometry_change_invalidates_review("rejected"))
        self.assertFalse(canopy_geometry_change_invalidates_review("unreviewed"))

    def test_material_parameter_edit_invalidates_review(self):
        self.assertTrue(canopy_attribute_change_invalidates_review("tightness", "accepted"))
        self.assertTrue(canopy_attribute_change_invalidates_review("mode", "accepted"))
        self.assertTrue(canopy_attribute_change_invalidates_review("chm_id", "accepted"))

    def test_non_material_metadata_edit_keeps_review(self):
        self.assertFalse(canopy_attribute_change_invalidates_review("species", "accepted"))
        self.assertFalse(canopy_attribute_change_invalidates_review("review_note", "accepted"))
        self.assertFalse(canopy_attribute_change_invalidates_review("tightness", "unreviewed"))


if __name__ == "__main__":
    unittest.main()
