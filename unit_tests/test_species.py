import unittest

from forest_labeler_core.species import decide_species_assignment


class SpeciesDecisionTest(unittest.TestCase):
    def test_missing_species_can_warn_without_blocking(self):
        decision = decide_species_assignment([], warn_if_missing=True)

        self.assertIsNone(decision.species)
        self.assertEqual(decision.point_count, 0)
        self.assertIsNotNone(decision.warning)
        self.assertFalse(decision.should_block)

    def test_single_species_is_assigned(self):
        decision = decide_species_assignment([" MAM "])

        self.assertEqual(decision.species, "MAM")
        self.assertEqual(decision.point_count, 1)
        self.assertIsNone(decision.warning)
        self.assertFalse(decision.should_block)

    def test_multiple_species_blocks_when_configured(self):
        decision = decide_species_assignment(["MAM", "KOU", "MAM"], block_multiple=True)

        self.assertIsNone(decision.species)
        self.assertEqual(decision.point_count, 3)
        self.assertIn("KOU", decision.warning)
        self.assertTrue(decision.should_block)

    def test_multiple_species_can_warn_without_blocking(self):
        decision = decide_species_assignment(["MAM", "KOU"], block_multiple=False)

        self.assertIsNone(decision.species)
        self.assertIsNotNone(decision.warning)
        self.assertFalse(decision.should_block)


if __name__ == "__main__":
    unittest.main()
