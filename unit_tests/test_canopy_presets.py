import unittest

from forest_labeler_core.canopy_presets import (
    MAX_CROWN_TIGHTNESS,
    MIN_CROWN_TIGHTNESS,
    build_canopy_parameters,
)


class CanopyPresetTest(unittest.TestCase):
    def test_builds_base_mixed_parameters(self):
        params = build_canopy_parameters("MIXED", 11)

        self.assertEqual(params.mode, "MIXED")
        self.assertEqual(params.crown_tightness, 11)
        self.assertEqual(params.num_angles, 48)
        self.assertAlmostEqual(params.profile_max_factor, 1.90)
        self.assertAlmostEqual(params.competing_apex_min_relative_height, 0.35)

    def test_mode_is_case_insensitive(self):
        params = build_canopy_parameters("dense", 11)

        self.assertEqual(params.mode, "DENSE")
        self.assertAlmostEqual(params.min_canopy_height_m, 1.5)

    def test_rejects_unknown_mode(self):
        with self.assertRaises(ValueError):
            build_canopy_parameters("JUNGLE", 11)

    def test_clamps_tightness_range(self):
        loose = build_canopy_parameters("SPARSE", -100)
        tight = build_canopy_parameters("SPARSE", 100)

        self.assertEqual(loose.crown_tightness, MIN_CROWN_TIGHTNESS)
        self.assertEqual(tight.crown_tightness, MAX_CROWN_TIGHTNESS)

    def test_tighter_crown_uses_more_sampling_and_competition_pressure(self):
        normal = build_canopy_parameters("MIXED", 11)
        tight = build_canopy_parameters("MIXED", 21)

        self.assertGreaterEqual(tight.num_angles, 84)
        self.assertLess(tight.profile_step_m, normal.profile_step_m)
        self.assertGreater(tight.profile_competitor_penalty, normal.profile_competitor_penalty)
        self.assertLess(tight.ownership_margin, normal.ownership_margin)

    def test_loose_crown_keeps_broader_smoother_shape(self):
        normal = build_canopy_parameters("DENSE", 11)
        loose = build_canopy_parameters("DENSE", 1)

        self.assertLessEqual(loose.num_angles, 40)
        self.assertGreater(loose.profile_max_factor, normal.profile_max_factor)
        self.assertGreaterEqual(loose.final_buffer_smooth_m, 0.45)
        self.assertGreaterEqual(loose.smooth_radius_passes, 3)


if __name__ == "__main__":
    unittest.main()
