import unittest

from forest_labeler_core.canopy_presets import build_canopy_parameters
from forest_labeler_core.crown_builder import build_crown_preview_points


class CrownBuilderTest(unittest.TestCase):
    def test_falls_back_to_circle_when_no_apex_found(self):
        params = build_canopy_parameters("MIXED", 11)
        result = build_crown_preview_points(
            center=(0, 0),
            seed_radius=2,
            params=params,
            sample_value=lambda point: None,
        )

        self.assertFalse(result.refined)
        self.assertIsNone(result.apex_point)
        self.assertIn("circle fallback", result.warnings[0])
        self.assertEqual(len(result.points), params.num_angles + 1)

    def test_builds_refined_points_when_apex_and_profiles_exist(self):
        params = build_canopy_parameters("MIXED", 11)

        def sampler(point):
            x_val, y_val = point
            distance = (x_val * x_val + y_val * y_val) ** 0.5
            return max(0.5, 10.0 - 2.0 * distance)

        result = build_crown_preview_points(
            center=(0, 0),
            seed_radius=2,
            params=params,
            sample_value=sampler,
        )

        self.assertTrue(result.refined)
        self.assertIsNotNone(result.apex_point)
        self.assertIsNotNone(result.apex_height_m)
        self.assertIsNotNone(result.threshold)
        self.assertEqual(len(result.points), params.num_angles + 1)
        self.assertEqual(result.points[0], result.points[-1])

    def test_competing_peak_constrains_crown_growth(self):
        params = build_canopy_parameters("DENSE", 11)

        def sampler(point):
            x_val, y_val = point
            target = max(0.0, 10.0 - 1.0 * (x_val * x_val + y_val * y_val) ** 0.5)
            competitor = max(0.0, 8.0 - 1.0 * ((x_val - 4.0) ** 2 + y_val * y_val) ** 0.5)
            return max(target, competitor)

        result = build_crown_preview_points(
            center=(0, 0),
            seed_radius=3,
            params=params,
            sample_value=sampler,
        )

        east_x = max(point[0] for point in result.points)
        self.assertLess(east_x, 6.0)


if __name__ == "__main__":
    unittest.main()
