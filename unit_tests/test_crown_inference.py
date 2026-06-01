import unittest

from forest_labeler_core.canopy_presets import build_canopy_parameters
from forest_labeler_core.crown_inference import (
    competitor_penalty,
    infer_crown_radii,
    infer_radius_from_profile,
    ownership_score,
)


class CrownInferenceTest(unittest.TestCase):
    def setUp(self):
        self.params = build_canopy_parameters("MIXED", 11)

    def test_ownership_score_favors_closer_stronger_apex(self):
        near_score = ownership_score((1, 0), 8, (0, 0), 10, self.params)
        far_score = ownership_score((8, 0), 8, (0, 0), 10, self.params)

        self.assertGreater(near_score, far_score)

    def test_competitor_penalty_is_zero_without_competitor(self):
        penalty = competitor_penalty((1, 0), 8, (0, 0), 10, [((0, 0), 10)], self.params)

        self.assertEqual(penalty, 0.0)

    def test_competitor_penalty_increases_near_other_apex(self):
        penalty = competitor_penalty(
            (4.8, 0),
            8,
            (0, 0),
            10,
            [((0, 0), 10), ((5, 0), 9)],
            self.params,
        )

        self.assertGreater(penalty, 0.0)

    def test_short_profile_returns_seed_radius(self):
        radius = infer_radius_from_profile(
            [1, 2, 3],
            [10, 9, 8],
            angle=0,
            apex_point=(0, 0),
            apex_value=10,
            seed_radius=2.5,
            threshold=2,
            competing_apexes=[((0, 0), 10)],
            params=self.params,
        )

        self.assertEqual(radius, 2.5)

    def test_profile_infers_radius_near_crown_edge(self):
        distances = [0.35, 0.7, 1.05, 1.4, 1.75, 2.1, 2.45, 2.8, 3.15]
        values = [10, 9.5, 8.5, 6.0, 3.0, 1.4, 1.0, 0.8, 0.7]

        radius = infer_radius_from_profile(
            distances,
            values,
            angle=0,
            apex_point=(0, 0),
            apex_value=10,
            seed_radius=1.5,
            threshold=1.5,
            competing_apexes=[((0, 0), 10)],
            params=self.params,
        )

        self.assertGreaterEqual(radius, 1.05)
        self.assertLessEqual(radius, 2.45)

    def test_infer_crown_radii_uses_configured_angle_count(self):
        def fake_sample_profile(apex_point, angle, max_search, step):
            return [1, 2, 3, 4, 5, 6], [10, 9, 7, 4, 2, 1]

        radii = infer_crown_radii(
            apex_point=(0, 0),
            apex_value=10,
            seed_radius=2,
            threshold=1.5,
            competing_apexes=[((0, 0), 10)],
            params=self.params,
            sample_profile=fake_sample_profile,
        )

        self.assertEqual(len(radii), self.params.num_angles)


if __name__ == "__main__":
    unittest.main()
