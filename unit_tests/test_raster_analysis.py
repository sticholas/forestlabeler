import math
import unittest

from forest_labeler_core.raster_analysis import (
    find_competing_apexes,
    find_local_apex,
    inner_support_threshold,
    sample_circle_values,
    sample_profile,
)


def plane_sampler(point):
    x_val, y_val = point
    return x_val + y_val


class RasterAnalysisTest(unittest.TestCase):
    def test_sample_profile_stops_when_sampler_returns_none(self):
        def sampler(point):
            return None if math.dist(point, (0, 0)) > 2.0 else point[0]

        distances, values = sample_profile((0, 0), 0.0, max_search=4.0, step=1.0, sample_value=sampler)

        self.assertEqual(distances, [1.0, 2.0])
        self.assertEqual(values, [1.0, 2.0])

    def test_sample_circle_values_samples_inside_radius(self):
        values = sample_circle_values((0, 0), radius=1.0, step=1.0, sample_value=lambda point: 1)

        self.assertEqual(len(values), 5)
        self.assertEqual(sum(values), 5)

    def test_find_local_apex_returns_highest_point(self):
        point, value = find_local_apex((0, 0), search_radius=1.0, step=1.0, sample_value=plane_sampler)

        self.assertIn(point, {(1.0, 0.0), (0.0, 1.0)})
        self.assertEqual(value, 1.0)

    def test_find_local_apex_returns_none_when_all_samples_missing(self):
        point, value = find_local_apex((0, 0), search_radius=1.0, step=1.0, sample_value=lambda point: None)

        self.assertIsNone(point)
        self.assertIsNone(value)

    def test_inner_support_threshold_uses_maximum_candidate(self):
        threshold = inner_support_threshold(
            apex_point=(0, 0),
            apex_value=10,
            seed_radius=2,
            step=1.0,
            sample_value=lambda point: 6,
            min_canopy_height_m=1.5,
            center_height_fraction=0.12,
            inner_support_fraction=0.5,
            inner_support_radius_factor=0.2,
            inner_support_radius_min_m=1.0,
        )

        self.assertEqual(threshold, 3.0)

    def test_find_competing_apexes_filters_by_height_and_separation(self):
        heights = {
            (0.0, 0.0): 10.0,
            (2.0, 0.0): 7.0,
            (2.0, 1.0): 6.8,
            (4.0, 0.0): 2.0,
        }

        apexes = find_competing_apexes(
            apex_point=(0, 0),
            apex_value=10.0,
            search_radius=4.0,
            step=1.0,
            threshold=4.0,
            sample_value=lambda point: heights.get(point),
            min_relative_height=0.5,
            min_separation_m=1.5,
        )

        self.assertEqual(apexes, [((0.0, 0.0), 10.0), ((2.0, 0.0), 7.0)])

    def test_find_competing_apexes_keeps_target_when_target_not_sampled(self):
        apexes = find_competing_apexes(
            apex_point=(0.25, 0.25),
            apex_value=10.0,
            search_radius=2.0,
            step=1.0,
            threshold=4.0,
            sample_value=lambda point: 6.0 if point == (1.25, 0.25) else None,
            min_relative_height=0.5,
            min_separation_m=1.5,
        )

        self.assertEqual(apexes[0], ((0.25, 0.25), 10.0))


if __name__ == "__main__":
    unittest.main()
