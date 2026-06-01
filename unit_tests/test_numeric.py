import unittest

from forest_labeler_core.numeric import (
    circular_gaussian_smooth,
    circular_moving_average,
    gaussian_kernel,
    median,
)


class NumericHelperTest(unittest.TestCase):
    def test_median_handles_empty_odd_and_even_values(self):
        self.assertIsNone(median([]))
        self.assertEqual(median([3, 1, 2]), 2)
        self.assertEqual(median([10, 2, 4, 8]), 6)

    def test_gaussian_kernel_is_normalized_and_symmetric(self):
        kernel = gaussian_kernel(radius=2, sigma=1.1)

        self.assertEqual(len(kernel), 5)
        self.assertAlmostEqual(sum(kernel), 1.0)
        self.assertAlmostEqual(kernel[0], kernel[-1])
        self.assertAlmostEqual(kernel[1], kernel[-2])
        self.assertGreater(kernel[2], kernel[1])

    def test_gaussian_kernel_rejects_bad_parameters(self):
        with self.assertRaises(ValueError):
            gaussian_kernel(radius=-1, sigma=1.0)
        with self.assertRaises(ValueError):
            gaussian_kernel(radius=2, sigma=0)

    def test_circular_gaussian_smooth_wraps_edges(self):
        values = [10.0, 0.0, 0.0, 0.0]
        smoothed = circular_gaussian_smooth(values, radius=1, sigma=1.0, passes=1)

        self.assertGreater(smoothed[0], smoothed[1])
        self.assertGreater(smoothed[-1], 0.0)
        self.assertAlmostEqual(sum(smoothed), sum(values))

    def test_circular_gaussian_smooth_honors_zero_passes(self):
        values = [1.0, 2.0, 3.0]

        self.assertEqual(circular_gaussian_smooth(values, passes=0), values)

    def test_circular_moving_average_wraps_edges(self):
        values = [9.0, 0.0, 0.0]

        self.assertEqual(circular_moving_average([], window=1), [])
        self.assertEqual(circular_moving_average(values, window=0), values)
        self.assertEqual(circular_moving_average(values, window=1), [3.0, 3.0, 3.0])


if __name__ == "__main__":
    unittest.main()
