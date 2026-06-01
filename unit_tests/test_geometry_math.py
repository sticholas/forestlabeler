import unittest

from forest_labeler_core.geometry_math import (
    circle_points,
    distance_xy,
    first_derivative,
    radii_to_points,
    second_derivative,
    simple_line_smooth,
)


class GeometryMathTest(unittest.TestCase):
    def test_distance_accepts_tuple_like_points(self):
        self.assertEqual(distance_xy((0, 0), (3, 4)), 5)

    def test_circle_points_returns_closed_ring(self):
        points = circle_points((0, 0), radius=2, segments=8)

        self.assertEqual(len(points), 9)
        self.assertEqual(points[0], points[-1])
        self.assertAlmostEqual(points[0][0], 2.0)
        self.assertAlmostEqual(points[0][1], 0.0)

    def test_circle_points_rejects_bad_inputs(self):
        with self.assertRaises(ValueError):
            circle_points((0, 0), radius=-1, segments=8)
        with self.assertRaises(ValueError):
            circle_points((0, 0), radius=1, segments=4)

    def test_radii_to_points_returns_empty_for_too_few_radii(self):
        self.assertEqual(radii_to_points((0, 0), [1, 2, 3]), [])

    def test_radii_to_points_returns_closed_ring(self):
        points = radii_to_points((0, 0), [1] * 8)

        self.assertEqual(len(points), 9)
        self.assertEqual(points[0], points[-1])

    def test_derivatives_match_quadratic_profile(self):
        values = [0, 1, 4, 9, 16]

        self.assertEqual(first_derivative(values, step=1), [1, 2, 4, 6, 7])
        self.assertEqual(second_derivative(values, step=1), [0.0, 2.0, 2.0, 2.0, 0.0])

    def test_simple_line_smooth_preserves_edges(self):
        self.assertEqual(simple_line_smooth([1, 10]), [1, 10])
        self.assertEqual(simple_line_smooth([1, 10, 1]), [1, 4.0, 1])


if __name__ == "__main__":
    unittest.main()
