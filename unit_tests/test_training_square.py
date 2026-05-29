import unittest

from forest_labeler_core.training_square import (
    build_training_shape_parameters,
    side_lengths,
    training_shape_ring_points,
)


class TrainingShapeTest(unittest.TestCase):
    def test_four_vertices_create_square_with_requested_side_length(self):
        params = build_training_shape_parameters(segment_length_m=100, vertex_count=4)
        points = training_shape_ring_points((0, 0), params)

        self.assertEqual(params.shape_name, "square")
        self.assertEqual(len(points), 5)
        for length in side_lengths(points):
            self.assertAlmostEqual(length, 100.0)

    def test_three_vertices_create_triangle(self):
        params = build_training_shape_parameters(segment_length_m=25, vertex_count=3)
        points = training_shape_ring_points((0, 0), params)

        self.assertEqual(params.shape_name, "triangle")
        self.assertEqual(len(points), 4)
        self.assertEqual(len(points[:-1]), 3)

    def test_six_vertices_create_hexagon(self):
        params = build_training_shape_parameters(segment_length_m=10, vertex_count=6)
        points = training_shape_ring_points((0, 0), params)

        self.assertEqual(params.shape_name, "hexagon")
        self.assertEqual(len(points), 7)
        for length in side_lengths(points):
            self.assertAlmostEqual(length, 10.0)

    def test_rejects_invalid_parameters(self):
        with self.assertRaises(ValueError):
            build_training_shape_parameters(segment_length_m=0, vertex_count=4)
        with self.assertRaises(ValueError):
            build_training_shape_parameters(segment_length_m=10, vertex_count=2)


if __name__ == "__main__":
    unittest.main()
