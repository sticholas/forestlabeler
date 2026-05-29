import unittest

from forest_labeler_core.training_square import (
    build_training_square_parameters,
    square_grid_nodes,
    square_ring_points,
)


class TrainingSquareTest(unittest.TestCase):
    def test_default_grid_matches_100_meter_square(self):
        params = build_training_square_parameters(segment_length_m=10, nodes_per_side=11)

        self.assertEqual(params.side_length_m, 100.0)
        self.assertEqual(len(square_ring_points((0, 0), params)), 5)
        self.assertEqual(len(square_grid_nodes((0, 0), params)), 121)

    def test_supports_arbitrary_segment_length_and_node_count(self):
        params = build_training_square_parameters(segment_length_m=25, nodes_per_side=5)

        self.assertEqual(params.side_length_m, 100.0)
        self.assertEqual(square_ring_points((0, 0), params)[0], (-50.0, -50.0))

    def test_rotates_square_points(self):
        params = build_training_square_parameters(segment_length_m=10, nodes_per_side=2, angle_deg=90)
        points = square_ring_points((0, 0), params)

        self.assertAlmostEqual(points[0][0], 5.0)
        self.assertAlmostEqual(points[0][1], -5.0)

    def test_rejects_invalid_parameters(self):
        with self.assertRaises(ValueError):
            build_training_square_parameters(segment_length_m=0, nodes_per_side=11)
        with self.assertRaises(ValueError):
            build_training_square_parameters(segment_length_m=10, nodes_per_side=1)


if __name__ == "__main__":
    unittest.main()
