import unittest

from forest_labeler_core.training_square import (
    build_training_shape_parameters,
    list_training_polygon_presets,
    parse_side_lengths_text,
    side_lengths,
    side_lengths_label,
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

    def test_custom_rectangle_side_lengths_are_honored(self):
        params = build_training_shape_parameters(
            segment_length_m=100,
            vertex_count=4,
            side_lengths=(100, 20, 100, 20),
        )
        lengths = side_lengths(training_shape_ring_points((0, 0), params))

        self.assertTrue(params.uses_custom_lengths)
        for actual, expected in zip(lengths, (100, 20, 100, 20)):
            self.assertAlmostEqual(actual, expected, places=5)

    def test_custom_triangle_side_lengths_are_honored(self):
        params = build_training_shape_parameters(
            segment_length_m=10,
            vertex_count=3,
            side_lengths=(10, 20, 25),
        )
        lengths = side_lengths(training_shape_ring_points((0, 0), params))

        for actual, expected in zip(lengths, (10, 20, 25)):
            self.assertAlmostEqual(actual, expected, places=5)

    def test_parses_custom_side_length_text(self):
        self.assertEqual(parse_side_lengths_text("100, 20; 100|20"), (100.0, 20.0, 100.0, 20.0))
        params = build_training_shape_parameters(100, 4, side_lengths=parse_side_lengths_text("100 20 100 20"))
        self.assertEqual(side_lengths_label(params), "100, 20, 100, 20")

    def test_training_polygon_presets_cover_common_field_shapes(self):
        presets = {preset.key: preset for preset in list_training_polygon_presets()}

        self.assertEqual(presets["square_100"].vertex_count, 4)
        self.assertEqual(presets["square_100"].segment_length_m, 100.0)
        self.assertEqual(presets["rectangle_100x20"].side_lengths_m, (100.0, 20.0, 100.0, 20.0))
        self.assertEqual(presets["triangle_25"].vertex_count, 3)
        self.assertEqual(presets["hexagon_25"].vertex_count, 6)

    def test_rejects_invalid_parameters(self):
        with self.assertRaises(ValueError):
            build_training_shape_parameters(segment_length_m=0, vertex_count=4)
        with self.assertRaises(ValueError):
            build_training_shape_parameters(segment_length_m=10, vertex_count=2)
        with self.assertRaises(ValueError):
            build_training_shape_parameters(segment_length_m=10, vertex_count=4, side_lengths=(10, 20))
        with self.assertRaises(ValueError):
            build_training_shape_parameters(segment_length_m=10, vertex_count=3, side_lengths=(100, 1, 1))


if __name__ == "__main__":
    unittest.main()
