"""Training shape geometry helpers."""

from __future__ import annotations

from dataclasses import dataclass
import math

from .geometry_math import distance_xy, xy


@dataclass(frozen=True)
class TrainingShapeParameters:
    segment_length_m: float = 100.0
    vertex_count: int = 4
    angle_deg: float = 0.0

    @property
    def shape_name(self):
        names = {
            3: "triangle",
            4: "square",
            5: "pentagon",
            6: "hexagon",
            7: "heptagon",
            8: "octagon",
        }
        return names.get(self.vertex_count, f"{self.vertex_count}-gon")

    @property
    def circumradius_m(self):
        return self.segment_length_m / (2.0 * math.sin(math.pi / self.vertex_count))


def build_training_shape_parameters(segment_length_m, vertex_count, angle_deg=0.0):
    """Validate and normalize training shape parameters."""
    segment_length = float(segment_length_m)
    vertices = int(vertex_count)
    if segment_length <= 0:
        raise ValueError("segment length must be greater than zero")
    if vertices < 3:
        raise ValueError("vertex count must be at least 3")
    return TrainingShapeParameters(
        segment_length_m=segment_length,
        vertex_count=vertices,
        angle_deg=float(angle_deg) % 360.0,
    )


def training_shape_ring_points(center, params):
    """Return closed regular-polygon ring points for a training shape."""
    center_x, center_y = xy(center)
    start_angle = math.radians(params.angle_deg) - math.pi / 2.0
    radius = params.circumradius_m
    points = []
    for index in range(params.vertex_count):
        angle = start_angle + (2.0 * math.pi * index) / params.vertex_count
        points.append((center_x + radius * math.cos(angle), center_y + radius * math.sin(angle)))
    points.append(points[0])
    return points


def side_lengths(points):
    """Return side lengths for a closed polygon ring."""
    return [distance_xy(points[index], points[index + 1]) for index in range(len(points) - 1)]


# Backwards-compatible names from the first Track B migration slice.
TrainingSquareParameters = TrainingShapeParameters
build_training_square_parameters = build_training_shape_parameters
square_ring_points = training_shape_ring_points
