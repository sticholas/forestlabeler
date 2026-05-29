"""Training square geometry helpers."""

from __future__ import annotations

from dataclasses import dataclass
import math

from .geometry_math import xy


@dataclass(frozen=True)
class TrainingSquareParameters:
    segment_length_m: float = 10.0
    nodes_per_side: int = 11
    angle_deg: float = 0.0

    @property
    def side_length_m(self):
        return self.segment_length_m * max(1, self.nodes_per_side - 1)


def build_training_square_parameters(segment_length_m, nodes_per_side, angle_deg=0.0):
    """Validate and normalize training square parameters."""
    segment_length = float(segment_length_m)
    node_count = int(nodes_per_side)
    if segment_length <= 0:
        raise ValueError("segment length must be greater than zero")
    if node_count < 2:
        raise ValueError("nodes per side must be at least 2")
    return TrainingSquareParameters(
        segment_length_m=segment_length,
        nodes_per_side=node_count,
        angle_deg=float(angle_deg) % 360.0,
    )


def square_ring_points(center, params):
    """Return closed rotated square ring points for training-square creation."""
    center_x, center_y = xy(center)
    half_size = params.side_length_m / 2.0
    local_corners = [
        (-half_size, -half_size),
        (half_size, -half_size),
        (half_size, half_size),
        (-half_size, half_size),
        (-half_size, -half_size),
    ]
    return [_rotate_offset(center_x, center_y, dx, dy, params.angle_deg) for dx, dy in local_corners]


def square_grid_nodes(center, params):
    """Return rotated grid node points inside the square, row-major."""
    center_x, center_y = xy(center)
    half_size = params.side_length_m / 2.0
    nodes = []
    for row in range(params.nodes_per_side):
        dy = -half_size + row * params.segment_length_m
        for col in range(params.nodes_per_side):
            dx = -half_size + col * params.segment_length_m
            nodes.append(_rotate_offset(center_x, center_y, dx, dy, params.angle_deg))
    return nodes


def _rotate_offset(center_x, center_y, dx, dy, angle_deg):
    angle = math.radians(angle_deg)
    cos_angle = math.cos(angle)
    sin_angle = math.sin(angle)
    return (
        center_x + dx * cos_angle - dy * sin_angle,
        center_y + dx * sin_angle + dy * cos_angle,
    )
