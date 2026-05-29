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
    side_lengths_m: tuple = ()

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
        return _circumradius_for_side_lengths(self.resolved_side_lengths_m)

    @property
    def resolved_side_lengths_m(self):
        if self.side_lengths_m:
            return self.side_lengths_m
        return tuple(self.segment_length_m for _ in range(self.vertex_count))

    @property
    def uses_custom_lengths(self):
        return bool(self.side_lengths_m)


@dataclass(frozen=True)
class TrainingPolygonPreset:
    key: str
    label: str
    segment_length_m: float
    vertex_count: int
    side_lengths_m: tuple = ()


TRAINING_POLYGON_PRESETS = (
    TrainingPolygonPreset("custom", "Custom", 100.0, 4),
    TrainingPolygonPreset("square_100", "100 m square", 100.0, 4),
    TrainingPolygonPreset("rectangle_100x20", "100 x 20 m rectangle", 100.0, 4, (100.0, 20.0, 100.0, 20.0)),
    TrainingPolygonPreset("triangle_25", "25 m triangle", 25.0, 3),
    TrainingPolygonPreset("hexagon_25", "25 m hexagon", 25.0, 6),
)


def list_training_polygon_presets():
    return TRAINING_POLYGON_PRESETS


def training_polygon_preset_by_key(key):
    for preset in TRAINING_POLYGON_PRESETS:
        if preset.key == key:
            return preset
    return None


def build_training_shape_parameters(segment_length_m, vertex_count, angle_deg=0.0, side_lengths=None):
    """Validate and normalize training polygon parameters."""
    segment_length = float(segment_length_m)
    vertices = int(vertex_count)
    if segment_length <= 0:
        raise ValueError("segment length must be greater than zero")
    if vertices < 3:
        raise ValueError("vertex count must be at least 3")
    normalized_side_lengths = _normalize_side_lengths(side_lengths, vertices)
    return TrainingShapeParameters(
        segment_length_m=segment_length,
        vertex_count=vertices,
        angle_deg=float(angle_deg) % 360.0,
        side_lengths_m=normalized_side_lengths,
    )


def parse_side_lengths_text(text):
    """Parse comma, semicolon, pipe, or whitespace separated side lengths."""
    if text is None or not str(text).strip():
        return ()
    cleaned = str(text).replace(",", " ").replace(";", " ").replace("|", " ")
    lengths = []
    for item in cleaned.split():
        lengths.append(float(item))
    return tuple(lengths)


def training_shape_ring_points(center, params):
    """Return closed ring points for a training polygon."""
    if params.vertex_count == 3 and params.uses_custom_lengths:
        return _triangle_ring_points(center, params)

    center_x, center_y = xy(center)
    start_angle = math.radians(params.angle_deg) - math.pi / 2.0
    radius = params.circumradius_m
    central_angles = [
        2.0 * math.asin(length / (2.0 * radius)) for length in params.resolved_side_lengths_m
    ]
    points = []
    angle = start_angle
    for index in range(params.vertex_count):
        points.append((center_x + radius * math.cos(angle), center_y + radius * math.sin(angle)))
        angle += central_angles[index]
    points.append(points[0])
    return points


def side_lengths(points):
    """Return side lengths for a closed polygon ring."""
    return [distance_xy(points[index], points[index + 1]) for index in range(len(points) - 1)]


def side_lengths_label(params):
    """Return a compact label for side lengths."""
    lengths = params.resolved_side_lengths_m
    return ", ".join(f"{length:g}" for length in lengths)


def _normalize_side_lengths(side_lengths, vertex_count):
    if not side_lengths:
        return ()
    lengths = tuple(float(length) for length in side_lengths)
    if len(lengths) != vertex_count:
        raise ValueError("custom side length count must match vertex count")
    if any(length <= 0 for length in lengths):
        raise ValueError("custom side lengths must be greater than zero")
    longest = max(lengths)
    if longest >= sum(lengths) - longest:
        raise ValueError("custom side lengths cannot form a closed polygon")
    _circumradius_for_side_lengths(lengths)
    return lengths


def _circumradius_for_side_lengths(lengths):
    longest = max(lengths)
    low = longest / 2.0
    high = max(sum(lengths), low * 2.0)

    def angle_sum(radius):
        return sum(2.0 * math.asin(length / (2.0 * radius)) for length in lengths)

    while angle_sum(high) > 2.0 * math.pi:
        high *= 2.0

    for _ in range(80):
        mid = (low + high) / 2.0
        if angle_sum(mid) > 2.0 * math.pi:
            low = mid
        else:
            high = mid
    return high


def _triangle_ring_points(center, params):
    side_a, side_b, side_c = params.resolved_side_lengths_m
    x_coord = (side_a * side_a + side_c * side_c - side_b * side_b) / (2.0 * side_a)
    y_coord = math.sqrt(max(0.0, side_c * side_c - x_coord * x_coord))
    raw_points = [(0.0, 0.0), (side_a, 0.0), (x_coord, y_coord)]
    centroid_x = sum(point[0] for point in raw_points) / 3.0
    centroid_y = sum(point[1] for point in raw_points) / 3.0
    center_x, center_y = xy(center)
    angle = math.radians(params.angle_deg)
    cos_angle = math.cos(angle)
    sin_angle = math.sin(angle)

    points = []
    for point_x, point_y in raw_points:
        dx = point_x - centroid_x
        dy = point_y - centroid_y
        points.append(
            (
                center_x + dx * cos_angle - dy * sin_angle,
                center_y + dx * sin_angle + dy * cos_angle,
            )
        )
    points.append(points[0])
    return points


# Backwards-compatible names from the first Track B migration slice.
TrainingSquareParameters = TrainingShapeParameters
build_training_square_parameters = build_training_shape_parameters
square_ring_points = training_shape_ring_points
