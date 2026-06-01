"""Geometry-oriented math helpers for canopy workflows."""

from __future__ import annotations

import math


def xy(point):
    """Return x/y coordinates from a tuple-like object or QGIS-like point."""
    if isinstance(point, (tuple, list)) and len(point) >= 2:
        return float(point[0]), float(point[1])
    return float(point.x()), float(point.y())


def distance_xy(point_a, point_b):
    """Return planar distance between two point-like objects."""
    ax, ay = xy(point_a)
    bx, by = xy(point_b)
    dx = bx - ax
    dy = by - ay
    return math.sqrt(dx * dx + dy * dy)


def circle_points(center, radius, segments=72):
    """Return closed polygon ring points for a circle."""
    if radius < 0:
        raise ValueError("radius must be greater than or equal to 0")
    if int(segments) < 8:
        raise ValueError("segments must be at least 8")

    center_x, center_y = xy(center)
    segments = int(segments)
    points = []
    for index in range(segments):
        angle = (2.0 * math.pi * index) / segments
        points.append(
            (
                center_x + radius * math.cos(angle),
                center_y + radius * math.sin(angle),
            )
        )
    points.append(points[0])
    return points


def radii_to_points(center, radii):
    """Return closed polygon ring points from radial distances."""
    if len(radii) < 8:
        return []

    center_x, center_y = xy(center)
    count = len(radii)
    points = []
    for index, radius in enumerate(radii):
        angle = (2.0 * math.pi * index) / count
        points.append(
            (
                center_x + radius * math.cos(angle),
                center_y + radius * math.sin(angle),
            )
        )
    points.append(points[0])
    return points


def first_derivative(values, step):
    """Compute first derivative with centered differences."""
    count = len(values)
    out = [0.0] * count
    if count < 2:
        return out

    out[0] = (values[1] - values[0]) / step
    out[-1] = (values[-1] - values[-2]) / step
    for index in range(1, count - 1):
        out[index] = (values[index + 1] - values[index - 1]) / (2.0 * step)
    return out


def second_derivative(values, step):
    """Compute second derivative with centered differences."""
    count = len(values)
    out = [0.0] * count
    if count < 3:
        return out

    for index in range(1, count - 1):
        out[index] = (
            values[index + 1] - 2.0 * values[index] + values[index - 1]
        ) / (step * step)
    return out


def simple_line_smooth(values):
    """Apply one pass of three-point line smoothing."""
    if len(values) < 3:
        return list(values)

    out = [values[0]]
    for index in range(1, len(values) - 1):
        out.append((values[index - 1] + values[index] + values[index + 1]) / 3.0)
    out.append(values[-1])
    return out
