"""Raster analysis helpers that run without QGIS imports."""

from __future__ import annotations

import math

from .geometry_math import distance_xy, xy
from .numeric import median


def sample_profile(center, angle, max_search, step, sample_value):
    """Sample values from a center along one radial profile."""
    center_x, center_y = xy(center)
    distances = []
    values = []
    radius = step

    while radius <= max_search + 1e-9:
        point = (
            center_x + radius * math.cos(angle),
            center_y + radius * math.sin(angle),
        )
        value = sample_value(point)
        if value is None:
            break
        distances.append(radius)
        values.append(value)
        radius += step

    return distances, values


def sample_circle_values(center, radius, step, sample_value):
    """Sample all raster values on a grid inside a circular area."""
    center_x, center_y = xy(center)
    values = []

    x_pos = center_x - radius
    while x_pos <= center_x + radius + 1e-9:
        y_pos = center_y - radius
        while y_pos <= center_y + radius + 1e-9:
            point = (x_pos, y_pos)
            if distance_xy(point, (center_x, center_y)) <= radius:
                value = sample_value(point)
                if value is not None:
                    values.append(value)
            y_pos += step
        x_pos += step

    return values


def find_local_apex(center, search_radius, step, sample_value):
    """Find the highest sampled value around a center point."""
    center_x, center_y = xy(center)
    best_point = None
    best_value = None

    x_pos = center_x - search_radius
    while x_pos <= center_x + search_radius + 1e-9:
        y_pos = center_y - search_radius
        while y_pos <= center_y + search_radius + 1e-9:
            point = (x_pos, y_pos)
            if distance_xy(point, (center_x, center_y)) <= search_radius:
                value = sample_value(point)
                if value is not None and (best_value is None or value > best_value):
                    best_value = value
                    best_point = point
            y_pos += step
        x_pos += step

    return best_point, best_value


def find_competing_apexes(
    apex_point,
    apex_value,
    search_radius,
    step,
    threshold,
    sample_value,
    *,
    min_relative_height,
    min_separation_m,
):
    """Find nearby apex candidates that can constrain a crown boundary."""
    apex_x, apex_y = xy(apex_point)
    min_candidate_value = max(threshold, apex_value * min_relative_height)
    candidates = []

    x_pos = apex_x - search_radius
    while x_pos <= apex_x + search_radius + 1e-9:
        y_pos = apex_y - search_radius
        while y_pos <= apex_y + search_radius + 1e-9:
            point = (x_pos, y_pos)
            if distance_xy(point, apex_point) <= search_radius:
                value = sample_value(point)
                if value is not None and value >= min_candidate_value:
                    candidates.append((point, value))
            y_pos += step
        x_pos += step

    candidates.sort(key=lambda item: item[1], reverse=True)

    apexes = []
    for point, value in candidates:
        if all(distance_xy(point, kept_point) >= min_separation_m for kept_point, _ in apexes):
            apexes.append((point, value))

    if all(distance_xy(apex_point, point) >= 1e-6 for point, _ in apexes):
        apexes.insert(0, (apex_point, apex_value))

    return apexes


def inner_support_threshold(
    apex_point,
    apex_value,
    seed_radius,
    step,
    sample_value,
    *,
    min_canopy_height_m,
    center_height_fraction,
    inner_support_fraction,
    inner_support_radius_factor,
    inner_support_radius_min_m,
):
    """Compute the inner support threshold used by crown inference."""
    radius = max(inner_support_radius_min_m, seed_radius * inner_support_radius_factor)
    values = sample_circle_values(apex_point, radius, step, sample_value)
    median_value = median(values)

    candidates = [min_canopy_height_m, apex_value * center_height_fraction]
    if median_value is not None:
        candidates.append(median_value * inner_support_fraction)
    return max(candidates)
