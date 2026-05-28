"""Numeric helpers for canopy profile analysis.

These functions are migrated from `CanopyCrownLabeler.py` without QGIS
dependencies. They are intentionally small and deterministic because they sit
under crown-boundary inference.
"""

from __future__ import annotations

import math


def median(values):
    """Return the median value, or None for an empty sequence."""
    if not values:
        return None

    sorted_values = sorted(values)
    length = len(sorted_values)
    mid = length // 2

    if length % 2 == 1:
        return sorted_values[mid]
    return (sorted_values[mid - 1] + sorted_values[mid]) / 2.0


def gaussian_kernel(radius, sigma):
    """Build a normalized 1D Gaussian kernel."""
    radius = int(radius)
    sigma = float(sigma)

    if radius < 0:
        raise ValueError("radius must be greater than or equal to 0")
    if sigma <= 0:
        raise ValueError("sigma must be greater than 0")

    weights = [
        math.exp(-(offset * offset) / (2.0 * sigma * sigma))
        for offset in range(-radius, radius + 1)
    ]
    total = sum(weights)
    return [weight / total for weight in weights]


def circular_gaussian_smooth(values, radius=3, sigma=1.5, passes=2):
    """Smooth values on a closed circular profile with a Gaussian kernel."""
    if not values:
        return []

    passes = int(passes)
    if passes <= 0:
        return list(values)

    kernel = gaussian_kernel(radius, sigma)
    out = list(values)
    length = len(out)
    offsets = list(range(-int(radius), int(radius) + 1))

    for _ in range(passes):
        smoothed = []
        for index in range(length):
            smoothed.append(
                sum(out[(index + offset) % length] * weight for offset, weight in zip(offsets, kernel))
            )
        out = smoothed

    return out


def circular_moving_average(values, window):
    """Average neighboring values on a closed circular profile."""
    if not values:
        return []

    window = int(round(window))
    if window <= 0:
        return list(values)

    length = len(values)
    out = []
    for index in range(length):
        neighbors = [
            values[(index + offset) % length]
            for offset in range(-window, window + 1)
        ]
        out.append(sum(neighbors) / len(neighbors))
    return out
