"""Preview-oriented crown building service."""

from __future__ import annotations

from dataclasses import dataclass

from .crown_inference import infer_crown_radii
from .geometry_math import circle_points, radii_to_points
from .numeric import circular_gaussian_smooth, circular_moving_average
from .raster_analysis import find_local_apex, inner_support_threshold, sample_profile


@dataclass(frozen=True)
class CrownBuildResult:
    points: list
    refined: bool
    apex_point: tuple | None
    apex_height_m: float | None
    threshold: float | None
    warnings: tuple


def build_crown_preview_points(center, seed_radius, params, sample_value):
    """Build crown polygon ring points without QGIS geometry or layer writes."""
    warnings = []
    cell_size = max(params.min_grid_size_m, min(params.max_grid_size_m, params.profile_step_m))

    apex_point, apex_value = find_local_apex(
        center,
        params.local_apex_search_radius_m,
        cell_size,
        sample_value,
    )
    if apex_point is None or apex_value is None:
        return CrownBuildResult(
            points=circle_points(center, seed_radius, params.num_angles),
            refined=False,
            apex_point=None,
            apex_height_m=None,
            threshold=None,
            warnings=("No local apex found; using circle fallback.",),
        )

    threshold = inner_support_threshold(
        apex_point,
        apex_value,
        seed_radius,
        cell_size,
        sample_value,
        min_canopy_height_m=params.min_canopy_height_m,
        center_height_fraction=params.center_height_fraction,
        inner_support_fraction=params.inner_support_fraction,
        inner_support_radius_factor=params.inner_support_radius_factor,
        inner_support_radius_min_m=params.inner_support_radius_min_m,
    )

    profile_sampler = lambda point, angle, max_search, step: sample_profile(
        point,
        angle,
        max_search,
        step,
        sample_value,
    )
    radii = infer_crown_radii(
        apex_point=apex_point,
        apex_value=apex_value,
        seed_radius=seed_radius,
        threshold=threshold,
        competing_apexes=[(apex_point, apex_value)],
        params=params,
        sample_profile=profile_sampler,
    )

    for _ in range(int(params.smooth_radius_passes)):
        radii = circular_moving_average(radii, params.smooth_radius_window)

    radii = circular_gaussian_smooth(
        radii,
        radius=params.gaussian_smooth_radius,
        sigma=params.gaussian_smooth_sigma,
        passes=params.gaussian_smooth_passes,
    )

    points = radii_to_points(apex_point, radii)
    if not points:
        warnings.append("Could not build crown radii polygon; using circle fallback.")
        points = circle_points(center, seed_radius, params.num_angles)
        return CrownBuildResult(
            points=points,
            refined=False,
            apex_point=apex_point,
            apex_height_m=apex_value,
            threshold=threshold,
            warnings=tuple(warnings),
        )

    return CrownBuildResult(
        points=points,
        refined=True,
        apex_point=apex_point,
        apex_height_m=apex_value,
        threshold=threshold,
        warnings=tuple(warnings),
    )
