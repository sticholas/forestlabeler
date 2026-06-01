"""Crown radius inference for Track A canopy labeling."""

from __future__ import annotations

import math

from .geometry_math import distance_xy, first_derivative, second_derivative, simple_line_smooth, xy


def ownership_score(point, value, apex_point, apex_value, params):
    """Score how strongly a point belongs to an apex."""
    distance = distance_xy(point, apex_point)
    drop = max(0.0, apex_value - value)
    return value - params.ownership_distance_weight * distance - params.ownership_drop_weight * drop


def competitor_penalty(point, value, apex_point, apex_value, competing_apexes, params):
    """Return positive penalty when another apex owns a candidate point better."""
    target_score = ownership_score(point, value, apex_point, apex_value, params)

    best_other = None
    for competitor_point, competitor_value in competing_apexes:
        if distance_xy(competitor_point, apex_point) < 1e-6:
            continue
        score = ownership_score(point, value, competitor_point, competitor_value, params)
        if best_other is None or score > best_other:
            best_other = score

    if best_other is None:
        return 0.0

    exceed = best_other - (target_score + params.ownership_margin)
    return max(0.0, exceed)


def infer_radius_from_profile(
    distances,
    values,
    *,
    angle,
    apex_point,
    apex_value,
    seed_radius,
    threshold,
    competing_apexes,
    params,
):
    """Infer one crown radius from a sampled radial height profile."""
    if len(values) < 6:
        return seed_radius

    smooth_values = list(values)
    for _ in range(int(params.smooth_profile_passes)):
        smooth_values = simple_line_smooth(smooth_values)

    slopes = first_derivative(smooth_values, params.profile_step_m)
    curvatures = second_derivative(smooth_values, params.profile_step_m)

    best_score = -1e18
    best_radius = seed_radius
    rebound_count = 0

    apex_x, apex_y = xy(apex_point)
    for index in range(2, len(smooth_values) - 2):
        radius = distances[index]
        height = smooth_values[index]
        slope = slopes[index]
        curvature = curvatures[index]

        if height < threshold * 0.40:
            break

        if slope > params.rebound_rise_m:
            rebound_count += 1
        else:
            rebound_count = 0

        outside_height = smooth_values[index + 1]
        edge_drop = max(0.0, height - outside_height)
        curvature_signal = abs(curvature)

        height_ratio = height / max(apex_value, 0.001)
        band_bonus = _edge_band_bonus(height_ratio, params)

        score = 0.0
        score += params.edge_drop_weight * edge_drop
        score += params.shoulder_curvature_weight * curvature_signal
        score += band_bonus
        score -= params.seed_radius_penalty * abs(radius - seed_radius)
        score -= params.low_outside_penalty * max(0.0, threshold * 0.40 - outside_height)

        if slope < -params.min_descent_slope:
            score += 0.5 * abs(slope)

        candidate_point = (
            apex_x + radius * math.cos(angle),
            apex_y + radius * math.sin(angle),
        )
        penalty = competitor_penalty(
            candidate_point,
            height,
            apex_point,
            apex_value,
            competing_apexes,
            params,
        )
        score -= params.profile_competitor_penalty * penalty

        if rebound_count >= params.rebound_steps and penalty > 0.35:
            break

        if score > best_score:
            best_score = score
            best_radius = radius

    if best_score < -1e10:
        best_radius = _last_supported_radius(distances, smooth_values, threshold, seed_radius)

    return best_radius


def infer_crown_radii(
    *,
    apex_point,
    apex_value,
    seed_radius,
    threshold,
    competing_apexes,
    params,
    sample_profile,
):
    """Infer crown radii for every configured radial angle."""
    max_search = max(
        params.profile_min_search_m,
        seed_radius * params.profile_max_factor + params.profile_max_extra_m,
    )

    radii = []
    for index in range(params.num_angles):
        angle = (2.0 * math.pi * index) / params.num_angles
        distances, values = sample_profile(apex_point, angle, max_search, params.profile_step_m)
        radii.append(
            infer_radius_from_profile(
                distances,
                values,
                angle=angle,
                apex_point=apex_point,
                apex_value=apex_value,
                seed_radius=seed_radius,
                threshold=threshold,
                competing_apexes=competing_apexes,
                params=params,
            )
        )
    return radii


def _edge_band_bonus(height_ratio, params):
    if not params.edge_height_ratio_low <= height_ratio <= params.edge_height_ratio_high:
        return 0.0

    center_of_band = (params.edge_height_ratio_low + params.edge_height_ratio_high) / 2.0
    bonus = params.edge_height_band_bonus * (
        1.0 - abs(height_ratio - center_of_band) / max(center_of_band, 0.001)
    )
    return max(0.0, bonus)


def _last_supported_radius(distances, values, threshold, seed_radius):
    last_good = seed_radius
    for radius, height in zip(distances, values):
        if height >= threshold * 0.40:
            last_good = radius
    return last_good
