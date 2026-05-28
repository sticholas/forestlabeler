"""Canopy mode and crown-tightness settings.

This module is migrated from `prototypes/canopies_workflow/CanopyCrownLabeler.py`
without QGIS dependencies so it can be tested outside QGIS.
"""

from __future__ import annotations

from dataclasses import dataclass, replace


VALID_CANOPY_MODES = ("DENSE", "SPARSE", "MIXED")
NORMAL_CROWN_TIGHTNESS = 11
MIN_CROWN_TIGHTNESS = 1
MAX_CROWN_TIGHTNESS = 21


@dataclass(frozen=True)
class CanopyParameters:
    mode: str
    crown_tightness: int
    start_radius_m: float = 0.75
    max_radius_m: float = 35.0
    growth_per_tick_m: float = 0.35
    timer_interval_ms: int = 60
    local_apex_search_radius_m: float = 2.0
    num_angles: int = 48
    profile_step_m: float = 0.35
    inner_support_radius_factor: float = 0.20
    inner_support_radius_min_m: float = 1.0
    competing_apex_min_separation_m: float = 1.5
    ownership_distance_weight: float = 0.10
    ownership_drop_weight: float = 0.12
    envelope_margin_factor: float = 1.10
    gaussian_smooth_radius: int = 2
    gaussian_smooth_sigma: float = 1.1
    gaussian_smooth_passes: int = 1
    final_buffer_smooth_m: float = 0.35
    min_grid_size_m: float = 0.25
    max_grid_size_m: float = 1.50
    min_canopy_height_m: float = 0.0
    center_height_fraction: float = 0.0
    inner_support_fraction: float = 0.0
    profile_max_factor: float = 0.0
    profile_max_extra_m: float = 0.0
    profile_min_search_m: float = 0.0
    min_descent_slope: float = 0.0
    rebound_rise_m: float = 0.0
    rebound_steps: int = 2
    edge_drop_weight: float = 0.0
    shoulder_curvature_weight: float = 0.0
    edge_height_ratio_low: float = 0.0
    edge_height_ratio_high: float = 0.0
    edge_height_band_bonus: float = 0.0
    competing_apex_search_factor: float = 0.0
    competing_apex_extra_m: float = 0.0
    competing_apex_min_relative_height: float = 0.0
    ownership_margin: float = 0.0
    seed_radius_penalty: float = 0.08
    low_outside_penalty: float = 0.55
    profile_competitor_penalty: float = 0.0
    smooth_profile_passes: int = 3
    smooth_radius_passes: int = 2
    smooth_radius_window: int = 2


BASE_PRESETS = {
    "DENSE": CanopyParameters(
        mode="DENSE",
        crown_tightness=NORMAL_CROWN_TIGHTNESS,
        min_canopy_height_m=1.5,
        center_height_fraction=0.12,
        inner_support_fraction=0.18,
        profile_max_factor=1.60,
        profile_max_extra_m=4.0,
        profile_min_search_m=3.0,
        min_descent_slope=0.015,
        rebound_rise_m=0.80,
        edge_drop_weight=2.1,
        shoulder_curvature_weight=1.5,
        edge_height_ratio_low=0.08,
        edge_height_ratio_high=0.30,
        edge_height_band_bonus=1.8,
        competing_apex_search_factor=1.80,
        competing_apex_extra_m=3.0,
        competing_apex_min_relative_height=0.30,
        ownership_margin=0.18,
        profile_competitor_penalty=1.25,
    ),
    "SPARSE": CanopyParameters(
        mode="SPARSE",
        crown_tightness=NORMAL_CROWN_TIGHTNESS,
        min_canopy_height_m=0.8,
        center_height_fraction=0.06,
        inner_support_fraction=0.10,
        profile_max_factor=2.30,
        profile_max_extra_m=8.0,
        profile_min_search_m=4.0,
        min_descent_slope=0.006,
        rebound_rise_m=1.40,
        edge_drop_weight=1.7,
        shoulder_curvature_weight=1.3,
        edge_height_ratio_low=0.04,
        edge_height_ratio_high=0.45,
        edge_height_band_bonus=1.5,
        competing_apex_search_factor=1.40,
        competing_apex_extra_m=2.5,
        competing_apex_min_relative_height=0.45,
        ownership_margin=0.40,
        profile_competitor_penalty=0.50,
    ),
    "MIXED": CanopyParameters(
        mode="MIXED",
        crown_tightness=NORMAL_CROWN_TIGHTNESS,
        min_canopy_height_m=1.2,
        center_height_fraction=0.10,
        inner_support_fraction=0.16,
        profile_max_factor=1.90,
        profile_max_extra_m=5.0,
        profile_min_search_m=3.0,
        min_descent_slope=0.010,
        rebound_rise_m=1.10,
        edge_drop_weight=1.9,
        shoulder_curvature_weight=1.4,
        edge_height_ratio_low=0.06,
        edge_height_ratio_high=0.35,
        edge_height_band_bonus=1.6,
        competing_apex_search_factor=1.60,
        competing_apex_extra_m=3.0,
        competing_apex_min_relative_height=0.35,
        ownership_margin=0.28,
        profile_competitor_penalty=0.90,
    ),
}


def build_canopy_parameters(mode: str, crown_tightness: int) -> CanopyParameters:
    """Build canopy parameters for a mode and 1..21 crown-tightness value."""
    normalized_mode = mode.upper()
    if normalized_mode not in BASE_PRESETS:
        raise ValueError("mode must be one of: " + ", ".join(VALID_CANOPY_MODES))

    params = replace(
        BASE_PRESETS[normalized_mode],
        crown_tightness=_clamp_tightness(crown_tightness),
    )
    return _apply_crown_tightness(params)


def _clamp_tightness(value: int) -> int:
    return max(MIN_CROWN_TIGHTNESS, min(MAX_CROWN_TIGHTNESS, int(value)))


def _apply_crown_tightness(params: CanopyParameters) -> CanopyParameters:
    tight = params.crown_tightness - NORMAL_CROWN_TIGHTNESS
    if tight == 0:
        return params

    params = replace(
        params,
        profile_max_factor=params.profile_max_factor * (1.0 - 0.035 * tight),
        profile_max_extra_m=params.profile_max_extra_m * (1.0 - 0.045 * tight),
        edge_drop_weight=params.edge_drop_weight * (1.0 + 0.055 * tight),
        shoulder_curvature_weight=params.shoulder_curvature_weight * (1.0 + 0.040 * tight),
        edge_height_band_bonus=params.edge_height_band_bonus * (1.0 + 0.040 * tight),
        competing_apex_search_factor=params.competing_apex_search_factor
        * (1.0 + 0.045 * tight),
        competing_apex_extra_m=params.competing_apex_extra_m * (1.0 + 0.030 * tight),
        competing_apex_min_relative_height=params.competing_apex_min_relative_height
        * (1.0 - 0.025 * tight),
        ownership_margin=params.ownership_margin * (1.0 - 0.045 * tight),
        profile_competitor_penalty=params.profile_competitor_penalty
        * (1.0 + 0.105 * tight),
        min_descent_slope=params.min_descent_slope * (1.0 + 0.080 * tight),
        rebound_rise_m=params.rebound_rise_m * (1.0 - 0.030 * tight),
        low_outside_penalty=params.low_outside_penalty * (1.0 + 0.060 * tight),
        seed_radius_penalty=params.seed_radius_penalty * (1.0 + 0.040 * tight),
        final_buffer_smooth_m=params.final_buffer_smooth_m * (1.0 - 0.035 * tight),
    )

    if params.crown_tightness >= 17:
        params = replace(
            params,
            num_angles=max(params.num_angles, 72),
            profile_step_m=max(0.18, params.profile_step_m * 0.90),
            smooth_radius_passes=max(params.smooth_radius_passes, 2),
            smooth_radius_window=max(params.smooth_radius_window, 2),
            gaussian_smooth_radius=max(params.gaussian_smooth_radius, 3),
            gaussian_smooth_sigma=max(params.gaussian_smooth_sigma, 1.25),
            gaussian_smooth_passes=max(params.gaussian_smooth_passes, 2),
            final_buffer_smooth_m=max(params.final_buffer_smooth_m, 0.18),
        )

    if params.crown_tightness >= 20:
        params = replace(
            params,
            num_angles=max(params.num_angles, 84),
            profile_step_m=max(0.15, params.profile_step_m * 0.85),
            gaussian_smooth_radius=max(params.gaussian_smooth_radius, 4),
            gaussian_smooth_sigma=max(params.gaussian_smooth_sigma, 1.45),
            gaussian_smooth_passes=max(params.gaussian_smooth_passes, 2),
            final_buffer_smooth_m=max(params.final_buffer_smooth_m, 0.22),
        )

    if params.crown_tightness <= 5:
        params = replace(
            params,
            num_angles=min(params.num_angles, 40),
            smooth_radius_passes=max(params.smooth_radius_passes, 3),
            smooth_radius_window=max(params.smooth_radius_window, 3),
            gaussian_smooth_radius=max(params.gaussian_smooth_radius, 4),
            gaussian_smooth_sigma=max(params.gaussian_smooth_sigma, 1.60),
            gaussian_smooth_passes=max(params.gaussian_smooth_passes, 2),
            final_buffer_smooth_m=max(params.final_buffer_smooth_m, 0.45),
        )

    return replace(
        params,
        profile_max_factor=max(0.45, params.profile_max_factor),
        profile_max_extra_m=max(0.35, params.profile_max_extra_m),
        competing_apex_min_relative_height=max(
            0.08, min(0.92, params.competing_apex_min_relative_height)
        ),
        ownership_margin=max(0.015, params.ownership_margin),
        profile_competitor_penalty=max(0.05, params.profile_competitor_penalty),
        min_descent_slope=max(0.0008, params.min_descent_slope),
        rebound_rise_m=max(0.15, params.rebound_rise_m),
        final_buffer_smooth_m=max(0.08, params.final_buffer_smooth_m),
        profile_step_m=max(0.12, params.profile_step_m),
    )
