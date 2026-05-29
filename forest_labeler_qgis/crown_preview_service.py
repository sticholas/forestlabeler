"""QGIS adapter for Track A crown preview generation."""

from __future__ import annotations

from dataclasses import dataclass

from qgis.core import QgsCoordinateTransform, QgsProject

from forest_labeler_core.canopy_presets import build_canopy_parameters
from forest_labeler_core.crown_builder import CrownBuildResult, build_crown_preview_points
from forest_labeler_qgis.geometry_adapter import polygon_geometry_from_points
from forest_labeler_qgis.raster_adapter import raster_sampler


@dataclass(frozen=True)
class CrownPreviewRequest:
    chm_layer: object
    target_layer: object
    center_xy: tuple
    seed_radius_m: float
    canopy_mode: str = "MIXED"
    crown_tightness: int = 11
    raster_band: int = 1


@dataclass(frozen=True)
class CrownPreviewResult:
    ok: bool
    geometry: object | None
    build_result: CrownBuildResult | None
    errors: tuple
    warnings: tuple


def build_crown_preview_geometry(request: CrownPreviewRequest):
    """Build a QGIS polygon preview from the tested core crown builder."""
    errors = []
    warnings = []

    if request.chm_layer is None:
        errors.append("Canopy height model layer is not selected.")
    if request.target_layer is None:
        errors.append("Target canopy layer is not selected.")
    if request.seed_radius_m <= 0:
        errors.append("Seed radius must be greater than zero.")

    try:
        params = build_canopy_parameters(request.canopy_mode, request.crown_tightness)
    except ValueError as exc:
        params = None
        errors.append(str(exc))

    if errors:
        return CrownPreviewResult(
            ok=False,
            geometry=None,
            build_result=None,
            errors=tuple(errors),
            warnings=tuple(warnings),
        )

    build_result = build_crown_preview_points(
        center=request.center_xy,
        seed_radius=request.seed_radius_m,
        params=params,
        sample_value=raster_sampler(request.chm_layer, band=request.raster_band),
    )
    warnings.extend(build_result.warnings)

    geometry = polygon_geometry_from_points(build_result.points)
    if geometry is None:
        errors.append("Could not build preview crown polygon geometry.")
    elif request.chm_layer.crs() != request.target_layer.crs():
        try:
            transform = QgsCoordinateTransform(
                request.chm_layer.crs(),
                request.target_layer.crs(),
                QgsProject.instance(),
            )
            geometry.transform(transform)
        except Exception:
            geometry = None
            errors.append("Could not transform preview crown polygon to the target layer CRS.")

    return CrownPreviewResult(
        ok=geometry is not None and not errors,
        geometry=geometry,
        build_result=build_result,
        errors=tuple(errors),
        warnings=tuple(warnings),
    )
