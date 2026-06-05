"""QGIS services for recalculating selected canopy metrics."""

from __future__ import annotations

import math
from dataclasses import dataclass

from qgis.core import QgsCoordinateTransform, QgsFeatureRequest, QgsGeometry, QgsPointXY, QgsProject

from ..forest_labeler_core.canopy_metrics import canopy_chm_metric_updates
from .raster_adapter import sample_raster_value


@dataclass(frozen=True)
class CanopyMetricUpdateResult:
    ok: bool
    updated_count: int
    errors: tuple
    warnings: tuple


def recalculate_selected_canopy_chm_metrics(layer, chm_layer, max_samples=5000):
    """Recalculate CHM-derived metrics for selected canopy features."""
    errors = []
    warnings = []
    if layer is None:
        errors.append("Select a target canopy polygon layer.")
    elif not layer.isEditable():
        errors.append(f"Turn editing on for '{layer.name()}' before recalculating CHM metrics.")
    if chm_layer is None:
        errors.append("Select a CHM raster layer.")
    if errors:
        return CanopyMetricUpdateResult(False, 0, tuple(errors), tuple(warnings))

    selected_ids = tuple(layer.selectedFeatureIds())
    if not selected_ids:
        return CanopyMetricUpdateResult(False, 0, ("Select one or more canopy features.",), ())

    apex_index = layer.fields().indexOf("apex_h")
    chm_index = layer.fields().indexOf("chm_id")
    if apex_index == -1 and chm_index == -1:
        return CanopyMetricUpdateResult(
            False,
            0,
            ("Missing CHM metric field(s): apex_h or chm_id.",),
            (),
        )

    features = layer.getFeatures(QgsFeatureRequest().setFilterFids(list(selected_ids)))
    updated_count = 0
    for feature in features:
        geometry = QgsGeometry(feature.geometry())
        if geometry.isEmpty():
            warnings.append(f"Feature {feature.id()} has empty geometry.")
            continue
        chm_geometry = _geometry_in_chm_crs(geometry, layer, chm_layer)
        apex_height = _max_raster_value_inside_geometry(chm_geometry, chm_layer, max_samples=max_samples)
        if apex_height is None:
            warnings.append(f"Could not sample CHM inside feature {feature.id()}.")
            continue
        updates = canopy_chm_metric_updates(apex_height, _layer_source(chm_layer))
        if apex_index != -1 and "apex_h" in updates:
            if not layer.changeAttributeValue(feature.id(), apex_index, updates["apex_h"]):
                warnings.append(f"Could not update apex_h for feature {feature.id()}.")
                continue
        if chm_index != -1 and "chm_id" in updates:
            if not layer.changeAttributeValue(feature.id(), chm_index, updates["chm_id"]):
                warnings.append(f"Could not update chm_id for feature {feature.id()}.")
        updated_count += 1

    layer.triggerRepaint()
    return CanopyMetricUpdateResult(
        ok=updated_count > 0,
        updated_count=updated_count,
        errors=() if updated_count > 0 else ("No selected canopy metrics were updated.",),
        warnings=tuple(warnings),
    )


def recalculate_canopy_chm_metrics_by_id(layer, chm_layer, feature_id, geometry=None, max_samples=5000):
    """Recalculate CHM metrics for one feature id without requiring selection."""
    if layer is None or chm_layer is None:
        return CanopyMetricUpdateResult(False, 0, ("Select a canopy layer and CHM raster.",), ())
    if feature_id is None:
        return CanopyMetricUpdateResult(False, 0, ("Feature id is required.",), ())

    feature = next(layer.getFeatures(QgsFeatureRequest().setFilterFid(feature_id)), None)
    if feature is None:
        return CanopyMetricUpdateResult(False, 0, (f"Could not read canopy feature {feature_id}.",), ())
    target_geometry = QgsGeometry(feature.geometry()) if geometry is None else QgsGeometry(geometry)
    return _recalculate_feature_chm_metrics(layer, chm_layer, feature_id, target_geometry, max_samples=max_samples)


def _recalculate_feature_chm_metrics(layer, chm_layer, feature_id, geometry, max_samples):
    apex_index = layer.fields().indexOf("apex_h")
    chm_index = layer.fields().indexOf("chm_id")
    if apex_index == -1 and chm_index == -1:
        return CanopyMetricUpdateResult(False, 0, ("Missing CHM metric field(s): apex_h or chm_id.",), ())
    if geometry.isEmpty():
        return CanopyMetricUpdateResult(False, 0, (f"Feature {feature_id} has empty geometry.",), ())

    chm_geometry = _geometry_in_chm_crs(geometry, layer, chm_layer)
    apex_height = _max_raster_value_inside_geometry(chm_geometry, chm_layer, max_samples=max_samples)
    if apex_height is None:
        return CanopyMetricUpdateResult(False, 0, (f"Could not sample CHM inside feature {feature_id}.",), ())

    updates = canopy_chm_metric_updates(apex_height, _layer_source(chm_layer))
    warnings = []
    if apex_index != -1 and "apex_h" in updates:
        if not layer.changeAttributeValue(feature_id, apex_index, updates["apex_h"]):
            return CanopyMetricUpdateResult(False, 0, (f"Could not update apex_h for feature {feature_id}.",), ())
    if chm_index != -1 and "chm_id" in updates:
        if not layer.changeAttributeValue(feature_id, chm_index, updates["chm_id"]):
            warnings.append(f"Could not update chm_id for feature {feature_id}.")
    layer.triggerRepaint()
    return CanopyMetricUpdateResult(True, 1, (), tuple(warnings))


def _geometry_in_chm_crs(geometry, layer, chm_layer):
    if layer.crs() == chm_layer.crs():
        return geometry
    transformed = QgsGeometry(geometry)
    transform = QgsCoordinateTransform(layer.crs(), chm_layer.crs(), QgsProject.instance())
    transformed.transform(transform)
    return transformed


def _max_raster_value_inside_geometry(geometry, chm_layer, max_samples):
    bbox = geometry.boundingBox()
    if bbox.isEmpty():
        return None
    step = _sample_step(chm_layer, bbox, max_samples=max_samples)
    best = None
    x = bbox.xMinimum()
    while x <= bbox.xMaximum() + 1e-9:
        y = bbox.yMinimum()
        while y <= bbox.yMaximum() + 1e-9:
            point = QgsPointXY(x, y)
            if geometry.contains(QgsGeometry.fromPointXY(point)):
                value = sample_raster_value(chm_layer, (x, y))
                if value is not None and (best is None or value > best):
                    best = value
            y += step
        x += step
    if best is None:
        centroid = geometry.centroid()
        if centroid is not None and not centroid.isEmpty():
            point = centroid.asPoint()
            best = sample_raster_value(chm_layer, (point.x(), point.y()))
    return best


def _sample_step(chm_layer, bbox, max_samples):
    try:
        base_step = max(
            abs(float(chm_layer.rasterUnitsPerPixelX())),
            abs(float(chm_layer.rasterUnitsPerPixelY())),
        )
    except Exception:
        base_step = 1.0
    width = max(float(bbox.width()), base_step)
    height = max(float(bbox.height()), base_step)
    estimated = (width / base_step) * (height / base_step)
    if estimated <= max_samples:
        return base_step
    return max(base_step, math.sqrt((width * height) / max_samples))


def _layer_source(layer):
    try:
        return layer.source()
    except Exception:
        return None
