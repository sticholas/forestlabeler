"""QGIS adapter for species point lookup."""

from __future__ import annotations

from dataclasses import dataclass

from qgis.core import Qgis, QgsCoordinateTransform, QgsGeometry, QgsPointXY, QgsProject

from ..forest_labeler_core.species import SpeciesDecision, decide_species_assignment


@dataclass(frozen=True)
class SpeciesLookupResult:
    decision: SpeciesDecision
    errors: tuple


def lookup_species_for_polygon(
    polygon_geometry,
    target_crs,
    species_layer,
    species_code_field,
    *,
    block_multiple=True,
    warn_if_missing=False,
):
    """Find species points inside a canopy polygon and return a pure decision."""
    errors = []

    if species_layer is None:
        return SpeciesLookupResult(
            decision=decide_species_assignment([], warn_if_missing=warn_if_missing),
            errors=("Species point layer is not selected.",),
        )

    if species_layer.geometryType() != Qgis.GeometryType.Point:
        return SpeciesLookupResult(
            decision=decide_species_assignment([], warn_if_missing=warn_if_missing),
            errors=(f"'{species_layer.name()}' must be a point layer.",),
        )

    if species_layer.fields().indexOf(species_code_field) == -1:
        return SpeciesLookupResult(
            decision=decide_species_assignment([], warn_if_missing=warn_if_missing),
            errors=(f"'{species_layer.name()}' is missing field '{species_code_field}'.",),
        )

    test_geometry = QgsGeometry(polygon_geometry)
    if target_crs != species_layer.crs():
        try:
            transform = QgsCoordinateTransform(
                target_crs,
                species_layer.crs(),
                QgsProject.instance(),
            )
            test_geometry.transform(transform)
        except Exception:
            return SpeciesLookupResult(
                decision=decide_species_assignment([], warn_if_missing=warn_if_missing),
                errors=("Could not transform canopy polygon to the species point layer CRS.",),
            )

    matches = []
    for point_feature in species_layer.getFeatures():
        point_geometry = point_feature.geometry()
        if point_geometry is None or point_geometry.isEmpty():
            continue

        point_xy = point_geometry.asPoint()
        if test_geometry.contains(QgsGeometry.fromPointXY(QgsPointXY(point_xy))):
            code_value = point_feature[species_code_field]
            if code_value is not None and str(code_value).strip():
                matches.append(str(code_value).strip())

    return SpeciesLookupResult(
        decision=decide_species_assignment(
            matches,
            block_multiple=block_multiple,
            warn_if_missing=warn_if_missing,
        ),
        errors=tuple(errors),
    )
