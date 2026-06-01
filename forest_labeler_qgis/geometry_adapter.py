"""QGIS geometry adapters for canopy helpers."""

from __future__ import annotations

from qgis.core import QgsCoordinateTransform, QgsGeometry, QgsPointXY, QgsProject

from ..forest_labeler_core.geometry_math import circle_points, radii_to_points


def polygon_geometry_from_points(points):
    """Create a QGIS polygon geometry from tuple points."""
    if len(points) < 4:
        return None
    qgs_points = [QgsPointXY(x, y) for x, y in points]
    return QgsGeometry.fromPolygonXY([qgs_points])


def circle_geometry(center_xy, radius_m, segments=72):
    """Create a QGIS polygon approximating a circle."""
    return polygon_geometry_from_points(circle_points(center_xy, radius_m, segments))


def radii_polygon_geometry(apex_xy, radii, source_crs, target_crs):
    """Create a QGIS polygon from radial crown distances and transform if needed."""
    points = radii_to_points(apex_xy, radii)
    if not points:
        return None

    geometry = polygon_geometry_from_points(points)
    if geometry is None:
        return None

    if source_crs != target_crs:
        try:
            transform = QgsCoordinateTransform(source_crs, target_crs, QgsProject.instance())
            geometry.transform(transform)
        except Exception:
            return None

    return geometry
