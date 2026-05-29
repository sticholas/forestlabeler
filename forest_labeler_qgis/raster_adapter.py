"""QGIS raster adapter helpers."""

from __future__ import annotations

from qgis.core import QgsPointXY


def sample_raster_value(raster_layer, point_xy, band=1):
    """Sample a raster layer value, returning None when unavailable."""
    try:
        provider = raster_layer.dataProvider()
        value, ok = provider.sample(QgsPointXY(point_xy[0], point_xy[1]), band)
        if ok and value is not None:
            return float(value)
    except Exception:
        return None
    return None


def raster_sampler(raster_layer, band=1):
    """Return a callable sampler for pure raster analysis helpers."""
    return lambda point_xy: sample_raster_value(raster_layer, point_xy, band=band)
