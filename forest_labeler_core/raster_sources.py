"""Raster source classification helpers."""

from __future__ import annotations


ORTHO_EXTENSIONS = (".tif", ".tiff", ".vrt", ".img", ".jp2")
NON_ORTHO_TOKENS = (
    "google",
    "xyz",
    "wmts",
    "wms",
    "tiles",
    "arcgisonline",
    "openstreetmap",
    "mapbox",
    "bing",
    "esri",
)


def is_probable_ortho_source(name, source, provider_type, excluded_names=None):
    """Return whether a raster source looks like a local orthoimage.

    This keeps the classification rule testable without requiring QGIS imports.
    QGIS adapters can pass layer name, source, and provider type into this helper.
    """
    excluded_names = {item.lower() for item in (excluded_names or [])}
    normalized_name = (name or "").lower()
    normalized_source = (source or "").lower()
    normalized_provider = (provider_type or "").lower()

    if normalized_name in excluded_names:
        return False

    if any(token in normalized_source for token in NON_ORTHO_TOKENS):
        return False
    if any(token in normalized_name for token in NON_ORTHO_TOKENS):
        return False

    if normalized_provider != "gdal":
        return False

    return normalized_source.endswith(ORTHO_EXTENSIONS)
