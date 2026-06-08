"""Pure policy rules for keeping canopy review evidence trustworthy."""

from __future__ import annotations


REVIEWED_CANOPY_STATUSES = frozenset({"accepted", "rejected", "unsure"})

MATERIAL_CANOPY_FIELDS = frozenset(
    {
        "mode",
        "tightness",
        "radius_m",
        "diam_m",
        "area_m2",
        "apex_h",
        "refined",
        "chm_id",
        "ortho_id",
    }
)


def normalized_review_status(value):
    return str(value or "").strip().lower()


def canopy_is_reviewed(review_status):
    return normalized_review_status(review_status) in REVIEWED_CANOPY_STATUSES


def canopy_attribute_change_invalidates_review(field_name, previous_status):
    """Return whether an attribute edit makes the prior review stale."""
    return canopy_is_reviewed(previous_status) and str(field_name or "") in MATERIAL_CANOPY_FIELDS


def canopy_geometry_change_invalidates_review(previous_status):
    """Return whether a geometry edit makes the prior review stale."""
    return canopy_is_reviewed(previous_status)
