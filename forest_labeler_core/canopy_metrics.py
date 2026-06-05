"""Pure canopy metric update planning."""

from __future__ import annotations


def canopy_chm_metric_updates(apex_height_m, chm_id=None):
    """Return attribute updates for CHM-derived canopy metrics."""
    try:
        apex = float(apex_height_m)
    except (TypeError, ValueError):
        return {}
    updates = {"apex_h": round(apex, 2)}
    if chm_id:
        updates["chm_id"] = str(chm_id)
    return updates
