"""Canopy feature attribute planning.

The QGIS writer should apply this plan only after validation succeeds. Keeping
the plan pure makes the write behavior reviewable and testable before it can
touch project data.
"""

from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class CanopyFieldSpec:
    name: str
    value_type: str
    length: int | None = None
    precision: int | None = None


CANOPY_FIELD_SPECS = (
    CanopyFieldSpec("fid", "int"),
    CanopyFieldSpec("radius_m", "double", precision=2),
    CanopyFieldSpec("diam_m", "double", precision=2),
    CanopyFieldSpec("area_m2", "double", precision=2),
    CanopyFieldSpec("apex_h", "double", precision=2),
    CanopyFieldSpec("mode", "string", length=40),
    CanopyFieldSpec("tightness", "int"),
    CanopyFieldSpec("num_trees", "int"),
    CanopyFieldSpec("species", "string", length=80),
    CanopyFieldSpec("reviewed", "int"),
    CanopyFieldSpec("review_status", "string", length=40),
    CanopyFieldSpec("review_note", "string", length=254),
    CanopyFieldSpec("refined", "int"),
    CanopyFieldSpec("chm_id", "string", length=254),
    CanopyFieldSpec("ortho_id", "string", length=254),
)


CANOPY_RECOMMENDED_FIELDS = tuple(field_spec.name for field_spec in CANOPY_FIELD_SPECS)


@dataclass(frozen=True)
class CanopyAttributeInputs:
    next_fid: int | None
    seed_radius_m: float
    geometry_area_m2: float
    apex_height_m: float | None
    canopy_mode: str
    crown_tightness: int | None = None
    species: str | None = None
    reviewed: int = 0
    review_status: str = "unreviewed"
    refined: int = 0
    chm_id: str | None = None
    ortho_id: str | None = None


@dataclass(frozen=True)
class AttributePlan:
    values: dict
    skipped_fields: tuple


def build_canopy_attribute_plan(inputs: CanopyAttributeInputs, available_fields):
    """Build the canopy attributes that should be written to a target feature."""
    available = set(available_fields)
    desired = {
        "fid": inputs.next_fid,
        "radius_m": round(inputs.seed_radius_m, 2),
        "diam_m": round(inputs.seed_radius_m * 2.0, 2),
        "area_m2": round(inputs.geometry_area_m2, 2),
        "apex_h": round(inputs.apex_height_m, 2) if inputs.apex_height_m is not None else None,
        "mode": inputs.canopy_mode,
        "tightness": inputs.crown_tightness,
        "num_trees": 1,
        "species": inputs.species,
        "reviewed": inputs.reviewed,
        "review_status": inputs.review_status,
        "refined": inputs.refined,
        "chm_id": inputs.chm_id,
        "ortho_id": inputs.ortho_id,
    }

    values = {
        field_name: value
        for field_name, value in desired.items()
        if field_name in available and not (field_name == "fid" and value is None)
    }
    skipped = tuple(field_name for field_name in desired if field_name not in available)
    return AttributePlan(values=values, skipped_fields=skipped)


def next_numeric_fid(existing_values):
    """Return the next positive integer fid from existing attribute values."""
    max_fid = 0
    for value in existing_values:
        try:
            if value is None:
                continue
            number = int(value)
        except (TypeError, ValueError):
            continue
        if number > max_fid:
            max_fid = number
    return max_fid + 1
