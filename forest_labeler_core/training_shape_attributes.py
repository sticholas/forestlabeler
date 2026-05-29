"""Training shape feature attribute planning."""

from __future__ import annotations

from dataclasses import dataclass

from .canopy_attributes import AttributePlan


@dataclass(frozen=True)
class TrainingShapeAttributeInputs:
    next_fid: int | None
    segment_length_m: float
    vertex_count: int
    shape_name: str
    angle_deg: float
    geometry_area_m2: float
    ortho_id: str | None = None


def build_training_shape_attribute_plan(inputs: TrainingShapeAttributeInputs, available_fields):
    """Build optional metadata for a stamped training polygon."""
    available = set(available_fields)
    desired = {
        "fid": inputs.next_fid,
        "segment_m": round(inputs.segment_length_m, 2),
        "side_m": round(inputs.segment_length_m, 2),
        "nodes": inputs.vertex_count,
        "vertices": inputs.vertex_count,
        "shape": inputs.shape_name,
        "angle": round(inputs.angle_deg, 2),
        "area_m2": round(inputs.geometry_area_m2, 2),
        "ortho_id": inputs.ortho_id,
    }
    values = {
        field_name: value
        for field_name, value in desired.items()
        if field_name in available and not (field_name == "fid" and value is None)
    }
    skipped = tuple(field_name for field_name in desired if field_name not in available)
    return AttributePlan(values=values, skipped_fields=skipped)
