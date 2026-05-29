"""Training shape feature attribute planning."""

from __future__ import annotations

from dataclasses import dataclass

from .canopy_attributes import AttributePlan


TRAINING_POLYGON_RECOMMENDED_FIELDS = (
    "fid",
    "segment_m",
    "side_m",
    "side_lengths",
    "nodes",
    "vertices",
    "shape",
    "angle",
    "area_m2",
    "ortho_id",
    "plot_area",
    "Detailed_L_count",
    "Detailed_L_majority",
    "Detailed_L_majority_pct",
    "Detailed_L1",
    "Detailed_L1_pct",
    "Detailed_L2",
    "Detailed_L2_pct",
    "Detailed_L3",
    "Detailed_L3_pct",
    "Detailed_L_other_pct",
)


@dataclass(frozen=True)
class TrainingShapeAttributeInputs:
    next_fid: int | None
    segment_length_m: float
    side_lengths_label: str
    vertex_count: int
    shape_name: str
    angle_deg: float
    geometry_area_m2: float
    ortho_id: str | None = None
    plot_area: str | None = None
    landcover_summary: dict | None = None


def build_training_shape_attribute_plan(inputs: TrainingShapeAttributeInputs, available_fields):
    """Build optional metadata for a stamped training polygon."""
    available = set(available_fields)
    desired = {
        "fid": inputs.next_fid,
        "segment_m": round(inputs.segment_length_m, 2),
        "side_m": round(inputs.segment_length_m, 2),
        "side_lengths": inputs.side_lengths_label,
        "nodes": inputs.vertex_count,
        "vertices": inputs.vertex_count,
        "shape": inputs.shape_name,
        "angle": round(inputs.angle_deg, 2),
        "area_m2": round(inputs.geometry_area_m2, 2),
        "ortho_id": inputs.ortho_id,
        "plot_area": inputs.plot_area,
    }
    if inputs.landcover_summary:
        desired.update(inputs.landcover_summary)
    values = {
        field_name: value
        for field_name, value in desired.items()
        if field_name in available and value is not None and not (field_name == "fid" and value is None)
    }
    skipped = tuple(field_name for field_name in desired if field_name not in available)
    return AttributePlan(values=values, skipped_fields=skipped)
