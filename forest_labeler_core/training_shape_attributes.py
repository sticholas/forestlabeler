"""Training shape feature attribute planning."""

from __future__ import annotations

from dataclasses import dataclass

from .canopy_attributes import AttributePlan


@dataclass(frozen=True)
class TrainingPolygonFieldSpec:
    name: str
    value_type: str
    length: int | None = None
    precision: int | None = None


TRAINING_POLYGON_FIELD_SPECS = (
    TrainingPolygonFieldSpec("fid", "int"),
    TrainingPolygonFieldSpec("segment_m", "double", precision=2),
    TrainingPolygonFieldSpec("side_m", "double", precision=2),
    TrainingPolygonFieldSpec("side_lengths", "string", length=160),
    TrainingPolygonFieldSpec("nodes", "int"),
    TrainingPolygonFieldSpec("vertices", "int"),
    TrainingPolygonFieldSpec("shape", "string", length=40),
    TrainingPolygonFieldSpec("angle", "double", precision=2),
    TrainingPolygonFieldSpec("area_m2", "double", precision=2),
    TrainingPolygonFieldSpec("ortho_id", "string", length=254),
    TrainingPolygonFieldSpec("plot_area", "string", length=120),
    TrainingPolygonFieldSpec("Detailed_L_count", "int"),
    TrainingPolygonFieldSpec("Detailed_L_majority", "string", length=120),
    TrainingPolygonFieldSpec("Detailed_L_majority_pct", "double", precision=1),
    TrainingPolygonFieldSpec("Detailed_L1", "string", length=120),
    TrainingPolygonFieldSpec("Detailed_L1_pct", "double", precision=1),
    TrainingPolygonFieldSpec("Detailed_L2", "string", length=120),
    TrainingPolygonFieldSpec("Detailed_L2_pct", "double", precision=1),
    TrainingPolygonFieldSpec("Detailed_L3", "string", length=120),
    TrainingPolygonFieldSpec("Detailed_L3_pct", "double", precision=1),
    TrainingPolygonFieldSpec("Detailed_L_other_pct", "double", precision=1),
    TrainingPolygonFieldSpec("reviewed", "int"),
    TrainingPolygonFieldSpec("review_status", "string", length=40),
    TrainingPolygonFieldSpec("review_note", "string", length=254),
)


TRAINING_POLYGON_RECOMMENDED_FIELDS = tuple(
    field_spec.name for field_spec in TRAINING_POLYGON_FIELD_SPECS
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
    reviewed: int = 0
    review_status: str = "unreviewed"


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
        "reviewed": inputs.reviewed,
        "review_status": inputs.review_status,
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
