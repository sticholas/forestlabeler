"""Controlled QGIS feature-writing helpers."""

from __future__ import annotations

from dataclasses import dataclass

from qgis.core import QgsFeature

from ..forest_labeler_core.canopy_attributes import (
    AttributePlan,
    CanopyAttributeInputs,
    build_canopy_attribute_plan,
    next_numeric_fid,
)
from ..forest_labeler_core.training_shape_attributes import (
    TrainingShapeAttributeInputs,
    build_training_shape_attribute_plan,
)


@dataclass(frozen=True)
class FeatureWriteResult:
    ok: bool
    feature_id: int | None
    attribute_plan: AttributePlan | None
    errors: tuple
    warnings: tuple


def layer_field_names(layer):
    """Return field names from a QGIS vector layer."""
    return [field.name() for field in layer.fields()]


def next_fid_for_layer(layer, field_name="fid"):
    """Return the next integer fid for a layer, or None when the field is absent."""
    if layer.fields().indexOf(field_name) == -1:
        return None
    return next_numeric_fid(feature[field_name] for feature in layer.getFeatures())


def add_canopy_feature(
    target_layer,
    geometry,
    *,
    seed_radius_m,
    apex_height_m,
    canopy_mode,
    species,
    refined,
    ortho_id=None,
    reviewed=0,
    require_editable=True,
):
    """Add a canopy feature to a target layer through a bounded write path."""
    errors = []
    warnings = []

    if target_layer is None:
        errors.append("Target canopy layer is not selected.")
    elif require_editable and not target_layer.isEditable():
        errors.append(f"'{target_layer.name()}' must be in edit mode before adding canopies.")

    if geometry is None or geometry.isEmpty():
        errors.append("Canopy geometry is empty and cannot be written.")

    if errors:
        return FeatureWriteResult(
            ok=False,
            feature_id=None,
            attribute_plan=None,
            errors=tuple(errors),
            warnings=tuple(warnings),
        )

    next_fid = next_fid_for_layer(target_layer)
    attribute_plan = build_canopy_attribute_plan(
        CanopyAttributeInputs(
            next_fid=next_fid,
            seed_radius_m=seed_radius_m,
            geometry_area_m2=geometry.area(),
            apex_height_m=apex_height_m,
            canopy_mode=canopy_mode,
            species=species,
            reviewed=reviewed,
            refined=refined,
            ortho_id=ortho_id,
        ),
        layer_field_names(target_layer),
    )

    if attribute_plan.skipped_fields:
        warnings.append(
            "Skipped missing optional field(s): " + ", ".join(attribute_plan.skipped_fields) + "."
        )

    feature = QgsFeature(target_layer.fields())
    feature.setGeometry(geometry)
    for field_name, value in attribute_plan.values.items():
        field_index = feature.fields().indexOf(field_name)
        if field_index != -1:
            feature[field_name] = value

    if not target_layer.addFeature(feature):
        return FeatureWriteResult(
            ok=False,
            feature_id=None,
            attribute_plan=attribute_plan,
            errors=("Could not add the canopy polygon to the target layer.",),
            warnings=tuple(warnings),
        )

    target_layer.updateExtents()
    target_layer.triggerRepaint()

    try:
        target_layer.removeSelection()
        target_layer.selectByIds([feature.id()])
    except Exception:
        warnings.append("Canopy was added, but the new feature could not be selected.")

    return FeatureWriteResult(
        ok=True,
        feature_id=feature.id(),
        attribute_plan=attribute_plan,
        errors=(),
        warnings=tuple(warnings),
    )


def add_training_shape_feature(
    target_layer,
    geometry,
    *,
    segment_length_m,
    vertex_count,
    shape_name,
    angle_deg,
    ortho_id=None,
    require_editable=True,
):
    """Add a training shape feature through a bounded write path."""
    errors = []
    warnings = []

    if target_layer is None:
        errors.append("Target training shape layer is not selected.")
    elif require_editable and not target_layer.isEditable():
        errors.append(f"'{target_layer.name()}' must be in edit mode before adding training shapes.")

    if geometry is None or geometry.isEmpty():
        errors.append("Training shape geometry is empty and cannot be written.")

    if errors:
        return FeatureWriteResult(
            ok=False,
            feature_id=None,
            attribute_plan=None,
            errors=tuple(errors),
            warnings=tuple(warnings),
        )

    attribute_plan = build_training_shape_attribute_plan(
        TrainingShapeAttributeInputs(
            next_fid=next_fid_for_layer(target_layer),
            segment_length_m=segment_length_m,
            vertex_count=vertex_count,
            shape_name=shape_name,
            angle_deg=angle_deg,
            geometry_area_m2=geometry.area(),
            ortho_id=ortho_id,
        ),
        layer_field_names(target_layer),
    )

    if attribute_plan.skipped_fields:
        warnings.append(
            "Skipped missing optional field(s): " + ", ".join(attribute_plan.skipped_fields) + "."
        )

    feature = QgsFeature(target_layer.fields())
    feature.setGeometry(geometry)
    for field_name, value in attribute_plan.values.items():
        field_index = feature.fields().indexOf(field_name)
        if field_index != -1:
            feature[field_name] = value

    if not target_layer.addFeature(feature):
        return FeatureWriteResult(
            ok=False,
            feature_id=None,
            attribute_plan=attribute_plan,
            errors=("Could not add the training shape to the target layer.",),
            warnings=tuple(warnings),
        )

    target_layer.updateExtents()
    target_layer.triggerRepaint()

    return FeatureWriteResult(
        ok=True,
        feature_id=feature.id(),
        attribute_plan=attribute_plan,
        errors=(),
        warnings=tuple(warnings),
    )
