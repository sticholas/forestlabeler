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
from ..forest_labeler_core.write_safety import (
    WritePreflightInputs,
    validate_feature_write_preflight,
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
    crown_tightness=None,
    species=None,
    refined,
    ortho_id=None,
    reviewed=0,
    chm_id=None,
    require_editable=True,
):
    """Add a canopy feature to a target layer through a bounded write path."""
    preflight = _feature_write_preflight(
        target_layer,
        geometry,
        layer_label="target canopy polygon layer",
        require_editable=require_editable,
    )
    warnings = list(preflight.warnings)

    if not preflight.ok:
        return FeatureWriteResult(
            ok=False,
            feature_id=None,
            attribute_plan=None,
            errors=tuple(preflight.errors),
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
            crown_tightness=crown_tightness,
            species=species,
            reviewed=reviewed,
            refined=refined,
            chm_id=chm_id,
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

    command = _LayerEditCommand(target_layer, "Add Forest Labeler canopy")
    try:
        command.begin()
        if not target_layer.addFeature(feature):
            command.rollback()
            return FeatureWriteResult(
                ok=False,
                feature_id=None,
                attribute_plan=attribute_plan,
                errors=("Could not add the canopy polygon to the target layer.",),
                warnings=tuple(warnings),
            )
        command.commit()
    except Exception as exc:
        command.rollback()
        return FeatureWriteResult(
            ok=False,
            feature_id=None,
            attribute_plan=attribute_plan,
            errors=(f"Could not add the canopy polygon to the target layer: {exc}",),
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
    side_lengths_label,
    vertex_count,
    shape_name,
    angle_deg,
    ortho_id=None,
    plot_area=None,
    landcover_summary=None,
    reviewed=0,
    review_status="unreviewed",
    require_editable=True,
):
    """Add a training polygon feature through a bounded write path."""
    preflight = _feature_write_preflight(
        target_layer,
        geometry,
        layer_label="target training polygon layer",
        require_editable=require_editable,
    )
    warnings = list(preflight.warnings)

    if not preflight.ok:
        return FeatureWriteResult(
            ok=False,
            feature_id=None,
            attribute_plan=None,
            errors=tuple(preflight.errors),
            warnings=tuple(warnings),
        )

    attribute_plan = build_training_shape_attribute_plan(
        TrainingShapeAttributeInputs(
            next_fid=next_fid_for_layer(target_layer),
            segment_length_m=segment_length_m,
            side_lengths_label=side_lengths_label,
            vertex_count=vertex_count,
            shape_name=shape_name,
            angle_deg=angle_deg,
            geometry_area_m2=geometry.area(),
            ortho_id=ortho_id,
            plot_area=plot_area,
            landcover_summary=landcover_summary,
            reviewed=reviewed,
            review_status=review_status,
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

    command = _LayerEditCommand(target_layer, "Add Forest Labeler training polygon")
    try:
        command.begin()
        if not target_layer.addFeature(feature):
            command.rollback()
            return FeatureWriteResult(
                ok=False,
                feature_id=None,
                attribute_plan=attribute_plan,
                errors=("Could not add the training polygon to the target layer.",),
                warnings=tuple(warnings),
            )
        command.commit()
    except Exception as exc:
        command.rollback()
        return FeatureWriteResult(
            ok=False,
            feature_id=None,
            attribute_plan=attribute_plan,
            errors=(f"Could not add the training polygon to the target layer: {exc}",),
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


def _feature_write_preflight(target_layer, geometry, *, layer_label, require_editable):
    layer_selected = target_layer is not None
    geometry_present = geometry is not None
    geometry_empty = True
    geometry_valid = None

    if geometry_present:
        geometry_empty = geometry.isEmpty()
        geometry_valid = _geometry_is_valid(geometry)

    return validate_feature_write_preflight(
        WritePreflightInputs(
            layer_label=layer_label,
            layer_name=target_layer.name() if target_layer is not None else None,
            layer_selected=layer_selected,
            require_editable=require_editable,
            is_editable=target_layer.isEditable() if target_layer is not None else False,
            geometry_present=geometry_present,
            geometry_empty=geometry_empty,
            geometry_valid=geometry_valid,
        )
    )


def _geometry_is_valid(geometry):
    if hasattr(geometry, "isGeosValid"):
        try:
            return geometry.isGeosValid()
        except Exception:
            return None
    return None


class _LayerEditCommand:
    def __init__(self, layer, label):
        self.layer = layer
        self.label = label
        self.started = False

    def begin(self):
        if hasattr(self.layer, "beginEditCommand"):
            self.layer.beginEditCommand(self.label)
            self.started = True

    def commit(self):
        if self.started and hasattr(self.layer, "endEditCommand"):
            self.layer.endEditCommand()
            self.started = False

    def rollback(self):
        if self.started and hasattr(self.layer, "destroyEditCommand"):
            self.layer.destroyEditCommand()
            self.started = False
