"""QGIS schema helpers for Training Polygon layers."""

from __future__ import annotations

from dataclasses import dataclass

from qgis.PyQt.QtCore import QVariant
from qgis.core import QgsField, QgsVectorDataProvider

from ..forest_labeler_core.training_shape_attributes import TRAINING_POLYGON_FIELD_SPECS


@dataclass(frozen=True)
class SchemaRepairResult:
    ok: bool
    added_fields: tuple
    skipped_fields: tuple
    errors: tuple


def repair_training_polygon_schema(layer):
    """Add missing optional Training Polygon fields to a writable vector layer."""
    if layer is None:
        return SchemaRepairResult(False, (), (), ("Select a target training polygon layer.",))
    if _layer_is_read_only(layer):
        return SchemaRepairResult(False, (), (), (f"'{layer.name()}' is read-only.",))

    missing_names = set(missing_training_polygon_schema_fields(layer))
    missing_specs = [
        field_spec
        for field_spec in TRAINING_POLYGON_FIELD_SPECS
        if field_spec.name in missing_names
    ]
    if not missing_specs:
        return SchemaRepairResult(True, (), (), ())

    provider = layer.dataProvider()
    if not _can_add_attributes(provider):
        return SchemaRepairResult(
            False,
            (),
            tuple(field_spec.name for field_spec in missing_specs),
            (f"'{layer.name()}' does not support adding fields.",),
        )

    fields = [_qgs_field_from_spec(field_spec) for field_spec in missing_specs]
    if not provider.addAttributes(fields):
        return SchemaRepairResult(
            False,
            (),
            tuple(field.name() for field in fields),
            (f"Could not add fields to '{layer.name()}'.",),
        )

    layer.updateFields()
    return SchemaRepairResult(
        True,
        tuple(field.name() for field in fields),
        (),
        (),
    )


def missing_training_polygon_schema_fields(layer):
    """Return Forest Labeler Training Polygon fields that are not present on the layer."""
    if layer is None:
        return ()
    existing_fields = {field.name() for field in layer.fields()}
    return tuple(
        field_spec.name
        for field_spec in TRAINING_POLYGON_FIELD_SPECS
        if field_spec.name not in existing_fields
    )


def _qgs_field_from_spec(field_spec):
    qvariant_type = {
        "int": QVariant.Int,
        "double": QVariant.Double,
        "string": QVariant.String,
    }[field_spec.value_type]
    return QgsField(
        field_spec.name,
        qvariant_type,
        len=field_spec.length or 0,
        prec=field_spec.precision or 0,
    )


def _can_add_attributes(provider):
    try:
        return bool(provider.capabilities() & QgsVectorDataProvider.AddAttributes)
    except Exception:
        return True


def _layer_is_read_only(layer):
    if hasattr(layer, "isReadOnly"):
        return layer.isReadOnly()
    if hasattr(layer, "readOnly"):
        return layer.readOnly()
    return False
