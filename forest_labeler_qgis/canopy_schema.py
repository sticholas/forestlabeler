"""QGIS schema helpers for canopy target layers."""

from __future__ import annotations

from dataclasses import dataclass

from qgis.PyQt.QtCore import QVariant
from qgis.core import QgsField, QgsVectorDataProvider

from ..forest_labeler_core.canopy_attributes import CANOPY_FIELD_SPECS


@dataclass(frozen=True)
class CanopySchemaRepairResult:
    ok: bool
    added_fields: tuple
    skipped_fields: tuple
    errors: tuple


def repair_canopy_schema(layer):
    if layer is None:
        return CanopySchemaRepairResult(False, (), (), ("Select a target canopy polygon layer.",))
    if _layer_is_read_only(layer):
        return CanopySchemaRepairResult(False, (), (), (f"'{layer.name()}' is read-only.",))

    missing_names = set(missing_canopy_schema_fields(layer))
    missing = [field_spec for field_spec in CANOPY_FIELD_SPECS if field_spec.name in missing_names]
    if not missing:
        return CanopySchemaRepairResult(True, (), (), ())

    provider = layer.dataProvider()
    if not _can_add_attributes(provider):
        return CanopySchemaRepairResult(
            False,
            (),
            tuple(field_spec.name for field_spec in missing),
            (f"'{layer.name()}' does not support adding fields.",),
        )

    fields = [_qgs_field_from_spec(field_spec) for field_spec in missing]
    if not provider.addAttributes(fields):
        return CanopySchemaRepairResult(
            False,
            (),
            tuple(field.name() for field in fields),
            (f"Could not add fields to '{layer.name()}'.",),
        )

    layer.updateFields()
    return CanopySchemaRepairResult(True, tuple(field.name() for field in fields), (), ())


def missing_canopy_schema_fields(layer):
    """Return Forest Labeler canopy fields that are not present on the layer."""
    if layer is None:
        return ()
    existing = {field.name() for field in layer.fields()}
    return tuple(field_spec.name for field_spec in CANOPY_FIELD_SPECS if field_spec.name not in existing)


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
