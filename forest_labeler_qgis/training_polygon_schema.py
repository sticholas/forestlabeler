"""QGIS schema helpers for Training Polygon layers."""

from __future__ import annotations

import sqlite3
from dataclasses import dataclass
from pathlib import Path
from urllib.parse import unquote

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

    layer.updateFields()
    missing_names = set(missing_training_polygon_schema_fields(layer))
    missing_specs = [
        field_spec
        for field_spec in TRAINING_POLYGON_FIELD_SPECS
        if field_spec.name in missing_names
    ]
    if not missing_specs:
        layer.updateFields()
        return SchemaRepairResult(True, (), (), ())

    provider = layer.dataProvider()
    if not _can_add_attributes(provider):
        return SchemaRepairResult(
            False,
            (),
            tuple(field_spec.name for field_spec in missing_specs),
            (f"'{layer.name()}' does not support adding fields.",),
        )

    added = []
    skipped = []
    errors = []
    for field_spec in missing_specs:
        if field_spec.name.lower() in _existing_field_names(layer):
            skipped.append(field_spec.name)
            continue

        field = _qgs_field_from_spec(field_spec)
        if provider.addAttributes([field]):
            added.append(field.name())
            layer.updateFields()
            continue

        layer.updateFields()
        if field_spec.name.lower() in _existing_field_names(layer):
            skipped.append(field_spec.name)
            continue
        errors.append(f"Could not add field '{field_spec.name}' to '{layer.name()}'.")

    if errors:
        return SchemaRepairResult(
            False,
            tuple(added),
            tuple(skipped),
            tuple(errors),
        )

    layer.updateFields()
    return SchemaRepairResult(
        True,
        tuple(added),
        tuple(skipped),
        (),
    )


def missing_training_polygon_schema_fields(layer):
    """Return Forest Labeler Training Polygon fields that are not present on the layer."""
    if layer is None:
        return ()
    existing_fields = _existing_field_names(layer)
    return tuple(
        field_spec.name
        for field_spec in TRAINING_POLYGON_FIELD_SPECS
        if field_spec.name.lower() not in existing_fields
    )


def _existing_field_names(layer):
    names = {field.name().lower() for field in layer.fields()}
    try:
        names.update(field.name().lower() for field in layer.dataProvider().fields())
    except Exception:
        pass
    names.update(_existing_geopackage_field_names(layer))
    return names


def _existing_geopackage_field_names(layer):
    source_path = _source_path(layer)
    table_name = _source_table_name(layer)
    if source_path is None or table_name is None:
        return set()
    if source_path.suffix.lower() not in {".gpkg", ".sqlite", ".db"}:
        return set()
    if not source_path.exists():
        return set()

    try:
        with sqlite3.connect(str(source_path)) as connection:
            cursor = connection.execute(f'PRAGMA table_info("{_escape_sqlite_identifier(table_name)}")')
            return {str(row[1]).lower() for row in cursor.fetchall()}
    except Exception:
        return set()


def _source_path(layer):
    try:
        path_text = layer.source().split("|", 1)[0]
    except Exception:
        return None
    if path_text.startswith("file://"):
        path_text = path_text[len("file://"):]
    return Path(unquote(path_text))


def _source_table_name(layer):
    try:
        uri = layer.source()
    except Exception:
        return None
    for part in uri.split("|")[1:]:
        if part.startswith("layername="):
            return unquote(part.split("=", 1)[1])
    try:
        provider_uri = layer.dataProvider().uri()
        table_name = provider_uri.table()
        if table_name:
            return str(table_name)
    except Exception:
        pass
    return None


def _escape_sqlite_identifier(identifier):
    return str(identifier).replace('"', '""')


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
