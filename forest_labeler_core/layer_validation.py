"""QGIS layer validation for Forest Labeler workflows."""

from dataclasses import dataclass

from qgis.core import Qgis, QgsRasterLayer, QgsVectorLayer, QgsWkbTypes

from .config import SPECIES_CODE_FIELD, TARGET_RECOMMENDED_FIELDS, TARGET_REQUIRED_FIELDS


@dataclass
class ValidationResult:
    """Validation messages for the currently selected QGIS layers."""

    errors: list
    warnings: list

    @property
    def ok(self):
        return not self.errors


def validate_plugin_layers(chm_layer, target_layer, species_layer=None):
    """Validate selected input/output layers before enabling edit tools."""
    errors = []
    warnings = []

    _validate_chm_layer(chm_layer, errors)
    _validate_target_layer(target_layer, errors, warnings)
    _validate_species_layer(species_layer, errors)

    return ValidationResult(errors=errors, warnings=warnings)


def _validate_chm_layer(layer, errors):
    if layer is None:
        errors.append("Select a canopy height model raster layer.")
        return

    if not isinstance(layer, QgsRasterLayer):
        errors.append(f"'{layer.name()}' must be a raster layer.")
        return

    if not layer.isValid():
        errors.append(f"'{layer.name()}' is not a valid raster layer.")


def _validate_target_layer(layer, errors, warnings):
    if layer is None:
        errors.append("Select a target canopy polygon layer.")
        return

    if not isinstance(layer, QgsVectorLayer):
        errors.append(f"'{layer.name()}' must be a vector polygon layer.")
        return

    if not layer.isValid():
        errors.append(f"'{layer.name()}' is not a valid vector layer.")
        return

    if layer.geometryType() != Qgis.GeometryType.Polygon:
        errors.append(f"'{layer.name()}' must have polygon geometry.")

    if QgsWkbTypes.hasZ(layer.wkbType()):
        warnings.append(f"'{layer.name()}' has Z values; generated canopy geometry will be 2D.")

    fields = layer.fields()
    missing_required = [field for field in TARGET_REQUIRED_FIELDS if fields.indexOf(field) == -1]
    if missing_required:
        errors.append(
            f"'{layer.name()}' is missing required field(s): {', '.join(missing_required)}."
        )

    missing_recommended = [
        field for field in TARGET_RECOMMENDED_FIELDS if fields.indexOf(field) == -1
    ]
    if missing_recommended:
        warnings.append(
            f"'{layer.name()}' is missing optional metadata field(s): "
            + ", ".join(missing_recommended)
            + "."
        )

    if layer.isReadOnly():
        errors.append(f"'{layer.name()}' is read-only and cannot receive canopy features.")


def _validate_species_layer(layer, errors):
    if layer is None:
        return

    if not isinstance(layer, QgsVectorLayer):
        errors.append(f"'{layer.name()}' must be a vector point layer.")
        return

    if not layer.isValid():
        errors.append(f"'{layer.name()}' is not a valid species point layer.")
        return

    if layer.geometryType() != Qgis.GeometryType.Point:
        errors.append(f"'{layer.name()}' must have point geometry.")

    if layer.fields().indexOf(SPECIES_CODE_FIELD) == -1:
        errors.append(
            f"'{layer.name()}' is missing species code field '{SPECIES_CODE_FIELD}'."
        )
