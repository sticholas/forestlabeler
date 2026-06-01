"""Pure write-safety preflight checks for feature creation."""

from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class WritePreflightInputs:
    layer_label: str
    layer_name: str | None
    layer_selected: bool
    require_editable: bool
    is_editable: bool
    geometry_present: bool
    geometry_empty: bool
    geometry_valid: bool | None = None


@dataclass(frozen=True)
class WritePreflightResult:
    errors: tuple
    warnings: tuple

    @property
    def ok(self):
        return not self.errors


def validate_feature_write_preflight(inputs: WritePreflightInputs):
    """Return clear user-facing write blockers before touching a layer."""
    errors = []
    warnings = []
    layer_name = inputs.layer_name or inputs.layer_label

    if not inputs.layer_selected:
        errors.append(f"Select a {inputs.layer_label}.")
    elif inputs.require_editable and not inputs.is_editable:
        errors.append(f"'{layer_name}' must be in edit mode before adding features.")

    if not inputs.geometry_present or inputs.geometry_empty:
        errors.append("Generated geometry is empty and cannot be written.")
    elif inputs.geometry_valid is False:
        errors.append("Generated geometry is invalid and cannot be written safely.")
    elif inputs.geometry_valid is None:
        warnings.append("Geometry validity could not be confirmed before writing.")

    return WritePreflightResult(errors=tuple(errors), warnings=tuple(warnings))
