"""Track A service layer for canopy creation.

This module coordinates QGIS adapters and pure core decisions. Map tools should
call this service instead of directly looking up species and writing features.
"""

from __future__ import annotations

from dataclasses import dataclass, replace

from ..forest_labeler_core.canopy_attempt_log import new_canopy_attempt_id
from ..forest_labeler_core.config import SPECIES_CODE_FIELD
from .canopy_attempt_log import log_created_canopy_attempt
from .feature_writer import FeatureWriteResult, add_canopy_feature
from .species_lookup import SpeciesLookupResult, lookup_species_for_polygon


@dataclass(frozen=True)
class CanopyCreationRequest:
    target_layer: object
    geometry: object
    seed_radius_m: float
    canopy_mode: str
    crown_tightness: int | None = None
    refined: int = 0
    apex_height_m: float | None = None
    species_layer: object | None = None
    species_code_field: str = SPECIES_CODE_FIELD
    chm_id: str | None = None
    ortho_id: str | None = None
    reviewed: int = 0
    attempt_id: str | None = None
    block_multiple_species: bool = True
    warn_if_missing_species: bool = False
    require_editable: bool = True


@dataclass(frozen=True)
class CanopyCreationResult:
    ok: bool
    feature_id: int | None
    species_lookup: SpeciesLookupResult | None
    write_result: FeatureWriteResult | None
    errors: tuple
    warnings: tuple


def create_canopy_feature(request: CanopyCreationRequest):
    """Create a canopy feature using the shared Track A write path."""
    errors = []
    warnings = []
    attempt_id = request.attempt_id or new_canopy_attempt_id()
    request_with_attempt_id = replace(request, attempt_id=attempt_id)

    species_lookup = None
    species_value = None

    if request.target_layer is None:
        errors.append("Target canopy layer is not selected.")

    if request.species_layer is not None:
        if request.target_layer is None:
            errors.append("Species lookup requires a selected target canopy layer.")
        else:
            species_lookup = lookup_species_for_polygon(
                request.geometry,
                request.target_layer.crs(),
                request.species_layer,
                request.species_code_field,
                block_multiple=request.block_multiple_species,
                warn_if_missing=request.warn_if_missing_species,
            )
            errors.extend(species_lookup.errors)

            decision = species_lookup.decision
            if decision.warning:
                warnings.append(decision.warning)
            if decision.should_block:
                errors.append("Canopy feature was not written because species lookup found a conflict.")
            species_value = decision.species

    if errors:
        return CanopyCreationResult(
            ok=False,
            feature_id=None,
            species_lookup=species_lookup,
            write_result=None,
            errors=tuple(errors),
            warnings=tuple(warnings),
        )

    write_result = add_canopy_feature(
        request.target_layer,
        request.geometry,
        seed_radius_m=request.seed_radius_m,
        attempt_id=attempt_id,
        apex_height_m=request.apex_height_m,
        canopy_mode=request.canopy_mode,
        crown_tightness=request.crown_tightness,
        species=species_value,
        refined=request.refined,
        chm_id=request.chm_id,
        ortho_id=request.ortho_id,
        reviewed=request.reviewed,
        require_editable=request.require_editable,
    )

    errors.extend(write_result.errors)
    warnings.extend(write_result.warnings)

    log_result = log_created_canopy_attempt(
        request_with_attempt_id,
        CanopyCreationResult(
            ok=write_result.ok and not errors,
            feature_id=write_result.feature_id,
            species_lookup=species_lookup,
            write_result=write_result,
            errors=tuple(errors),
            warnings=tuple(warnings),
        ),
    )
    if not log_result.ok:
        warnings.extend(log_result.errors)

    return CanopyCreationResult(
        ok=write_result.ok and not errors,
        feature_id=write_result.feature_id,
        species_lookup=species_lookup,
        write_result=write_result,
        errors=tuple(errors),
        warnings=tuple(warnings),
    )
