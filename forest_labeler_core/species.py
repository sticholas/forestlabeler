"""Species assignment decision helpers."""

from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class SpeciesDecision:
    species: str | None
    point_count: int
    warning: str | None
    should_block: bool


def decide_species_assignment(matches, block_multiple=True, warn_if_missing=False):
    """Decide species value and conflict behavior from matched species codes."""
    cleaned = [str(value).strip() for value in matches if value is not None and str(value).strip()]

    if not cleaned:
        return SpeciesDecision(
            species=None,
            point_count=0,
            warning="No species point found inside polygon." if warn_if_missing else None,
            should_block=False,
        )

    if len(cleaned) == 1:
        return SpeciesDecision(
            species=cleaned[0],
            point_count=1,
            warning=None,
            should_block=False,
        )

    unique_species = sorted(set(cleaned))
    return SpeciesDecision(
        species=None,
        point_count=len(cleaned),
        warning=(
            "Multiple species points found inside polygon. "
            "Point species found: " + ", ".join(unique_species) + "."
        ),
        should_block=bool(block_multiple),
    )
