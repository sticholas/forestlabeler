"""Policy contracts for explainable Forest Labeler learning scopes."""

from __future__ import annotations

from dataclasses import dataclass


SCOPE_PROJECT = "project"
SCOPE_USER = "user"
SCOPE_TEAM = "team"
SCOPE_UNIVERSAL = "universal"

SCOPE_PRECEDENCE = (
    SCOPE_PROJECT,
    SCOPE_USER,
    SCOPE_TEAM,
    SCOPE_UNIVERSAL,
)


@dataclass(frozen=True)
class LearningContext:
    workflow: str
    algorithm_version: str
    ecosystem_tag: str | None = None
    chm_resolution_m: float | None = None


@dataclass(frozen=True)
class RecommendationEvidence:
    scope: str
    canopy_mode: str
    crown_tightness: int
    reviewed_total: int
    accepted_rate: float
    context: LearningContext | None = None
    source_label: str | None = None


@dataclass(frozen=True)
class LearningRecommendation:
    evidence: RecommendationEvidence
    explanation: str


@dataclass(frozen=True)
class SharingPolicy:
    user_local_enabled: bool = False
    team_sharing_enabled: bool = False
    universal_contribution_enabled: bool = False
    include_raw_geometry: bool = False
    include_personal_paths: bool = False


def choose_learning_recommendation(candidates, current_context, min_reviewed=3):
    """Choose the highest-trust compatible evidence with enough observations."""
    eligible = [
        candidate
        for candidate in candidates
        if candidate.scope in SCOPE_PRECEDENCE
        and _has_enough_evidence(candidate, min_reviewed)
        and contexts_are_compatible(candidate.context, current_context, candidate.scope)
    ]
    if not eligible:
        return None

    best = min(
        eligible,
        key=lambda candidate: (
            SCOPE_PRECEDENCE.index(candidate.scope),
            -candidate.reviewed_total,
            -candidate.accepted_rate,
        ),
    )
    return LearningRecommendation(best, format_recommendation_explanation(best))


def contexts_are_compatible(evidence_context, current_context, scope):
    """Return whether evidence is appropriate for the current labeling context."""
    if scope == SCOPE_UNIVERSAL:
        return True
    if evidence_context is None or current_context is None:
        return False
    if evidence_context.workflow != current_context.workflow:
        return False
    if evidence_context.algorithm_version != current_context.algorithm_version:
        return False
    if not _optional_text_matches(evidence_context.ecosystem_tag, current_context.ecosystem_tag):
        return False
    return _resolution_is_compatible(
        evidence_context.chm_resolution_m,
        current_context.chm_resolution_m,
    )


def allowed_contribution_scopes(policy: SharingPolicy):
    """Return scopes the user has explicitly allowed Forest Labeler to populate."""
    scopes = [SCOPE_PROJECT]
    if policy.user_local_enabled:
        scopes.append(SCOPE_USER)
    if policy.team_sharing_enabled:
        scopes.append(SCOPE_TEAM)
    if policy.universal_contribution_enabled:
        scopes.append(SCOPE_UNIVERSAL)
    return tuple(scopes)


def format_recommendation_explanation(evidence):
    accepted_pct = round(evidence.accepted_rate * 100.0, 1)
    source = evidence.source_label or f"{evidence.scope} evidence"
    return (
        f"Recommended {evidence.canopy_mode} mode at tightness {evidence.crown_tightness} "
        f"from {source}: {accepted_pct}% accepted across "
        f"{evidence.reviewed_total} reviewed canopies."
    )


def _has_enough_evidence(candidate, min_reviewed):
    if candidate.scope == SCOPE_UNIVERSAL:
        return True
    return candidate.reviewed_total >= min_reviewed


def _optional_text_matches(left, right):
    if not left or not right:
        return True
    return str(left).strip().lower() == str(right).strip().lower()


def _resolution_is_compatible(left, right, tolerance=0.25):
    if left is None or right is None:
        return True
    left_value = float(left)
    right_value = float(right)
    if left_value <= 0 or right_value <= 0:
        return False
    return abs(left_value - right_value) / max(left_value, right_value) <= tolerance
