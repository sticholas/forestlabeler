"""Explainable canopy-setting recommendations across learning scopes."""

from __future__ import annotations

from dataclasses import dataclass

from .feedback_event_store import recommendation_evidence_from_event_store
from .learning_scopes import (
    SCOPE_PROJECT,
    SCOPE_UNIVERSAL,
    LearningContext,
    RecommendationEvidence,
    choose_learning_recommendation,
    recommendation_confidence,
)


CANOPY_ALGORITHM_VERSION = "canopy-v1"
UNIVERSAL_CANOPY_MODE = "MIXED"
UNIVERSAL_CROWN_TIGHTNESS = 11


@dataclass(frozen=True)
class CanopySettingAssessment:
    evidence: RecommendationEvidence
    confidence: str
    confidence_reasons: tuple
    eligible: bool


@dataclass(frozen=True)
class CanopyRecommendationLab:
    ready_for_project_recommendations: bool
    next_action: str
    assessments: tuple


def canopy_learning_context(ecosystem_tag=None, chm_resolution_m=None):
    return LearningContext(
        workflow="label_canopy",
        algorithm_version=CANOPY_ALGORITHM_VERSION,
        ecosystem_tag=ecosystem_tag,
        chm_resolution_m=chm_resolution_m,
    )


def universal_canopy_baseline():
    return RecommendationEvidence(
        scope=SCOPE_UNIVERSAL,
        canopy_mode=UNIVERSAL_CANOPY_MODE,
        crown_tightness=UNIVERSAL_CROWN_TIGHTNESS,
        reviewed_total=0,
        accepted_rate=0.0,
        source_label="Forest Labeler universal baseline",
    )


def recommend_canopy_setting(event_store_path, context=None, min_reviewed=3):
    """Recommend from project evidence, falling back to the universal baseline."""
    current_context = context or canopy_learning_context()
    project_evidence = recommendation_evidence_from_event_store(
        event_store_path,
        scope=SCOPE_PROJECT,
        context=current_context,
        source_label="this project",
    )
    return choose_learning_recommendation(
        project_evidence + (universal_canopy_baseline(),),
        current_context,
        min_reviewed=min_reviewed,
    )


def canopy_recommendation_lab(event_store_path, context=None, min_reviewed=3):
    """Return ranked read-only evidence diagnostics for review/agent workflows."""
    current_context = context or canopy_learning_context()
    project_evidence = recommendation_evidence_from_event_store(
        event_store_path,
        scope=SCOPE_PROJECT,
        context=current_context,
        source_label="this project",
    )
    assessments = tuple(
        _assess_canopy_setting(evidence, min_reviewed=min_reviewed)
        for evidence in sorted(
            project_evidence,
            key=lambda item: (
                item.reviewed_total < min_reviewed,
                -item.accepted_rate,
                -item.reviewed_total,
                item.canopy_mode,
                item.crown_tightness,
            ),
        )
    )
    eligible = tuple(assessment for assessment in assessments if assessment.eligible)
    return CanopyRecommendationLab(
        ready_for_project_recommendations=bool(eligible),
        next_action=_recommendation_lab_next_action(assessments, min_reviewed=min_reviewed),
        assessments=assessments,
    )


def _assess_canopy_setting(evidence, min_reviewed):
    confidence, reasons = recommendation_confidence(evidence)
    return CanopySettingAssessment(
        evidence=evidence,
        confidence=confidence,
        confidence_reasons=reasons,
        eligible=evidence.reviewed_total >= min_reviewed,
    )


def _recommendation_lab_next_action(assessments, min_reviewed):
    if not assessments:
        return "Create and review canopy crowns to build project-specific evidence."
    if any(assessment.eligible for assessment in assessments):
        best = next(assessment for assessment in assessments if assessment.eligible)
        return (
            f"Project evidence is ready. Best current candidate is "
            f"{best.evidence.canopy_mode} at tightness {best.evidence.crown_tightness}."
        )
    closest = max(assessments, key=lambda assessment: assessment.evidence.reviewed_total)
    needed = max(0, min_reviewed - closest.evidence.reviewed_total)
    return (
        f"Review {needed} more canopy crown(s) for "
        f"{closest.evidence.canopy_mode} at tightness {closest.evidence.crown_tightness} "
        "to unlock project-specific recommendations."
    )
