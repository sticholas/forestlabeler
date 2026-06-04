"""Explainable canopy-setting recommendations across learning scopes."""

from __future__ import annotations

from .feedback_event_store import recommendation_evidence_from_event_store
from .learning_scopes import (
    SCOPE_PROJECT,
    SCOPE_UNIVERSAL,
    LearningContext,
    RecommendationEvidence,
    choose_learning_recommendation,
)


CANOPY_ALGORITHM_VERSION = "canopy-v1"
UNIVERSAL_CANOPY_MODE = "MIXED"
UNIVERSAL_CROWN_TIGHTNESS = 11


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
