import unittest

from forest_labeler_core.learning_scopes import (
    SCOPE_PROJECT,
    SCOPE_TEAM,
    SCOPE_UNIVERSAL,
    SCOPE_USER,
    LearningContext,
    RecommendationEvidence,
    SharingPolicy,
    allowed_contribution_scopes,
    choose_learning_recommendation,
    contexts_are_compatible,
)


class LearningScopesTest(unittest.TestCase):
    def setUp(self):
        self.context = LearningContext(
            workflow="label_canopy",
            algorithm_version="canopy-v1",
            ecosystem_tag="dry_forest",
            chm_resolution_m=1.0,
        )
        self.universal = RecommendationEvidence(
            scope=SCOPE_UNIVERSAL,
            canopy_mode="MIXED",
            crown_tightness=11,
            reviewed_total=0,
            accepted_rate=0.0,
            source_label="Forest Labeler universal baseline",
        )

    def test_universal_baseline_is_available_for_new_user(self):
        recommendation = choose_learning_recommendation([self.universal], self.context)

        self.assertEqual(recommendation.evidence.scope, SCOPE_UNIVERSAL)
        self.assertEqual(recommendation.confidence, "starter")
        self.assertIn("universal baseline", recommendation.explanation)

    def test_project_evidence_overrides_universal_after_minimum_samples(self):
        project = RecommendationEvidence(
            scope=SCOPE_PROJECT,
            canopy_mode="DENSE",
            crown_tightness=17,
            reviewed_total=12,
            accepted_rate=0.83,
            context=self.context,
        )

        recommendation = choose_learning_recommendation([self.universal, project], self.context)

        self.assertEqual(recommendation.evidence.scope, SCOPE_PROJECT)
        self.assertEqual(recommendation.confidence, "medium")
        self.assertIn("83.0% accepted across 12 reviewed canopies", recommendation.explanation)

    def test_high_confidence_requires_larger_consistent_sample(self):
        project = RecommendationEvidence(
            scope=SCOPE_PROJECT,
            canopy_mode="DENSE",
            crown_tightness=17,
            reviewed_total=24,
            accepted_rate=0.9,
            context=self.context,
        )

        recommendation = choose_learning_recommendation([self.universal, project], self.context)

        self.assertEqual(recommendation.confidence, "high")
        self.assertIn("24 reviewed compatible canopies.", recommendation.confidence_reasons)

    def test_low_confidence_explains_need_for_more_examples(self):
        project = RecommendationEvidence(
            scope=SCOPE_PROJECT,
            canopy_mode="DENSE",
            crown_tightness=17,
            reviewed_total=3,
            accepted_rate=1.0,
            context=self.context,
        )

        recommendation = choose_learning_recommendation([self.universal, project], self.context)

        self.assertEqual(recommendation.confidence, "low")
        self.assertIn(
            "More reviewed examples are needed before trusting this strongly.",
            recommendation.confidence_reasons,
        )

    def test_under_sampled_project_does_not_override_universal(self):
        project = RecommendationEvidence(
            scope=SCOPE_PROJECT,
            canopy_mode="DENSE",
            crown_tightness=17,
            reviewed_total=2,
            accepted_rate=1.0,
            context=self.context,
        )

        recommendation = choose_learning_recommendation(
            [self.universal, project],
            self.context,
            min_reviewed=3,
        )

        self.assertEqual(recommendation.evidence.scope, SCOPE_UNIVERSAL)

    def test_incompatible_team_evidence_is_rejected(self):
        incompatible_context = LearningContext(
            workflow="label_canopy",
            algorithm_version="canopy-v2",
            ecosystem_tag="wet_forest",
            chm_resolution_m=5.0,
        )
        team = RecommendationEvidence(
            scope=SCOPE_TEAM,
            canopy_mode="SPARSE",
            crown_tightness=5,
            reviewed_total=100,
            accepted_rate=0.99,
            context=incompatible_context,
        )

        recommendation = choose_learning_recommendation([self.universal, team], self.context)

        self.assertEqual(recommendation.evidence.scope, SCOPE_UNIVERSAL)
        self.assertFalse(contexts_are_compatible(incompatible_context, self.context, SCOPE_TEAM))

    def test_precedence_prefers_project_then_user_then_team(self):
        candidates = [self.universal]
        for scope in (SCOPE_TEAM, SCOPE_USER, SCOPE_PROJECT):
            candidates.append(
                RecommendationEvidence(
                    scope=scope,
                    canopy_mode=scope.upper(),
                    crown_tightness=11,
                    reviewed_total=10,
                    accepted_rate=0.8,
                    context=self.context,
                )
            )

        recommendation = choose_learning_recommendation(candidates, self.context)

        self.assertEqual(recommendation.evidence.scope, SCOPE_PROJECT)

    def test_sharing_is_opt_in_and_project_local_by_default(self):
        self.assertEqual(allowed_contribution_scopes(SharingPolicy()), (SCOPE_PROJECT,))
        self.assertEqual(
            allowed_contribution_scopes(
                SharingPolicy(
                    user_local_enabled=True,
                    team_sharing_enabled=True,
                    universal_contribution_enabled=True,
                )
            ),
            (SCOPE_PROJECT, SCOPE_USER, SCOPE_TEAM, SCOPE_UNIVERSAL),
        )


if __name__ == "__main__":
    unittest.main()
