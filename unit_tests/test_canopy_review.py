import unittest

from forest_labeler_core.canopy_review import (
    CANOPY_REVIEW_FILTER_ATTENTION,
    CANOPY_REVIEW_FILTER_UNREVIEWED,
    REVIEW_STATUS_ACCEPTED,
    REVIEW_STATUS_REJECTED,
    REVIEW_STATUS_UNREVIEWED,
    best_canopy_tool_recommendation,
    canopy_review_status_matches_filter,
    canopy_quality_insight_lines,
    format_canopy_review_summary,
    normalize_canopy_review_status,
    summarize_canopy_reviews,
)


class CanopyReviewTest(unittest.TestCase):
    def test_normalizes_status_and_reviewed_flags(self):
        self.assertEqual(normalize_canopy_review_status("accepted"), REVIEW_STATUS_ACCEPTED)
        self.assertEqual(normalize_canopy_review_status(" rejected "), REVIEW_STATUS_REJECTED)
        self.assertEqual(normalize_canopy_review_status("", 1), REVIEW_STATUS_ACCEPTED)
        self.assertEqual(normalize_canopy_review_status(None, -1), REVIEW_STATUS_REJECTED)
        self.assertEqual(normalize_canopy_review_status(None, 0), REVIEW_STATUS_UNREVIEWED)

    def test_summarizes_canopy_reviews(self):
        summary = summarize_canopy_reviews(
            [
                {"review_status": "accepted"},
                {"review_status": "accepted"},
                {"review_status": "rejected"},
                {"review_status": "unsure"},
                {"review_status": "unreviewed"},
            ]
        )

        self.assertEqual(summary.total, 5)
        self.assertEqual(summary.reviewed_total, 4)
        self.assertEqual(summary.accepted, 2)
        self.assertEqual(summary.needs_attention, 2)
        self.assertAlmostEqual(summary.accepted_rate, 0.5)

    def test_review_filters_match_qa_states(self):
        self.assertTrue(
            canopy_review_status_matches_filter(None, None, CANOPY_REVIEW_FILTER_UNREVIEWED)
        )
        self.assertTrue(
            canopy_review_status_matches_filter("rejected", None, CANOPY_REVIEW_FILTER_ATTENTION)
        )
        self.assertTrue(
            canopy_review_status_matches_filter("unsure", None, CANOPY_REVIEW_FILTER_ATTENTION)
        )
        self.assertFalse(
            canopy_review_status_matches_filter("accepted", None, CANOPY_REVIEW_FILTER_ATTENTION)
        )
        with self.assertRaises(ValueError):
            canopy_review_status_matches_filter("accepted", None, "unknown")

    def test_quality_insights_group_by_mode_and_tightness(self):
        records = [
            {"mode": "MIXED", "tightness": 11, "review_status": "accepted"},
            {"mode": "MIXED", "tightness": 11, "review_status": "accepted"},
            {"mode": "MIXED", "tightness": 11, "review_status": "accepted"},
            {"mode": "DENSE", "tightness": 17, "review_status": "accepted"},
            {"mode": "DENSE", "tightness": 17, "review_status": "rejected"},
            {"mode": "DENSE", "tightness": 17, "review_status": "unsure"},
        ]

        lines = canopy_quality_insight_lines(records, min_reviewed=3)
        recommendation = best_canopy_tool_recommendation(records, min_reviewed=3)

        self.assertIn("Best canopy tool: mode=MIXED | tightness=11", lines[0])
        self.assertIn("Watch canopy tool: mode=DENSE | tightness=17", lines[1])
        self.assertEqual(recommendation.canopy_mode, "MIXED")
        self.assertEqual(recommendation.crown_tightness, 11)

    def test_quality_insights_wait_for_enough_reviews(self):
        lines = canopy_quality_insight_lines(
            [{"mode": "MIXED", "tightness": 11, "review_status": "accepted"}],
            min_reviewed=3,
        )
        recommendation = best_canopy_tool_recommendation(
            [{"mode": "MIXED", "tightness": 11, "review_status": "accepted"}],
            min_reviewed=3,
        )

        self.assertEqual(
            lines,
            ("Canopy tool insights need at least 3 reviewed crowns per mode/tightness setting.",),
        )
        self.assertIsNone(recommendation)

    def test_formats_summary(self):
        lines = format_canopy_review_summary(
            summarize_canopy_reviews(
                [{"review_status": "accepted"}, {"review_status": "rejected"}]
            )
        )

        self.assertIn("Total canopies: 2", lines)
        self.assertIn("Accepted: 1 (50.0%)", lines)


if __name__ == "__main__":
    unittest.main()
