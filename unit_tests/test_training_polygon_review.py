import unittest

from forest_labeler_core.training_polygon_review import (
    REVIEW_STATUS_ACCEPTED,
    REVIEW_STATUS_REJECTED,
    REVIEW_STATUS_UNREVIEWED,
    REVIEW_STATUS_UNSURE,
    format_training_polygon_review_summary,
    normalize_review_status,
    summarize_training_polygon_reviews,
)


class TrainingPolygonReviewTest(unittest.TestCase):
    def test_normalizes_status_and_legacy_reviewed_flags(self):
        self.assertEqual(normalize_review_status("accepted"), REVIEW_STATUS_ACCEPTED)
        self.assertEqual(normalize_review_status(" rejected "), REVIEW_STATUS_REJECTED)
        self.assertEqual(normalize_review_status("unsure"), REVIEW_STATUS_UNSURE)
        self.assertEqual(normalize_review_status("", 1), REVIEW_STATUS_ACCEPTED)
        self.assertEqual(normalize_review_status(None, -1), REVIEW_STATUS_REJECTED)
        self.assertEqual(normalize_review_status(None, 0), REVIEW_STATUS_UNREVIEWED)

    def test_summarizes_training_polygon_review_records(self):
        summary = summarize_training_polygon_reviews(
            [
                {"review_status": "accepted", "reviewed": 1},
                {"review_status": "rejected", "reviewed": -1},
                {"review_status": "unsure", "reviewed": 0},
                {"review_status": "", "reviewed": None},
                {"review_status": None, "reviewed": 1},
            ]
        )

        self.assertEqual(summary.total, 5)
        self.assertEqual(summary.reviewed_total, 4)
        self.assertEqual(summary.accepted, 2)
        self.assertEqual(summary.rejected, 1)
        self.assertEqual(summary.unsure, 1)
        self.assertEqual(summary.unreviewed, 1)
        self.assertAlmostEqual(summary.accepted_rate, 0.5)
        self.assertEqual(summary.needs_attention, 2)

    def test_formats_summary_for_status_panel(self):
        summary = summarize_training_polygon_reviews(
            [
                {"review_status": "accepted"},
                {"review_status": "accepted"},
                {"review_status": "rejected"},
                {"review_status": "unreviewed"},
            ]
        )

        lines = format_training_polygon_review_summary(summary)

        self.assertIn("Total polygons: 4", lines)
        self.assertIn("Accepted: 2 (66.7%)", lines)
        self.assertIn("Needs attention: 1 (1 rejected, 0 unsure)", lines)


if __name__ == "__main__":
    unittest.main()
