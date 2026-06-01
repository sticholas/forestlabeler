import unittest

from forest_labeler_core.feedback import (
    FeedbackRecord,
    RATING_ACCEPTABLE,
    RATING_BAD,
    RATING_GOOD,
    best_feedback_bucket,
    summarize_feedback,
    validate_feedback_record,
)


class FeedbackTest(unittest.TestCase):
    def test_validates_feedback_records(self):
        self.assertEqual(
            validate_feedback_record(
                FeedbackRecord(
                    workflow="label_canopy",
                    canopy_mode="MIXED",
                    crown_tightness=11,
                    rating=RATING_GOOD,
                )
            ),
            (),
        )

        errors = validate_feedback_record(
            FeedbackRecord(
                workflow="",
                canopy_mode="MIXED",
                crown_tightness=99,
                rating="excellent",
            )
        )

        self.assertEqual(len(errors), 3)

    def test_summarizes_feedback_by_settings(self):
        summaries = summarize_feedback(
            [
                FeedbackRecord("label_canopy", "MIXED", 11, RATING_GOOD),
                FeedbackRecord("label_canopy", "MIXED", 11, RATING_ACCEPTABLE),
                FeedbackRecord("label_canopy", "MIXED", 11, RATING_BAD),
                FeedbackRecord("label_canopy", "DENSE", 17, RATING_GOOD),
            ]
        )

        mixed = summaries[1]
        self.assertEqual(mixed.workflow, "label_canopy")
        self.assertEqual(mixed.canopy_mode, "MIXED")
        self.assertEqual(mixed.crown_tightness, 11)
        self.assertEqual(mixed.total, 3)
        self.assertAlmostEqual(mixed.positive_rate, 2 / 3)

    def test_best_feedback_bucket_requires_enough_samples(self):
        records = [
            FeedbackRecord("label_canopy", "MIXED", 11, RATING_GOOD),
            FeedbackRecord("label_canopy", "MIXED", 11, RATING_GOOD),
            FeedbackRecord("label_canopy", "DENSE", 17, RATING_GOOD),
        ]

        self.assertIsNone(best_feedback_bucket(records, min_samples=3))
        best = best_feedback_bucket(records, min_samples=2)
        self.assertEqual(best.canopy_mode, "MIXED")

    def test_invalid_feedback_raises_during_summary(self):
        with self.assertRaises(ValueError):
            summarize_feedback([FeedbackRecord("", None, None, "excellent")])


if __name__ == "__main__":
    unittest.main()
