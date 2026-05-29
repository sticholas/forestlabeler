import unittest

from forest_labeler_core.workflows import (
    WORKFLOW_CREATE_TRAINING_SQUARE,
    WORKFLOW_DETECT_APEXES,
    WORKFLOW_LABEL_CANOPY,
    get_workflow,
    list_workflows,
    workflow_requires_confirmation,
)


class WorkflowRegistryTest(unittest.TestCase):
    def test_production_priority_workflows_are_available(self):
        label_canopy = get_workflow(WORKFLOW_LABEL_CANOPY)
        training_square = get_workflow(WORKFLOW_CREATE_TRAINING_SQUARE)

        self.assertEqual(label_canopy.label, "Label Canopy")
        self.assertFalse(label_canopy.is_experimental)
        self.assertTrue(label_canopy.can_write_data)
        self.assertIn("Backend extraction", label_canopy.readiness_note)
        self.assertFalse(training_square.is_experimental)

    def test_unknown_workflow_raises_value_error(self):
        with self.assertRaises(ValueError):
            get_workflow("unknown")

    def test_can_filter_experimental_workflows(self):
        all_workflows = list_workflows(include_experimental=True)
        stable_workflows = list_workflows(include_experimental=False)

        self.assertGreater(len(all_workflows), len(stable_workflows))
        self.assertNotIn(WORKFLOW_DETECT_APEXES, [workflow.key for workflow in stable_workflows])

    def test_experimental_write_workflows_require_confirmation(self):
        apex = get_workflow(WORKFLOW_DETECT_APEXES)
        label_canopy = get_workflow(WORKFLOW_LABEL_CANOPY)

        self.assertTrue(workflow_requires_confirmation(apex))
        self.assertFalse(workflow_requires_confirmation(label_canopy))


if __name__ == "__main__":
    unittest.main()
