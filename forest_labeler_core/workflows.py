"""Workflow registry for Forest Labeler modes."""

from __future__ import annotations

from dataclasses import dataclass


MATURITY_PRODUCTION_TARGET = "production_target"
MATURITY_EXPERIMENTAL = "experimental"

WORKFLOW_LABEL_CANOPY = "label_canopy"
WORKFLOW_CREATE_TRAINING_SQUARE = "create_training_square"
WORKFLOW_PROPOSE_CANOPIES = "propose_canopies"
WORKFLOW_DETECT_APEXES = "detect_apexes"
WORKFLOW_VALIDATE_PROJECT = "validate_project"


@dataclass(frozen=True)
class WorkflowDefinition:
    key: str
    label: str
    maturity: str
    source_script: str | None
    purpose: str
    can_write_data: bool
    readiness_note: str
    experimental_warning: str | None = None

    @property
    def is_experimental(self):
        return self.maturity == MATURITY_EXPERIMENTAL


WORKFLOWS = {
    WORKFLOW_LABEL_CANOPY: WorkflowDefinition(
        key=WORKFLOW_LABEL_CANOPY,
        label="Label Canopy",
        maturity=MATURITY_PRODUCTION_TARGET,
        source_script="prototypes/canopies_workflow/CanopyCrownLabeler.py",
        purpose="Create canopy crown polygons from CHM structure and species context.",
        can_write_data=True,
        readiness_note="Backend extraction is underway. Interactive map-tool wiring is next.",
    ),
    WORKFLOW_CREATE_TRAINING_SQUARE: WorkflowDefinition(
        key=WORKFLOW_CREATE_TRAINING_SQUARE,
        label="Create Training Square",
        maturity=MATURITY_PRODUCTION_TARGET,
        source_script="prototypes/canopies_workflow/NewTrainingSquare.py",
        purpose="Stamp and enrich training square geometry.",
        can_write_data=True,
        readiness_note="Workflow is tracked, but production migration has not started yet.",
    ),
    WORKFLOW_PROPOSE_CANOPIES: WorkflowDefinition(
        key=WORKFLOW_PROPOSE_CANOPIES,
        label="Propose Canopies In Square",
        maturity=MATURITY_EXPERIMENTAL,
        source_script="prototypes/canopies_workflow/PolygonsWithinSquare3.py",
        purpose="Generate reviewable canopy polygon proposals inside selected squares.",
        can_write_data=True,
        readiness_note="Experimental prototype. Needs QA metrics before production use.",
        experimental_warning="Review proposals before writing; this workflow is not production-ready.",
    ),
    WORKFLOW_DETECT_APEXES: WorkflowDefinition(
        key=WORKFLOW_DETECT_APEXES,
        label="Detect Apexes",
        maturity=MATURITY_EXPERIMENTAL,
        source_script="prototypes/canopies_workflow/ApexDetector.py",
        purpose="Detect reviewable apex candidate points inside selected squares.",
        can_write_data=True,
        readiness_note="Experimental prototype. Needs accuracy review before production use.",
        experimental_warning="Treat apex detections as assistive candidates until QA improves.",
    ),
    WORKFLOW_VALIDATE_PROJECT: WorkflowDefinition(
        key=WORKFLOW_VALIDATE_PROJECT,
        label="Validate Project",
        maturity=MATURITY_PRODUCTION_TARGET,
        source_script=None,
        purpose="Check selected layers, schema, and readiness before editing.",
        can_write_data=False,
        readiness_note="Available now.",
    ),
}


def get_workflow(key):
    """Return a workflow definition by key."""
    try:
        return WORKFLOWS[key]
    except KeyError as exc:
        raise ValueError(f"Unknown workflow: {key}") from exc


def list_workflows(include_experimental=True):
    """Return workflows in the intended UI order."""
    workflows = [
        WORKFLOWS[WORKFLOW_VALIDATE_PROJECT],
        WORKFLOWS[WORKFLOW_LABEL_CANOPY],
        WORKFLOWS[WORKFLOW_CREATE_TRAINING_SQUARE],
        WORKFLOWS[WORKFLOW_PROPOSE_CANOPIES],
        WORKFLOWS[WORKFLOW_DETECT_APEXES],
    ]
    if include_experimental:
        return workflows
    return [workflow for workflow in workflows if not workflow.is_experimental]


def workflow_requires_confirmation(workflow):
    """Return whether a workflow needs an extra confirmation before writes."""
    return workflow.is_experimental and workflow.can_write_data
