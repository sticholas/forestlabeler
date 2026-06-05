# Architecture

Forest Labeler is organized around one rule: keep product logic testable and
keep QGIS side effects explicit.

## Current Package Boundaries

```text
forest_labeler.py                  QGIS plugin entrypoint and lifecycle
forest_labeler_dockwidget.py       Dock controller and UI coordination
forest_labeler_dockwidget_base.ui  Qt Designer layout

forest_labeler_core/               QGIS-independent product logic
forest_labeler_qgis/               QGIS adapters and side effects
prototypes/                        Original scripts kept as migration references
unit_tests/                        Pure Python tests
scripts/                           Local checks and QGIS deploy helpers
docs/                              Product, user, engineering, and release docs
```

## Core Layer

`forest_labeler_core/` contains logic that should run without QGIS imports:

- canopy parameter presets and strength/tightness mapping
- crown geometry and raster-analysis decisions
- attribute planning
- layer validation contracts
- species assignment decisions
- review summaries
- training polygon geometry rules
- feedback and learning-log record shapes
- workflow registry metadata
- write-safety preflight rules

This layer should be covered by ordinary Python unit tests.

## QGIS Adapter Layer

`forest_labeler_qgis/` contains the QGIS-specific boundary:

- map tools
- raster sampling through QGIS providers
- CRS transforms
- geometry conversion
- schema repair
- feature writing
- species layer queries
- review actions against selected features
- project-local feedback log writing
- versioned SQLite feedback-event persistence

This layer may call QGIS APIs directly, but it should avoid burying product
decisions inside UI callbacks.

## Dock Layer

`forest_labeler_dockwidget.py` coordinates the dock UI:

- populates layer selectors
- validates the selected workflow
- gathers user settings
- activates map tools
- shows user-facing status messages
- routes review and schema-repair actions

It should stay thin. New canopy, training polygon, review, or learning behavior
should usually start in `forest_labeler_core/` or `forest_labeler_qgis/`, not as
large button-handler code.

## Write Safety

Production writes should follow this path:

1. Validate selected workflow layers.
2. Build geometry through the workflow service or map tool.
3. Build an attribute plan in `forest_labeler_core/`.
4. Run write preflight checks.
5. Apply the QGIS feature write through `forest_labeler_qgis/feature_writer.py`.
6. Report success, warnings, or blocked action to the user.

Feature writes should be bounded, explainable, and reversible through normal
QGIS editing/undo behavior where practical.

## Workflow Model

Workflow metadata lives in `forest_labeler_core/workflows.py`. The UI should use
that registry to communicate:

- workflow label
- production or experimental maturity
- whether the workflow can write data
- readiness notes
- experimental warnings

Current tracks:

- **Label Canopy**: first production workflow.
- **Training Polygon**: secondary workflow, useful and still growing.
- **Propose Canopies In Square**: experimental, preview/review-first.
- **Detect Apexes**: experimental, assistive until QA improves.

## Prototype Migration Rule

Prototype scripts stay in `prototypes/` until their behavior is either:

- migrated into production modules,
- covered by tests or manual verification, or
- intentionally retired in an issue, PR, or commit.

Production code should not import prototype scripts directly.

## Feedback Loop

Forest Labeler records enough context to support future QA and learning:

- stable `attempt_id`
- project-level `project_id`
- real canopy-layer `fid` as `canopy_fid`
- QGIS internal feature ID only as debug context
- canopy mode, strength/tightness, radius, area, apex height, species, and review
  status

The project-local
`<project_name>_forest_labeler_files/forest_labeler_feedback.sqlite3` database
is the durable source of truth for lifecycle events. The CSV learning log is an
explicit readable export generated from SQLite when the user requests it. Pure
event identity, schema, and persistence behavior live in
`forest_labeler_core/feedback_event_store.py`; QGIS adapters determine
project-local paths and translate QGIS lifecycle activity into event records.
Read-only feedback inspection is allowed in the UI; mutation, cleanup, or
sandbox testing should be implemented as explicit service commands rather than
manual database edits.
Health checks are the gate before future agents or automated tuning consume
feedback evidence.
Recommendation confidence belongs in the review/inspection lane, not the
default labeling lane, unless a future product decision intentionally promotes
it into the primary workflow.
Feedback backups are stored under
`<project_name>_forest_labeler_files/backups/` and should be created before any
future destructive cleanup, migration, or sandbox experiment.
Recommendation lab analysis is read-only and belongs in the review/inspection
lane. It can rank evidence and guide review effort, but it must not write data
or change labeling settings without explicit user action.

Learning-scope policy lives in `forest_labeler_core/learning_scopes.py`. It
defines project, user, team, and universal evidence; compatibility rules;
minimum evidence requirements; recommendation precedence; and explicit sharing
permissions. This policy layer must remain independent from storage and UI so it
can be tested before recommendations affect user workflows.

See [Canopy Learning Log](../reference/CANOPY_LEARNING_LOG.md).
