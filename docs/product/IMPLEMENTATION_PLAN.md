# Implementation Plan

This plan turns the current QGIS console scripts into a stable, extensible Forest Labeler plugin. The goal is not only to reproduce the scripts, but to make the plugin safer, easier to use, easier to test, and able to improve from user feedback over time.

## North Star

Forest Labeler should help users create and review high-quality forest training data faster. It should support multiple workflow modes, make parameters understandable, prevent unsafe writes, and collect feedback that can later guide recommendations and automated QA.

## Current Source Scripts

| Track | Source script | Maturity | Product role |
| --- | --- | --- | --- |
| A | `CanopyCrownLabeler.py` | Strongest | First production canopy labeling tool |
| B | `NewTrainingSquare.py` | Strong | Second production workflow |
| C | `PolygonsWithinSquare3.py` | Mid-level | Experimental proposal workflow |
| D | `ApexDetector.py` | Mid-level | Experimental assistive workflow |

## Execution Phases

### Phase 1: Plugin Shell And Validation

Status: underway in PR #7 and expanded in PR #8.

Objective:

- Make the plugin load reliably.
- Give users layer selectors and clear validation.
- Establish workflow mode selection.
- Keep production and experimental workflows visibly separate.

Implementation:

- Dock UI with workflow selector.
- Layer selectors for CHM, target polygons, and species points.
- Project validation before editing.
- Workflow registry from `forest_labeler_core/workflows.py`.

Testing:

- QGIS manual load test.
- Dropdown population test.
- Validation pass/fail test.
- `bash scripts/checks.sh`.

Exit gate:

- Plugin opens in QGIS without traceback.
- Validation runs without traceback.
- Workflow selector displays maturity and readiness.
- Experimental modes show warnings.

### Phase 2: Track A Backend Extraction

Status: active in PR #8.

Objective:

- Extract `CanopyCrownLabeler.py` into testable backend modules and thin QGIS adapters.
- Avoid wiring raw console-script behavior directly into UI buttons.

Implemented foundation:

- `forest_labeler_core/canopy_presets.py`
- `forest_labeler_core/numeric.py`
- `forest_labeler_core/raster_sources.py`
- `forest_labeler_core/canopy_attributes.py`
- `forest_labeler_core/species.py`
- `forest_labeler_core/feedback.py`
- `forest_labeler_qgis/feature_writer.py`
- `forest_labeler_qgis/species_lookup.py`
- `forest_labeler_qgis/canopy_service.py`

Next implementation steps:

1. Extract geometry profile helpers from `CanopyCrownLabeler.py`.
2. Add QGIS raster sampling adapter.
3. Add local apex search adapter.
4. Add crown radius inference service.
5. Add geometry creation and cleanup adapter.
6. Wire `canopy_service.py` into a non-destructive preview path.
7. Wire controlled feature writes after manual QA passes.

Testing:

- Unit tests for pure helpers.
- Adapter syntax checks.
- QGIS manual tests for sample project.
- Known-click test cases once a repeatable project fixture is chosen.

Exit gate:

- Canopy parameters are controlled from UI.
- User can create a canopy polygon through the plugin.
- Species conflicts block or warn as configured.
- Feature writes use the controlled writer only.
- Manual QGIS verification is recorded using `docs/operations/TRACK_A_QGIS_VERIFICATION.md`.

### Phase 3: Track A User Controls And Productivity

Objective:

- Make canopy labeling ergonomic and parameter-driven.
- Give users visible control over mode, tightness, species behavior, and feedback.

Parameter controls:

- Canopy mode: `DENSE`, `MIXED`, `SPARSE`.
- Crown tightness: 1 to 21.
- Block multiple species points: toggle.
- Warn if no species point: toggle.
- Optional metadata behavior: show missing fields clearly.
- Future: profile/smoothing advanced settings behind an expert panel.

Implementation:

- Add mode/tightness controls to the dock.
- Show current parameter summary.
- Add "Start Label Canopy" action.
- Add preview-first behavior.
- Add success/warning/error report after each write.

Testing:

- UI state tests by manual QGIS check.
- Unit tests for parameter object creation.
- Manual tests across dense/mixed/sparse and loose/tight settings.

Exit gate:

- User can change parameters without editing code.
- Plugin reports which settings produced each polygon.
- Created features store mode/tightness where fields exist.

### Phase 4: Feedback And Learning Foundation

Objective:

- Let users say whether created polygons were good, acceptable after edit, bad, or uncertain.
- Store enough context to learn which settings work.

Implementation:

- Add feedback panel for selected canopy feature.
- Store feedback in target attributes if fields exist, or a sidecar GeoPackage table.
- Track correction reasons:
  - too large
  - too small
  - wrong species
  - missed canopy
  - split/merge issue
  - bad CHM response
- Summarize feedback by workflow, canopy mode, and crown tightness.

Testing:

- Unit tests for feedback summaries.
- Manual tests for feedback entry and persistence.
- QA report generation test.

Learning guardrails:

- Feedback first powers reporting and recommendations.
- No silent automatic tuning.
- Recommendation requires minimum reviewed samples.

Exit gate:

- User can rate a polygon.
- Feedback persists.
- Plugin can summarize settings that are working well or poorly.

### Phase 5: Track B Training Square Workflow

Objective:

- Migrate `NewTrainingSquare.py` as the second production workflow.

Parameter controls:

- Square size, default 100 m.
- Rotation controls.
- Supporting layers for vegetation and land cover.
- Attribute fill report.

Implementation:

- Extract square geometry helpers.
- Add square layer validation.
- Add preview and stamp tool.
- Add controlled write path.
- Add metadata report after each square.

Testing:

- Unit tests for square geometry.
- Manual QGIS placement tests.
- Attribute enrichment tests with known layers.

Exit gate:

- User can preview, rotate, and stamp a training square.
- Plugin reports what attributes were filled and what was missing.

### Phase 6: Experimental Tracks C And D

Objective:

- Keep canopy proposals and apex detection useful but clearly experimental until QA improves.

Track C: `PolygonsWithinSquare3.py`

- Add proposal preview mode.
- Require confirmation before writing.
- Track false positives and false negatives.
- Add proposal confidence metadata.

Track D: `ApexDetector.py`

- Add apex candidate preview.
- Preserve manual apexes by default.
- Add quality and review flags.
- Require confirmation before clearing or replacing outputs.

Testing:

- Known-square benchmark tests.
- Manual review metrics.
- QA summary by sample area.

Exit gate:

- Experimental label remains visible.
- No batch writes happen without confirmation.
- Outputs are reviewable and traceable.

### Phase 7: Black-Box Agent Testing

Objective:

- Add automated and semi-automated checks that test the plugin like a user would.

Agent test targets:

- QGIS starts and plugin loads.
- Dock opens.
- Workflow selector populates.
- Project validation passes/fails correctly.
- Known sample feature can be created.
- Attributes are written as expected.
- Experimental modes show warnings.
- Feedback can be recorded.

Report contents:

- branch/commit
- QGIS version
- project file
- actions performed
- pass/fail result
- screenshots/logs
- suspected regression area

Exit gate:

- A repeatable black-box check can be run before major merges or releases.

## Parameter Strategy

Parameters should move from hidden script constants to explicit configuration:

- Basic controls visible by default.
- Advanced controls hidden until needed.
- Each created feature should record the parameters used when schema allows.
- Recommended settings should come from feedback summaries, not silent auto-tuning.

## Testing Strategy

| Layer | Purpose | Tooling |
| --- | --- | --- |
| Unit tests | Pure logic and decision rules | `unit_tests/` |
| Syntax checks | Import/syntax confidence | `scripts/checks.sh` |
| QGIS manual checks | Plugin load and UI behavior | Known project |
| Adapter checks | QGIS layer/raster/write behavior | QGIS runtime |
| Black-box checks | End-to-end user workflows | Future agent scripts |

Standard local command:

```bash
bash scripts/checks.sh
```

## Decision Rule For New Features

Every new feature must answer:

- What user workflow does this improve?
- Is it production-target or experimental?
- What data can it write?
- What validation blocks unsafe use?
- What tests or manual checks prove it works?
- What feedback can the user provide after using it?

## Immediate Next Work

1. Continue Track A geometry/raster extraction from `CanopyCrownLabeler.py`.
2. Add UI controls for canopy mode and crown tightness.
3. Wire preview-only canopy creation before writes.
4. Add feedback schema design.
5. Define the first known QGIS manual test project and checklist.
