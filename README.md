# Forest Labeler

Forest Labeler is a QGIS plugin for creating, reviewing, and improving forest
training data. The first production workflow focuses on CHM-assisted tree canopy
labeling: click or press-hold near a tree crown, preview the inferred canopy
polygon, and write clean training attributes into a target polygon layer.

The project is being built as a professional QGIS plugin, not a one-off script.
Core canopy logic lives in testable Python modules, QGIS-specific behavior lives
in adapter modules, and prototype scripts are preserved separately until their
behavior is migrated safely.

## Current Capabilities

- Validate selected QGIS layers before writes.
- Label canopy crowns from CHM structure using Dense, Mixed, or Sparse modes.
- Adjust canopy strength with a 0-100% slider while preserving the tested
  backend tightness scale.
- Write canopy metadata such as `fid`, `attempt_id`, `num_trees`, radius,
  diameter, area, apex height, mode, tightness, species, review status, CHM
  source, and ortho source when fields exist.
- Add missing canopy metadata fields to supported target layers.
- Review selected canopies as accepted, rejected, or unsure.
- Reject and remove selected canopies while logging the attempt for future
  learning and QA.
- Create configurable training polygons with preset or custom side lengths.
- Preserve experimental prototype tracks for future canopy proposals and apex
  detection.

## Install For QGIS

See [Install Guide](docs/INSTALL.md).

For local development on this machine, the fastest path is:

```bash
cd "/mnt/c/Users/Milo/Documents/Forest Labeler"
bash scripts/deploy-plugin.sh
```

Then restart QGIS or reload the plugin.

## Use The Plugin

See [User Guide](docs/USER_GUIDE.md).

The normal workflow is:

1. Open a QGIS project with a CHM raster and target polygon layer.
2. Open **Forest Labeler** from the QGIS plugin menu or toolbar.
3. Select **Label Canopy**.
4. Choose the CHM raster, target canopy polygon layer, and optional species
   point layer.
5. Click **Validate**.
6. Repair canopy metadata fields if needed.
7. Click **Start Label Canopy**.
8. Click or press-hold on a tree crown to create one canopy polygon.

## Repository Map

- `forest_labeler_core/`: QGIS-independent logic and tested algorithms.
- `forest_labeler_qgis/`: QGIS adapters for layers, geometry, raster sampling,
  map tools, schema repair, writing, and review.
- `forest_labeler_dockwidget.py`: QGIS dock coordination and UI wiring.
- `forest_labeler_dockwidget_base.ui`: Qt Designer UI layout.
- `prototypes/`: source scripts kept as migration references.
- `unit_tests/`: tests that run outside QGIS.
- `scripts/`: local check and deploy scripts.
- `docs/`: architecture, roadmap, QA, install, user, and release documents.

## Product Tracks

- **Track A: Label Canopy** - production priority.
- **Track B: Create Training Polygon** - useful secondary workflow.
- **Track C: Propose Canopies In Square** - experimental, review-first.
- **Track D: Detect Apexes** - experimental, assistive until QA improves.

See [Product Tracks](docs/PRODUCT_TRACKS.md) for details.

## Development

Run the standard local checks before committing:

```bash
bash scripts/checks.sh
```

Deploy the current working tree into the local QGIS plugin profile:

```bash
bash scripts/deploy-plugin.sh
```

QGIS-specific modules usually require QGIS' Python runtime. Pure logic in
`forest_labeler_core/` should remain testable with ordinary Python.

## Documentation

- [Install Guide](docs/INSTALL.md)
- [User Guide](docs/USER_GUIDE.md)
- [Release Process](docs/RELEASE_PROCESS.md)
- [Architecture](docs/ARCHITECTURE.md)
- [Development Workflow](docs/DEVELOPMENT.md)
- [Roadmap](docs/ROADMAP.md)
- [Quality Gates](docs/QUALITY_GATES.md)
- [Source Script Inventory](docs/SOURCE_SCRIPT_INVENTORY.md)
- [Product Tracks](docs/PRODUCT_TRACKS.md)
- [Decision Framework](docs/DECISION_FRAMEWORK.md)
- [Feedback And Evaluation](docs/FEEDBACK_AND_EVALUATION.md)
- [Canopy Learning Log](docs/CANOPY_LEARNING_LOG.md)
- [Future Capabilities](docs/FUTURE_CAPABILITIES.md)
- [Implementation Plan](docs/IMPLEMENTATION_PLAN.md)
- [Codex Prompt Scripts](docs/codex_prompts/README.md)
