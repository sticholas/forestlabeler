# Forest Labeler

Forest Labeler is a QGIS plugin for building forest training data from canopy
height models, imagery, and reviewable user decisions.

The current production focus is simple: help a GIS user create one clean canopy
polygon for one tree, store useful metadata, and preserve enough feedback to
make the workflow smarter over time.

## What It Does Today

- Validates selected QGIS layers before writing data.
- Creates CHM-assisted canopy crown polygons from click or press-hold input.
- Supports Dense, Mixed, and Sparse canopy modes.
- Shows canopy strength as a 0-100% slider while keeping the tested backend
  tightness model.
- Writes canopy metadata when fields exist, including `fid`, `attempt_id`,
  `num_trees`, radius, area, apex height, mode, tightness, species, review
  status, CHM source, and ortho source.
- Adds missing canopy metadata fields to supported layers.
- Reviews selected canopies as accepted, rejected, or unsure.
- Logs rejected/removed canopy attempts for future QA and learning.
- Creates configurable training polygons as a secondary workflow.

## Quick Start

1. Clone the repository.
2. Follow the [Install Guide](docs/user/INSTALL.md).
3. Open the [User Guide](docs/user/USER_GUIDE.md).
4. Restart QGIS or reload the plugin after installation.

## First Canopy Workflow

1. Open a QGIS project with a CHM raster and target canopy polygon layer.
2. Open **Forest Labeler**.
3. Select **Label Canopy**.
4. Choose the CHM, target polygon layer, and optional species point layer.
5. Click **Validate**.
6. Add canopy metadata fields if the plugin recommends it.
7. Click **Start Label Canopy**.
8. Click or press-hold near a tree crown.

## Repository Structure

```text
forest_labeler_core/       Testable canopy, geometry, review, and workflow logic
forest_labeler_qgis/       QGIS adapters for map tools, layers, rasters, and writes
forest_labeler.py          QGIS plugin entrypoint
forest_labeler_dockwidget.py
forest_labeler_dockwidget_base.ui
prototypes/                Original scripts kept as migration references
scripts/                   Local checks and QGIS deploy helpers
unit_tests/                QGIS-independent test suite
docs/                      User, product, engineering, release, and reference docs
```

## Documentation

Start here: [Documentation Home](docs/README.md)

Key pages:

- [Install Guide](docs/user/INSTALL.md)
- [User Guide](docs/user/USER_GUIDE.md)
- [Architecture](docs/development/ARCHITECTURE.md)
- [Development Workflow](docs/development/DEVELOPMENT.md)
- [Product Roadmap](docs/product/ROADMAP.md)
- [Release Process](docs/operations/RELEASE_PROCESS.md)

## Development Checks

Run before committing:

```bash
bash scripts/checks.sh
```

Deploy into the local QGIS profile:

```bash
bash scripts/deploy-plugin.sh
```

## Project Status

Forest Labeler is in active product development. Track A, **Label Canopy**, is
the first production workflow. Track B, **Training Polygon**, is useful but still
growing. Canopy proposal and apex detection workflows remain experimental until
their QA metrics are stronger.
