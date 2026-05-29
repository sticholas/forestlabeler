# Forest Labeler

Forest Labeler is a QGIS plugin for delineating tree canopy polygons from canopy height model data and carrying useful labeling metadata into a target training layer.

The repository currently contains:

- a QGIS Plugin Builder scaffold copied from the installed local plugin
- existing prototype scripts under `prototypes/`
- project documentation under `docs/`

## Current Status

This project is in foundation phase. The installed plugin opens in QGIS, but the production workflow still needs to be wired into the plugin UI and structured into testable modules.

## Local Development

1. Open this folder in PyCharm:
   `C:\Users\Milo\Documents\Forest Labeler`
2. Use QGIS for runtime testing. QGIS plugin Python code depends on QGIS' bundled Python environment, so ordinary system Python will not import `qgis.*`.
3. Keep prototype scripts in `prototypes/` until each behavior is moved into a proper plugin module with tests and documentation.
4. Use small commits that tell the story of the work: scaffold, core extraction, UI wiring, validation, packaging.

## Documentation

- [Architecture](docs/ARCHITECTURE.md)
- [Development Workflow](docs/DEVELOPMENT.md)
- [Roadmap](docs/ROADMAP.md)
- [Quality Gates](docs/QUALITY_GATES.md)
- [Source Script Inventory](docs/SOURCE_SCRIPT_INVENTORY.md)
- [Product Tracks](docs/PRODUCT_TRACKS.md)
