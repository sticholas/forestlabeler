# Roadmap

## Phase 0: Inventory and Foundation

Goal: make the project understandable and recoverable.

- Copy installed plugin scaffold into the working repo.
- Preserve prototype scripts under `prototypes/`.
- Add README, architecture notes, development workflow, issue templates, and quality gates.
- Confirm how the GitHub repo and local folder will be synchronized.
- Confirm Git is installed and available in Warp/PyCharm.

Exit criteria:

- New contributor can open the repo and understand the project shape.
- Installed plugin baseline is recoverable from source.

## Phase 1: Plugin Skeleton Hardening

Goal: make the existing plugin load reliably and expose a useful UI shell.

- Rename classes/modules to consistent Python style where safe.
- Add plugin versioning discipline through `metadata.txt`.
- Add a dock widget with layer selectors and status output.
- Add startup validation for required QGIS APIs.
- Add clear message-bar errors for missing layers or fields.

Exit criteria:

- Plugin loads in QGIS.
- User can select layers and see validation status.
- No canopy edits happen until validation passes.

## Phase 2: Core Canopy Engine Extraction

Goal: move prototype logic into maintainable modules.

- Identify reusable functions from `canopoly.py` and prototype scripts.
- Create config/preset objects for dense, sparse, and mixed canopy modes.
- Separate raster sampling, geometry creation, species lookup, and metadata filling.
- Add unit tests for pure helper functions.

Exit criteria:

- Core decisions are not trapped inside one large script.
- Settings are named, documented, and testable.

## Phase 3: Interactive QGIS Tool

Goal: wire the canopy engine into actual map interaction.

- Implement a `QgsMapTool` for click-to-delineate.
- Show rubber-band preview during growth if practical.
- Write validated polygon features to the selected target layer.
- Handle no species, one species, and multiple species cases.

Exit criteria:

- User can create a canopy polygon from a click.
- Plugin reports exactly what was added or why it refused.

## Phase 4: Data Safety and QA

Goal: prevent accidental bad edits.

- Add field schema checks.
- Add CRS transformation checks.
- Add edit-session handling and rollback behavior.
- Add geometry validity checks and cleanup.
- Add manual QA checklist with sample project.

Exit criteria:

- Bad project setup is blocked before edits.
- Geometry and species assignment edge cases are explicit.

## Phase 5: Packaging and Release

Goal: make installation repeatable.

- Build a clean plugin zip from source.
- Exclude caches, prototypes, test junk, and local data from release zip.
- Add release checklist.
- Tag versions and update changelog.

Exit criteria:

- A reviewer can install the zip in QGIS and reproduce the release behavior.
