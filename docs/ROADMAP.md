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

Functional check:

- GitHub branch and draft PR exist.
- Local project folder is the development workspace.
- QGIS plugin profile folder is treated as an install target only.

Needs more work if:

- The local workspace cannot push to GitHub.
- Source scripts are not preserved or traceable.
- A future contributor cannot tell which folder is canonical.

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

Functional check:

- Run Python syntax checks on edited modules.
- Parse the Qt `.ui` file.
- Deploy to the QGIS profile using `scripts/deploy-plugin.sh`.
- Open QGIS, load/reload Forest Labeler, and click `Validate`.

Needs more work if:

- QGIS cannot import the plugin.
- The dock opens but layer selectors are empty when matching layers are loaded.
- Validation passes with missing required layers or fields.
- Validation messages are unclear to a novice user.

## Phase 2: Core Canopy Engine Extraction

Goal: move prototype logic into maintainable modules.

- Identify reusable functions from `canopoly.py` and prototype scripts.
- Create config/preset objects for dense, sparse, and mixed canopy modes.
- Separate raster sampling, geometry creation, species lookup, and metadata filling.
- Add unit tests for pure helper functions.
- Keep `CanopyCrownLabeler.py` as the first production target.
- Keep `NewTrainingSquare.py` as the second production target.
- Track `PolygonsWithinSquare3.py` and `ApexDetector.py` as experimental until stronger QA exists.

Exit criteria:

- Core decisions are not trapped inside one large script.
- Settings are named, documented, and testable.

Functional check:

- Source-script behavior is mapped in `docs/SOURCE_SCRIPT_INVENTORY.md`.
- Crown presets and tightness settings are represented as explicit config objects.
- Pure helpers compile and have unit tests where QGIS is not required.
- QGIS-dependent adapters are isolated behind small interfaces.

Needs more work if:

- Production code imports reference scripts directly.
- Business rules remain hidden in global constants.
- Layer writes happen without validation or edit-session control.
- Dense, mixed, sparse, and tightness behavior cannot be explained from code or docs.
- The plugin UI does not make it clear which workflow mode the user is using.

## Phase 3: Interactive QGIS Tool

Goal: wire the canopy engine into actual map interaction.

- Implement a `QgsMapTool` for click-to-delineate.
- Show rubber-band preview during growth if practical.
- Write validated polygon features to the selected target layer.
- Handle no species, one species, and multiple species cases.

Exit criteria:

- User can create a canopy polygon from a click.
- Plugin reports exactly what was added or why it refused.

Functional check:

- Click-to-label works on a known QGIS project.
- No-species, one-species, and multiple-species cases are tested.
- CRS transformations are checked with layers in different CRS values.
- Bad geometry is blocked or repaired with a clear message.

Needs more work if:

- User can accidentally write to the wrong layer.
- Species conflicts produce silent blanks.
- A failed edit leaves partial features behind.

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

Functional check:

- Manual QA checklist is run on a known sample project.
- Edit rollback behavior is verified.
- Schema validation covers canopy, square, species, and apex workflows.
- Logs or message-bar output explain blocked actions.

Needs more work if:

- The plugin can change data without a clear success/failure report.
- There is no repeatable manual test project.
- Validation depends on tribal knowledge instead of code.

## Phase 5: Packaging and Release

Goal: make installation repeatable.

- Build a clean plugin zip from source.
- Exclude caches, prototypes, test junk, and local data from release zip.
- Add release checklist.
- Tag versions and update changelog.

Exit criteria:

- A reviewer can install the zip in QGIS and reproduce the release behavior.

Functional check:

- Release zip excludes prototypes, docs-only material, caches, and local data.
- Fresh QGIS profile installation succeeds.
- Version, changelog, and release notes agree.

Needs more work if:

- The release can only be reproduced from one machine.
- Generated files or local datasets leak into the plugin zip.
- The install instructions require guessing.
