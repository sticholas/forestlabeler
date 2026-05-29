# Source Script Inventory

This inventory captures the working QGIS console scripts that informed Forest Labeler. These files are preserved as reference material under `prototypes/canopies_workflow/` and should be migrated into production modules deliberately, one behavior at a time.

## Source Location

Original working folder:

```text
X:\PROJECTS_2\Big_Island\ChangeHI_Trees\Dry_Forest\Data\Vector\Training\TrainingData\Canopies\Scripts
```

Local reference copy:

```text
prototypes/canopies_workflow/
```

## Workflow Scripts

Current maturity:

- `CanopyCrownLabeler.py`: strongest current canopy workflow and first production priority.
- `NewTrainingSquare.py`: strong working square workflow and second production priority.
- `PolygonsWithinSquare3.py`: mid-level prototype; useful but needs more QA before production.
- `ApexDetector.py`: mid-level prototype; should stay experimental until quality metrics improve.

### `NewTrainingSquare.py`

Creates 100 m training squares and enriches them from supporting vegetation and land-cover layers.

Required project layers:

- `BigIsland_CustomVegetationAreas` / `BigIsland_CustomVegitationAreas - Areas`
- `CAH_LandCover`
- `training_squares*`, in edit mode

Production migration target:

- training-square map tool
- square metadata service
- layer schema validation for square outputs

### `CanopyTypeLabeler2.py`

Interactive canopy labeling tool with `DENSE`, `MIXED`, and `SPARSE` modes. It writes canopy attributes such as square id, apex height, area, mode, ortho source, and species.

Required project layers:

- `chm`
- `training_canopies*`, in edit mode

Production migration target:

- canopy label map tool
- canopy preset configuration
- canopy attribute writer

### `CanopyCrownLabeler.py`

Interactive canopy crown labeling tool with expanded crown tightness controls from 1 to 21. This appears to be the strongest candidate for the main Forest Labeler canopy engine.

Required project layers:

- `chm`
- `training_canopies*`, in edit mode
- optional species point layer for species lookup

Production migration target:

- canopy engine configuration
- crown tightness control
- species lookup and conflict handling
- geometry safety checks

### `PolygonsWithinSquare3.py`

Generates or filters canopy polygons within training squares using CHM-driven candidate detection and canopy-mode presets.

Required project layers:

- `training_squares*`
- `training_canopies*`
- `chm`

Production migration target:

- batch canopy proposal workflow
- square/canopy relationship checks
- batch processing safety limits

### `ApexDetector.py`

Detects apex candidates within selected training squares and writes them to `training_apexes`.

Required project layers:

- `training_squares*`
- `training_apexes`, in edit mode
- `chm`

Production migration target:

- apex detection service
- apex output writer
- dense/mixed/sparse apex presets

## Migration Rules

- Reference scripts stay untouched unless they are being refreshed from the working source folder.
- Production code should not import these scripts directly.
- Each migrated behavior needs a small ticket, verification notes, and either unit tests or QGIS manual checks.
- Direct layer edits must move behind validation and edit-session handling before becoming production behavior.
- Any source-script assumptions about exact layer names, field names, or edit mode must become explicit configuration or validation.

## Current Best Candidate For Phase 2

Start with `CanopyCrownLabeler.py`, because it contains the most complete crown workflow and the crown tightness range that should become user-facing plugin configuration.

First migration slice:

- `forest_labeler_core/canopy_presets.py` extracts dense, sparse, mixed, and crown-tightness settings into a QGIS-independent module.
- `unit_tests/test_canopy_presets.py` covers mode normalization, tightness clamping, dense-end behavior, and loose-end behavior.

Second migration slice:

- `forest_labeler_core/numeric.py` extracts median, Gaussian kernel, circular Gaussian smoothing, and circular moving average helpers.
- `unit_tests/test_numeric.py` covers edge wrapping, normalization, invalid parameters, empty inputs, and zero-pass behavior.

Third migration slice:

- `forest_labeler_core/raster_sources.py` extracts probable-ortho source classification without QGIS imports.
- `unit_tests/test_raster_sources.py` covers local ortho acceptance, CHM/landcover exclusion, web/tile rejection, provider filtering, and extension filtering.

Fourth migration slice:

- `forest_labeler_core/canopy_attributes.py` extracts canopy feature attribute planning before QGIS writes occur.
- `forest_labeler_core/species.py` extracts species assignment decisions before geometry/layer adapters are wired.
- `unit_tests/test_canopy_attributes.py` and `unit_tests/test_species.py` cover metadata planning, fid selection, missing species, single species, and multiple-species blocking behavior.

Fifth migration slice:

- `forest_labeler_qgis/feature_writer.py` adds the first controlled QGIS adapter for applying canopy feature writes.
- The adapter consumes pure core plans and returns structured success, warning, and error results instead of writing silently from a map tool.

Sixth migration slice:

- `forest_labeler_qgis/species_lookup.py` adds a QGIS adapter that finds species point matches inside canopy polygons.
- The adapter delegates assignment, warning, and block decisions to `forest_labeler_core/species.py`.

Seventh migration slice:

- `forest_labeler_qgis/canopy_service.py` coordinates species lookup and controlled feature writing behind one Track A service call.
- Future map tools should call the service instead of repeating species lookup and direct `QgsFeature` writes.

Eighth migration slice:

- `forest_labeler_core/feedback.py` adds QGIS-independent feedback validation and summary rules.
- `unit_tests/test_feedback.py` covers feedback validation, setting-level summaries, minimum sample requirements, and invalid feedback rejection.

Ninth migration slice:

- `forest_labeler_core/workflows.py` turns product tracks into code-level workflow metadata.
- `unit_tests/test_workflows.py` covers production priorities, experimental filtering, unknown workflows, and confirmation requirements.

Tenth migration slice:

- The dock workflow selector now reads from `forest_labeler_core/workflows.py`.
- Users can see workflow maturity, write behavior, and experimental warnings before individual tools are wired in.

Eleventh migration slice:

- `forest_labeler_core/geometry_math.py` extracts planar distance, circle point generation, radial point generation, derivatives, and simple line smoothing.
- `unit_tests/test_geometry_math.py` covers closed rings, input validation, derivatives, and smoothing behavior.

Twelfth migration slice:

- `forest_labeler_qgis/geometry_adapter.py` converts tested point-generation helpers into QGIS polygon geometries.
- Runtime behavior should be manually verified once the adapter is wired into preview and write workflows.

Thirteenth migration slice:

- `forest_labeler_core/raster_analysis.py` extracts QGIS-independent profile sampling, circular area sampling, local apex search, and inner support threshold calculation.
- `forest_labeler_qgis/raster_adapter.py` wraps QGIS raster provider sampling behind a callable sampler.
- `unit_tests/test_raster_analysis.py` covers profile stop behavior, circular sampling, local apex search, missing samples, and threshold selection.

Fourteenth migration slice:

- `forest_labeler_core/crown_inference.py` extracts ownership scoring, competitor penalty, one-profile radius inference, and multi-angle crown radius inference.
- `unit_tests/test_crown_inference.py` covers ownership, competitor pressure, short profiles, edge-radius inference, and configured angle counts.

Fifteenth migration slice:

- `forest_labeler_core/crown_builder.py` composes local apex search, thresholding, crown radius inference, smoothing, and point generation into a preview-safe crown build result.
- The builder returns polygon points and metadata without creating QGIS geometry or writing features.
- `unit_tests/test_crown_builder.py` covers circle fallback and refined crown point generation.

Sixteenth migration slice:

- `forest_labeler_core/raster_analysis.py` extracts competing-apex discovery from `CanopyCrownLabeler.py`.
- `forest_labeler_core/crown_builder.py` now passes nearby apex candidates into crown-radius inference so preview crowns can respect neighboring canopy peaks.
- Unit coverage checks competing-apex height filtering, minimum spacing, target-apex preservation, and constrained crown growth near a neighboring peak.

Seventeenth migration slice:

- `forest_labeler_qgis/crown_preview_service.py` adds the first QGIS adapter bridge from CHM sampling to preview crown geometry.
- The adapter keeps parameter selection, raster sampling, QGIS polygon creation, and CRS transformation outside the pure crown builder so core inference remains unit-testable.
- Runtime behavior still needs manual QGIS verification when the interactive map tool is wired.

Eighteenth migration slice:

- `forest_labeler_qgis/canopy_map_tool.py` adds the first interactive Label Canopy map tool.
- The dock now exposes canopy mode, crown tightness, and an activation control that validates layers before enabling the map tool.
- The map tool previews generated crown geometry while the user clicks or press-holds, then writes accepted geometry through `forest_labeler_qgis/canopy_service.py`.

Nineteenth migration slice:

- Press-hold interaction now shows a stable seed-radius circle during sizing.
- Crown inference runs once on release, allowing the final polygon to snap/refine to the local canopy apex without jittering while the user is holding the mouse.

Twentieth migration slice:

- `forest_labeler_core/training_square.py` starts the `NewTrainingSquare.py` migration with tested, QGIS-free training shape parameter logic.
- The dock now shows workflow-specific controls so Label Canopy and Create Training Square no longer share one layer contract.
- Create Training Square now has a target square layer, segment length, nodes per side, and angle controls; 10 m segments with 11 nodes preserves the existing 100 m default.

Twenty-first migration slice:

- Training Square controls now treat nodes as polygon vertices/sides: 3 creates a triangle, 4 a square, 6 a hexagon, and higher counts create regular n-gons.
- Added `forest_labeler_qgis/training_shape_map_tool.py` so the workflow has an activation button, live preview, and click-to-stamp behavior.
- Segment length now means side length, so the default 4 vertices with 100 m segments creates the existing 100 m square behavior.

Twenty-second migration slice:

- Training Shape map tool restores the original `Q` / `E` rotation shortcuts with 3 degree steps.
- Rotation updates the live preview and writes the current angle to the stamped feature when the target layer has an `angle` field.
