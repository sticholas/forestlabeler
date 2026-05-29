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
