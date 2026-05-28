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
