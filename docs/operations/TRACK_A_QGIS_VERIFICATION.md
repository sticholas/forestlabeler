# Track A QGIS Verification: Label Canopy

Use this checklist to decide whether Track A is ready to close as the first production workflow. Record one report per meaningful QGIS test pass.

## Test Context

- Date:
- Tester:
- QGIS version:
- Forest Labeler commit:
- Branch:
- Project file:
- Plugin install method:
- CHM layer:
- Target canopy layer:
- Species point layer:
- Ortho imagery layer(s):
- Notes/screenshots:

## Preflight

| Check | Expected Result | Status | Notes |
| --- | --- | --- | --- |
| Plugin loads without traceback | Forest Labeler toolbar/menu action is available | Not run |  |
| Dock opens | Dock displays workflow selector and current controls | Not run |  |
| Label Canopy workflow selected | Canopy layer controls are visible; Training Polygon controls are hidden | Not run |  |
| Refresh loads project layers | CHM, target polygons, and species point controls populate | Not run |  |
| Validate blocks missing setup | Missing/wrong layers produce clear errors and no edit tool starts | Not run |  |
| Validate passes good setup | Valid CHM, target canopy layer, and optional species layer pass | Not run |  |
| Target layer edit mode required | Start/use write path refuses writes when target layer is not editable | Not run |  |

## Canopy Creation

Test at least three crowns per mode/tightness combination you care about.

| Scenario | Expected Result | Status | Notes |
| --- | --- | --- | --- |
| Mixed, tightness 11, click | Crown preview appears and one canopy feature is written on release | Not run |  |
| Mixed, tightness 11, press-hold | Seed radius grows while held; final crown refines on release | Not run |  |
| Dense mode | Crown is tighter and appropriate for dense canopy structure | Not run |  |
| Sparse mode | Crown is looser/appropriate for sparse canopy structure | Not run |  |
| Low tightness | Crown behavior is visibly looser than high tightness | Not run |  |
| High tightness | Crown behavior is visibly tighter than low tightness | Not run |  |
| No valid crown | User gets clear failure; no empty feature is written | Not run |  |

## Attribute Verification

After creating a canopy, inspect the target layer attribute table.

| Field | Expected Value | Status | Notes |
| --- | --- | --- | --- |
| `fid` | Next numeric feature id when field exists | Not run |  |
| `radius_m` | Seed/press-hold radius in meters | Not run |  |
| `diam_m` | `radius_m * 2` | Not run |  |
| `area_m2` | Polygon area in target CRS units | Not run |  |
| `apex_h` | CHM apex height when refined | Not run |  |
| `mode` | Selected canopy mode | Not run |  |
| `tightness` | Selected crown tightness | Not run |  |
| `num_trees` | `1` | Not run |  |
| `species` | Species code when exactly one matching point exists | Not run |  |
| `reviewed` | `0` by default | Not run |  |
| `review_status` | `unreviewed` by default | Not run |  |
| `refined` | `1` when CHM refinement succeeded, otherwise `0` | Not run |  |
| `chm_id` | Selected CHM raster source | Not run |  |
| `ortho_id` | Local ortho raster covering the clicked canopy, if detected | Not run |  |

## Species Decisions

| Scenario | Expected Result | Status | Notes |
| --- | --- | --- | --- |
| One species point inside canopy | Feature writes species code | Not run |  |
| No species point inside canopy | Feature writes with blank species or configured warning | Not run |  |
| Multiple species points inside canopy | Write is blocked with clear species conflict message | Not run |  |
| Species layer omitted | Feature writes without species lookup | Not run |  |

## Review And QA Loop

| Action | Expected Result | Status | Notes |
| --- | --- | --- | --- |
| Validation schema repair | Missing optional fields are added after confirmation; existing fields such as `attempt_id` are skipped without duplicate-column failure | Not run |  |
| Accept selected canopy | `reviewed = 1`, `review_status = accepted` | Not run |  |
| Reject selected canopy | `reviewed = -1`, `review_status = rejected` | Not run |  |
| Unsure selected canopy | `reviewed = 0`, `review_status = unsure` | Not run |  |
| Reject + Remove selected canopy | Attempt is logged to `forest_labeler_tool_files/forest_labeler_feedback.sqlite3` and feature is removed from target layer | Not run |  |
| `Ctrl+Z` quick reject while Label Canopy is active | Selected canopy attempt is logged to `forest_labeler_tool_files/forest_labeler_feedback.sqlite3` with quick-reject note and feature is removed from target layer | Not run |  |
| `Ctrl+Z` with no selected canopy | Normal QGIS undo behavior remains available | Not run |  |
| Review note | `review_note` stores typed note when field exists | Not run |  |
| Canopy Review Summary | Counts total, reviewed, unreviewed, accepted, rejected, unsure | Not run |  |
| Export CSV | User confirms export; `forest_labeler_tool_files/forest_labeler_canopy_attempts.csv` is written next to the QGIS project | Not run |  |
| Select Unreviewed | Selects only canopies with unreviewed status | Not run |  |
| Select Attention | Selects rejected and unsure canopies | Not run |  |
| Use Best Canopy Tool | Applies best reviewed mode/tightness after enough reviewed examples | Not run |  |

## Pass/Fail Summary

- Overall result: Not run
- Blocking issues:
- Non-blocking follow-up:
- Recommended next ticket:
- Screenshots/logs attached:
