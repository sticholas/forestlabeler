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

- `forest_labeler_core/training_square.py` starts the `NewTrainingSquare.py` migration with tested, QGIS-free training polygon parameter logic.
- The dock now shows workflow-specific controls so Label Canopy and Create Training Polygon no longer share one layer contract.
- Create Training Polygon now has a target polygon layer, side length, vertices, and angle controls; 4 vertices with 100 m sides preserves the original 100 m square use case.

Twenty-first migration slice:

- Training Polygon controls now treat nodes as polygon vertices/sides: 3 creates a triangle, 4 a square, 6 a hexagon, and higher counts create regular n-gons.
- Added `forest_labeler_qgis/training_shape_map_tool.py` so the workflow has an activation button, live preview, and click-to-stamp behavior.
- Segment length now means side length, so the default 4 vertices with 100 m segments creates the existing 100 m square behavior.

Twenty-second migration slice:

- Training Polygon map tool restores the original `Q` / `E` rotation shortcuts with 3 degree steps.
- Rotation updates the live preview and writes the current angle to the stamped feature when the target layer has an `angle` field.

Twenty-third migration slice:

- `forest_labeler_core/training_shape_attributes.py` adds tested metadata planning for stamped training polygons.
- Training Polygon writes optional `fid`, side length, vertex count, shape name, angle, area, and ortho source fields when present.
- `forest_labeler_qgis/training_shape_map_tool.py` now uses the shared feature-writing path instead of setting attributes directly.

Twenty-fourth migration slice:

- Training Polygon now supports exact custom side lengths for valid polygons, including rectangles such as `100, 20, 100, 20` and triangles with three differing side lengths.
- Blank custom side lengths preserve the simple equal-side workflow.
- The dock summarizes custom side lengths and reports validation errors before activation.

Twenty-fifth migration slice:

- The dock now has a product-style QSS layer with cleaner cards, compact controls, primary/secondary action buttons, and clearer status panels.
- Workflow controls were lightly renamed from activation language to start-language for a more end-user friendly feel.

Twenty-sixth migration slice:

- Training Polygon now uses a compact primary path by default and hides angle/custom side-length controls behind an Advanced options toggle.
- Validation details collapse unless warnings/errors are present, keeping the dock smaller during normal use.

Twenty-seventh migration slice:

- User-facing Track B language now says Training Polygon instead of Training Square/Shape.
- The canopy-only Layers section is hidden when Training Polygon is active, so the workflow panel only shows relevant controls.

Twenty-eighth migration slice:

- Training Polygon now includes reusable presets for common field layouts: 100 m square, 100 x 20 m rectangle, 25 m triangle, and 25 m hexagon.
- The map tool keeps `Q` / `E` rotation and adds `R` for exact angle entry during digitizing.
- Training Polygon validation now recommends a fuller metadata schema for side lengths, plot area, ortho source, and land-cover summaries.
- Stamped polygons can now populate optional `plot_area` from the project vegetation area layer and `Detailed_L*` land-cover summary fields from `CAH_LandCover` when those supporting layers are loaded.

Twenty-ninth migration slice:

- Training Polygon now has an `Add Metadata Fields` action that adds missing optional fields to the selected target layer after user confirmation.
- Training Polygon schema definitions now live in one typed field-spec list so validation, repair actions, and write behavior stay aligned.
- New Training Polygon features now default optional review metadata to `reviewed = 0` and `review_status = unreviewed` when those fields exist.

Thirtieth migration slice:

- Training Polygon now includes lightweight review actions for selected features: `Accept`, `Reject`, and `Unsure`.
- Review actions update `reviewed`, `review_status`, and optional `review_note` fields, creating the first in-tool feedback loop for later learning and quality reporting.
- Review updates require the target layer to be in edit mode, matching the safer write behavior used by polygon stamping.

Thirty-first migration slice:

- Training Polygon now has a `Review Summary` action that reports total, reviewed, unreviewed, accepted, rejected, and unsure counts for the selected layer.
- Review summary logic is covered by pure unit tests so future recommendation engines can build on stable acceptance-rate and attention-count calculations.
- The review summary uses both `review_status` and legacy `reviewed` flags, which keeps older or partially populated layers useful.

Thirty-second migration slice:

- Training Polygon review summaries now include pattern insights once a shape/side-length pattern has enough reviewed examples.
- Pattern insights identify the best-performing pattern by acceptance rate and the pattern that most needs attention by rejected/unsure count.
- The insight engine is pure and tested, which gives future adaptive recommendations a stable contract before any automated behavior is introduced.

Thirty-third migration slice:

- Training Polygon now has a `Use Best Reviewed Pattern` action that can apply the strongest reviewed shape/side-length pattern back into the digitizing controls.
- Recommendations require enough reviewed examples, ask for confirmation, and keep automated behavior user-controlled.
- The recommendation engine returns typed control settings, including vertex count, segment length, and custom side lengths, so future adaptive presets can reuse the same contract.

Thirty-fourth migration slice:

- Refocused feedback intelligence on the main Label Canopy workflow rather than the Training Polygon helper.
- Canopy features now optionally store the crown tightness that produced them, alongside mode, radius, refinement, and review fields.
- Label Canopy now has schema repair, review actions, review summary, quality insights, and `Use Best Canopy Tool` controls.
- Canopy quality insights group reviewed crowns by mode and tightness so we can evaluate which press-hold settings are producing the best tree crowns.

Thirty-fifth migration slice:

- Label Canopy now auto-populates optional `num_trees` metadata with `1`, matching the one-tree-per-press-hold labeling workflow.
- Canopy schema repair and validation now include `num_trees` as a recommended field.

Thirty-sixth migration slice:

- Label Canopy now has QA selection controls for `Select Unreviewed` and `Select Attention`.
- `Select Attention` finds canopies marked rejected or unsure, making manual press-hold verification faster.
- Selection helpers do not require edit mode because they only update the active feature selection.

Thirty-seventh migration slice:

- Label Canopy now records optional source provenance for generated crowns through `chm_id` and `ortho_id`.
- The CHM source comes from the selected CHM raster, and the ortho source is inferred from the visible project raster covering the clicked point.
- Canopy schema repair and validation now include `chm_id` as recommended metadata.
