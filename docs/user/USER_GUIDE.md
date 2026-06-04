# User Guide

Forest Labeler helps build forest training data in QGIS. The plugin is organized
by workflow so users can choose the tool that matches the task in front of them.

## Validate Project

Use **Validate** before writing data.

Validation checks selected layers, geometry types, required fields, editable
state, and optional metadata fields. Forest Labeler should not write production
features until validation passes.

Warnings usually mean the tool can run, but some metadata will not be stored
until missing fields are added. When Forest Labeler detects missing metadata
fields on a valid writable target layer, it offers to add those fields
automatically after validation. Existing features are kept.

## Label Canopy

Use **Label Canopy** to create one canopy polygon for one tree.

1. Select **Label Canopy** from the workflow list.
2. Choose a CHM raster.
3. Choose the target canopy polygon layer.
4. Choose a species point layer if available.
5. Click **Validate**.
6. If validation offers to add missing Forest Labeler fields, choose **Yes** to
   let the plugin prepare the target layer schema.
7. Choose canopy mode:
   - `DENSE`: tighter behavior for closed canopy or crowded trees.
   - `MIXED`: balanced default.
   - `SPARSE`: broader behavior for open canopy or isolated trees.
8. Choose **Strength** with the slider:
   - `0%` is the loosest setting.
   - `50%` is the default balanced setting.
   - `100%` is the tightest setting.
9. Click **Start Label Canopy**.
10. Click or press-hold near the tree crown.

The backend still uses the tested `1..21` tightness scale. The UI shows this as
`0..100%` so the control is easier to understand.

## Canopy Review

Open **Review & QA** to mark selected canopy polygons:

- **Accept**: good canopy label.
- **Reject**: poor canopy label, kept in layer for inspection.
- **Unsure**: needs another look.
- **Reject + Remove**: logs the rejected attempt, then removes it from the clean
  target layer.

While **Label Canopy** is active, `Ctrl+Z` is a quick reject/remove shortcut for
the currently selected canopy. It writes the rejected attempt to the feedback
CSV before removing the feature. If no canopy is selected, Forest Labeler leaves
`Ctrl+Z` available for normal QGIS undo behavior.

Forest Labeler writes a project-local feedback CSV named:

```text
forest_labeler_canopy_attempts.csv
```

Forest Labeler also writes a durable project-local event database named:

```text
forest_labeler_feedback.sqlite3
```

The SQLite database is the source of truth for future QA summaries, learning,
and team review tooling. The CSV remains a readable compatibility export.

Key identity fields:

- `attempt_id`: stable Forest Labeler attempt ID.
- `canopy_fid`: the real `fid` attribute in the canopy layer.
- `qgis_feature_id`: QGIS internal feature ID, sometimes temporary or negative.
- `project_id`: stable project identity stored as a QGIS project variable.

Forest Labeler keeps reject/remove actions log-first. If a rejected attempt
cannot be written to the feedback CSV, the canopy feature is kept so the
training evidence is not lost silently.

## Create Training Polygon

Use **Training Polygon** to create configurable training areas.

1. Select a target polygon layer.
2. Choose a preset or custom settings.
3. Set side length, vertex count, angle, or custom side lengths.
4. Click **Start Training Polygon**.
5. Click the map to place the polygon.

Open **Advanced options** only when rotation or custom side lengths are needed.
Open **Review & QA** for review summaries, best reviewed pattern selection, and
selected-polygon review actions.

Keyboard shortcuts while the map tool is active:

- `Q`: rotate left.
- `E`: rotate right.
- `R`: reset angle.
- `Esc`: cancel the active tool.

## Experimental Workflows

The future workflows **Propose Canopies In Square** and **Detect Apexes** are
tracked as product directions but should remain preview/review-first until their
quality metrics are strong enough for production use.

Experimental output should not be treated as final training data without user
review.

## Practical Tips

- Keep the target layer editable while labeling.
- Validate before each major labeling session.
- Accept validation prompts to add Forest Labeler fields early so future review
  and learning data is preserved.
- Use `Reject + Remove` for bad generated crowns you do not want to keep.
- If canopy creation feels slow, use smaller press-hold radii and avoid
  unnecessarily high strength settings unless the tree needs it.
