# Feedback And Evaluation

Forest Labeler should become smarter through structured feedback, not hidden magic. The plugin should record how a canopy polygon was created, how the user judged it, and which settings produced good or bad results.

## Product Goal

Help users create better training data faster by learning which settings work well for different forest structures, imagery contexts, and user workflows.

## Feedback Loop

1. The plugin creates or proposes a polygon.
2. The plugin stores the settings used to create it:
   - workflow mode
   - canopy mode
   - crown tightness
   - seed radius
   - apex height
   - CHM source
   - ortho source
   - species decision status
3. The user marks the result:
   - good
   - acceptable after edit
   - bad
   - uncertain
4. The plugin stores optional correction notes:
   - too large
   - too small
   - wrong species
   - missed canopy
   - split/merge problem
   - bad CHM response
5. Future workflows summarize which settings are working best.

## Near-Term Implementation

Start simple and local:

- Add review fields to output layers where available.
- Add a small feedback panel for selected canopy features.
- Store feedback as attributes or a sidecar GeoPackage table.
- Summarize feedback by mode and tightness.
- Use `forest_labeler_core/feedback.py` for QGIS-independent feedback validation and summary rules.

Avoid automatic model training until the data is trustworthy and reviewable.

## Future Agent Testing

Future agents should run black-box checks that answer:

- Does the plugin load in QGIS?
- Do layer selectors populate?
- Does validation block unsafe setup?
- Can a known sample polygon be created?
- Are required attributes written?
- Are warnings understandable?
- Do experimental tools stay clearly labeled?

Agent tests should produce a short report with:

- branch/commit
- QGIS version
- project file
- actions performed
- pass/fail result
- screenshots or logs
- suspected regression area

## Learning Guardrails

The tool should not silently change behavior based on a few ratings. Use feedback first for reporting and recommendations:

- "Tightness 17 has produced more accepted crowns in this project."
- "Sparse mode has produced more edits/rejections in this area."
- "Multiple species conflicts are frequent in this layer."

Only promote automated tuning after enough reviewed examples exist and the recommendation can be explained.
