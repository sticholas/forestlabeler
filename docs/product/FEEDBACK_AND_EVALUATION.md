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
- Store immutable lifecycle events in the project-local
  `forest_labeler_feedback.sqlite3` database.
- Keep `forest_labeler_canopy_attempts.csv` as a readable compatibility export,
  not the source of truth.
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

## Learning Scopes

Forest Labeler uses a four-scope intelligence model:

1. **Project**: highest-trust evidence from the current project.
2. **User**: optional evidence from compatible projects owned by the current
   user.
3. **Team**: approved, compatible evidence shared by an organization.
4. **Universal**: a bundled baseline that gives first-time users useful default
   behavior.

Recommendation precedence is:

```text
project -> user -> team -> universal
```

Higher-trust evidence only overrides the universal baseline after minimum sample
and compatibility checks pass. Compatibility includes workflow, algorithm
version, ecosystem context, and CHM resolution where known.

The first production recommendation path uses durable project review events:

- Accept, Reject, Unsure, and Reject + Remove create lifecycle events.
- Project evidence is summarized by canopy mode and tightness.
- A project setting overrides the universal baseline after at least three
  reviewed attempts support that setting.
- The user sees the evidence scope, acceptance rate, and reviewed sample count
  before applying the recommendation.

Universal and team contributions must be explicit opt-in. Forest Labeler must
not silently upload project data, raw geometry, or personal paths. Shared
learning should prefer approved summaries over raw project records.

## Event Store Foundation

The event store links lifecycle events through a stable `attempt_id`:

```text
created -> accepted / rejected / unsure -> edited / removed
```

The initial SQLite schema contains:

- `schema_version`: controlled schema evolution.
- `attempts`: stable creation context and parameter settings.
- `events`: immutable lifecycle observations.

Deterministic event IDs distinguish immutable lifecycle transitions, while
latest-state checks suppress duplicate signals for the same transition. This
prevents duplicate observations from inflating future QA metrics without
discarding useful history.

The selected canopy target layer is observed for normal QGIS mutations. Plugin
buttons, Ctrl+Z quick reject, toolbar or attribute-table deletion, bulk
deletion, direct review-status edits, and deletion undo/restoration all update
the same attempt lifecycle. Recommendation evidence always uses the latest
meaningful state for each stable `attempt_id`.

Material geometry or provenance edits invalidate an earlier review and create
an `edited` lifecycle event. The crown returns to `unreviewed` until a person
reviews the changed result again. Non-material labeling metadata, such as
species and review notes, does not invalidate crown-shape evidence.

Geometry edits also refresh geometry-derived attributes before the lifecycle
event is persisted. `area_m2`, `radius_m`, and `diam_m` are recalculated from
the edited polygon so the layer attributes and event-store context do not drift
apart. Raster-derived metrics, including `apex_h`, require an explicit CHM-aware
recalculation workflow rather than an automatic geometry-only update.
