# Product Tracks

Forest Labeler is a QGIS training-data toolkit, not a single-purpose button. The plugin should expose separate capabilities depending on what the user is trying to do in the moment.

## Track A: Canopy Crown Labeling

Current source script:

```text
prototypes/canopies_workflow/CanopyCrownLabeler.py
```

Current maturity:

```text
Strongest current workflow. Closest to the intended plugin experience.
```

Purpose:

- Click or press-hold near a canopy apex.
- Infer a canopy crown polygon from CHM structure.
- Fill canopy metadata where schema supports it.
- Use species points to assign or warn about species labels.

Near-term product direction:

- Make this the first production interactive map tool.
- Keep dense, mixed, sparse, and crown tightness as user-facing controls.
- Add better validation, undo/rollback handling, and clear warnings.
- Make species conflicts explicit and reviewable.

## Track B: Training Square Creation

Current source script:

```text
prototypes/canopies_workflow/NewTrainingSquare.py
```

Current maturity:

```text
Working well and valuable, but expected to grow.
```

Purpose:

- Stamp 100 m training squares.
- Rotate and place square geometry.
- Enrich square attributes from vegetation and land-cover layers.

Near-term product direction:

- Become a separate plugin mode/tool.
- Add safer layer schema validation.
- Add configurable square size and rotation controls.
- Add clearer reporting of attributes filled from supporting layers.

## Track C: Canopy Proposals Within Squares

Current source script:

```text
prototypes/canopies_workflow/PolygonsWithinSquare3.py
```

Current maturity:

```text
Mid-level prototype. Useful direction, not production-ready.
```

Purpose:

- Generate or filter canopy polygon proposals within training squares.
- Use CHM-derived candidates and forest-mode presets.

Near-term product direction:

- Treat as experimental until accuracy, speed, and failure cases are better understood.
- Build behind batch-processing safety limits.
- Require preview/review before writing features.

## Track D: Apex Detection

Current source script:

```text
prototypes/canopies_workflow/ApexDetector.py
```

Current maturity:

```text
Mid-level prototype. Needs more work before production use.
```

Purpose:

- Detect tree apex candidates within training squares.
- Write candidate points to an apex layer.

Near-term product direction:

- Keep as a research/assistive workflow first.
- Add quality metrics and review flags.
- Avoid presenting output as final until validation improves.

## UI Implication

The plugin should eventually expose modes similar to:

- Label Canopy
- Create Training Square
- Propose Canopies In Square
- Detect Apexes
- Validate Project

The first two modes are the production priority. The last two should stay clearly marked as experimental until they pass stronger QA.

The code-level registry for these modes lives in `forest_labeler_core/workflows.py`. UI controls should use that registry instead of hard-coding workflow labels or maturity states.

The dock UI now reads from that registry so users can see workflow mode, maturity, write behavior, and experimental warnings before a tool is wired in.
