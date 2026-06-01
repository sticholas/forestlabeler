# Decision Framework

Forest Labeler should improve productivity without becoming fragile. Each implementation step should answer the questions below before it becomes production behavior.

## Decision Filters

### 1. User Value

- Does this save repeated manual effort?
- Does it reduce field/lab labeling mistakes?
- Does it make a common QGIS task clearer or faster?

### 2. Data Safety

- Can the plugin write to the wrong layer?
- Can it partially write data and then fail?
- Can the user understand what changed?
- Is rollback possible or at least clearly bounded?

### 3. Testability

- Can the rule run outside QGIS as a unit test?
- If QGIS is required, is the adapter small enough to manually verify?
- Is there a known project or dataset for repeatable checks?

### 4. Workflow Clarity

- Is this a production workflow or experimental workflow?
- Does the UI make the active mode obvious?
- Are blocked actions explained in plain language?

### 5. Future Growth

- Does this make future features easier?
- Are settings explicit rather than hidden in script globals?
- Can another contributor understand the module boundary?

## Implementation Rule

Prefer this order:

1. Document the workflow and maturity.
2. Extract pure backend logic with tests.
3. Add QGIS adapters for layers, rasters, geometry, and feature writing.
4. Add UI controls and validation.
5. Add write behavior with manual QGIS verification.

Directly copying console scripts into plugin buttons is not production work. It is acceptable only as a temporary prototype and must be labeled that way.

## Productivity Goal

Every production feature should make one of these faster:

- selecting the right layers
- creating training squares
- creating canopy polygons
- assigning/reviewing species
- detecting labeling mistakes
- producing consistent metadata
- reviewing experimental proposals safely
