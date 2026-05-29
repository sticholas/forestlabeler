# Quality Gates

## Before Merging a Change

- Scope is small and connected to a ticket.
- Plugin still loads in QGIS.
- New behavior has tests or manual verification notes.
- No local data, caches, or generated junk are committed.
- User-facing failures report a clear reason.

## End Of Phase Review

Every phase ends with a short review note that answers:

- What works now?
- What was verified mechanically?
- What was verified inside QGIS?
- What risks remain?
- What would block the next phase?
- Which issue or PR carries the next slice of work?

## Code Review Checklist

- Does this change preserve existing user data?
- Are layer names, field names, and thresholds configurable?
- Are CRS transformations explicit?
- Are geometry operations checked for empty or invalid results?
- Are exceptions handled at the boundary where QGIS can show feedback?
- Is prototype code being migrated rather than duplicated blindly?

## Testing Levels

- Unit tests: pure Python helpers and configuration rules.
- Integration checks: QGIS layer/raster adapters where feasible.
- Manual QGIS tests: plugin loading, map clicks, feature edits, visual output.

## Manual Test Record

Manual QGIS checks should record:

- QGIS version
- plugin branch or commit
- project file used
- layer names selected
- exact action performed
- expected result
- actual result
- screenshots when the result is visual

## Phase 1 Minimum Check

- Plugin imports without traceback.
- Dock opens from the toolbar/menu action.
- Layer selectors populate from the current project.
- `Validate` fails when required layers are missing.
- `Validate` passes only when required layer and field contracts are satisfied.

## Phase 2 Minimum Check

- Reference scripts are inventoried.
- Migrated helpers are no longer dependent on QGIS globals such as `iface` or `canvas`.
- Configuration is explicit and reviewable.
- Pure helper tests can run outside QGIS.
- `bash scripts/checks.sh` passes before pushing.
- Each workflow is labeled as production-target or experimental before UI wiring.

## Release Checklist

- Update `metadata.txt` version.
- Update changelog or release notes.
- Build plugin zip from a clean source tree.
- Install zip into a fresh QGIS profile when possible.
- Run the manual verification checklist.
