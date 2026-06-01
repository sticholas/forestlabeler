# Quality Gates

## Before Merging a Change

- Scope is small and connected to a ticket.
- Plugin still loads in QGIS.
- New behavior has tests or manual verification notes.
- No local data, caches, or generated junk are committed.
- User-facing failures report a clear reason.

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

## Release Checklist

- Update `metadata.txt` version.
- Update changelog or release notes.
- Build plugin zip from a clean source tree.
- Install zip into a fresh QGIS profile when possible.
- Run the manual verification checklist.
