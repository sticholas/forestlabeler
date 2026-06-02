# Forest Labeler Feature Builder Script

Use this when asking Codex to implement a new Forest Labeler capability.

```text
Implement the next small, reviewable Forest Labeler product slice. Work like a senior engineer responsible for a safe QGIS production plugin.

Task:
[PASTE THE SPECIFIC FEATURE OR BUG HERE]

Before coding:
- Read docs/product/IMPLEMENTATION_PLAN.md, docs/development/ARCHITECTURE.md, docs/operations/QUALITY_GATES.md, and the files directly touched by this feature.
- Use rtk for broad/noisy commands.
- Check git status and do not revert user changes.
- Identify whether this belongs to:
  - Validate Project
  - Label Canopy
  - Create Training Polygon
  - Propose Canopies In Square
  - Detect Apexes
  - Feedback/Evaluation
  - Packaging/Release

Implementation expectations:
- Prefer forest_labeler_core/ for testable rules and forest_labeler_qgis/ for QGIS adapters.
- Keep forest_labeler_dockwidget.py focused on UI coordination.
- Do not copy prototype code wholesale into UI handlers.
- Preserve workflow maturity rules from forest_labeler_core/workflows.py.
- Validate project state before enabling or applying writes.
- Use clear user-facing errors and warnings.
- Keep edits narrow and easy to review.

For canopy labeling work:
- Keep dense, mixed, sparse, and crown tightness explicit.
- Species decisions must report no species, one species, and multiple species cases.
- Geometry and CRS handling must be explicit before writes.
- Feature writes should flow through the controlled service/writer path.

For training polygon work:
- Keep square size and rotation configurable.
- Validate target polygon layer schema.
- Report which attributes were filled, skipped, or unavailable.

For experimental workflows:
- Keep experimental warning visible.
- Add preview or confirmation before writes.
- Track enough metadata for later review.

Verification:
- Run bash scripts/checks.sh unless blocked.
- Add or update unit tests for pure behavior.
- If QGIS is required, write a short manual verification note with:
  - QGIS version needed or used
  - project/layers needed
  - steps
  - expected result
  - risks that remain

Final response:
- Summarize files changed.
- Summarize tests run.
- Call out QGIS/manual verification still needed.
```

