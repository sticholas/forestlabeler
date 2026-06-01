# Forest Labeler Review And QA Script

Use this when asking Codex to review a change, PR, branch, or risky area.

```text
Review this Forest Labeler change as a senior project engineer. Prioritize bugs, data-safety risks, workflow regressions, missing tests, and product-quality gaps.

Scope:
[PASTE BRANCH, PR, DIFF, OR FILES HERE]

Context to read:
- docs/QUALITY_GATES.md
- docs/DECISION_FRAMEWORK.md
- docs/IMPLEMENTATION_PLAN.md
- docs/ARCHITECTURE.md
- forest_labeler_core/workflows.py
- Any files changed by the scope

Review priorities, in order:
1. Data safety: wrong-layer writes, partial writes, unsafe edit sessions, missing rollback, missing CRS checks, invalid geometry, missing schema validation.
2. Workflow clarity: production versus experimental state, clear UI mode, clear blocked-action messages.
3. Architecture: pure logic in core, QGIS specifics in adapters, thin UI/controller code, no direct production dependence on prototype scripts.
4. Testability: unit tests for pure helpers, small QGIS adapters, manual QGIS verification notes where needed.
5. Product quality: does the change make canopy labeling, training polygons, validation, review, or feedback faster and clearer?
6. Maintainability: small slices, explicit configuration, readable naming, no hidden globals or local machine assumptions.

Commands:
- Use rtk git status and rtk git diff for broad inspection.
- Use rtk rg for targeted searches.
- Run bash scripts/checks.sh if the review requires verification and it is feasible.

Output format:
- Findings first, ordered by severity, with file/line references.
- Then open questions or assumptions.
- Then testing performed or not performed.
- Then a short product/architecture summary.

If there are no issues:
- Say no blocking issues found.
- Still list residual risks, especially QGIS manual verification gaps.
```

