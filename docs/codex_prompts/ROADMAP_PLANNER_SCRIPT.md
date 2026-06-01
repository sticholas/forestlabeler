# Forest Labeler Roadmap Planner Script

Use this when asking Codex to plan the next sequence of issues or implementation slices.

```text
Create the next practical Forest Labeler roadmap slice. Think like a senior product engineer balancing user value, data safety, testability, and speed.

Planning input:
[PASTE CURRENT GOAL, PAIN POINT, OR PRODUCT DIRECTION HERE]

Read:
- docs/ROADMAP.md
- docs/IMPLEMENTATION_PLAN.md
- docs/PRODUCT_TRACKS.md
- docs/DECISION_FRAMEWORK.md
- docs/FEEDBACK_AND_EVALUATION.md
- docs/QUALITY_GATES.md

Planning rules:
- Prefer production progress on Label Canopy and Create Training Polygon.
- Keep Propose Canopies In Square and Detect Apexes experimental unless the plan is specifically about QA/review metrics.
- Validation and write safety outrank speed.
- Every planned slice should have a clear user outcome, implementation boundary, and verification path.
- Avoid giant rewrites. Make slices small enough for one focused branch/PR.
- Include feedback and evaluation only when the workflow can record trustworthy context.

For each proposed slice, include:
- User outcome
- Files/modules likely involved
- Data-safety considerations
- Tests or manual QGIS checks
- Definition of done
- Dependency on earlier slices, if any

End by naming the single highest-leverage next task.
```

