# Future Capabilities

Forest Labeler can grow into a broader QGIS training-data assistant. These ideas should be explored behind clear workflow boundaries so the plugin remains reliable while it becomes more powerful.

## High-Value Extensions

### Review Dashboard

Show progress and quality signals for a project:

- number of canopies labeled
- number reviewed
- number rejected or uncertain
- species conflict count
- average canopy area by species or mode
- which tightness settings are working best

### Smart Recommendations

Recommend settings without silently changing behavior:

- ship a universal baseline so first-time users receive useful defaults
- adapt recommendations through compatible project and user evidence
- allow approved team and universal contributions through explicit opt-in
- suggest crown tightness based on reviewed success rates
- warn when a mode is producing many rejected polygons
- suggest checking species points if conflicts are frequent
- flag unusually large or small canopy polygons

Every recommendation should name its evidence scope, compatibility context,
sample size, and observed success rate.

### Guided QA

Help users inspect their own work:

- jump to unreviewed polygons
- jump to uncertain or rejected polygons
- filter by correction reason
- compare accepted vs edited shapes
- export a QA summary

### Training Square Productivity

Grow `NewTrainingSquare.py` into a square workflow:

- configurable square sizes
- rotation presets
- attribute fill report
- coverage map of completed squares
- reminders for missing supporting layers

### Experimental Assistive Tools

Keep experimental tools useful but honest:

- propose canopy polygons within a square
- detect apex candidates
- batch-review proposals
- score proposal confidence
- require explicit confirmation before writing experimental output

### Agent And Black-Box Testing

Future agents should repeatedly test real workflows:

- load plugin in QGIS
- open known project
- validate layers
- create known sample output
- inspect attributes
- compare screenshots/logs
- report regression risks

## Implementation Guardrails

- New capability starts as documentation and issue tracking.
- Production-target workflows get validation, tests, and manual QA.
- Experimental workflows stay labeled until quality is demonstrated.
- Feedback drives recommendations first, not automatic behavior changes.
