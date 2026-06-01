# Contributing

## How We Work

Forest Labeler should be built in small, understandable steps. Every ticket should explain the user problem, the intended behavior, and how the change will be verified.

## Ticket Template

Use the GitHub issue templates in `.github/ISSUE_TEMPLATE/`.

## Pull Requests

Each pull request should include:

- what changed
- why it changed
- how it was tested
- screenshots or short notes for visual QGIS behavior

## Coding Expectations

- Prefer clear module boundaries over one large script.
- Keep QGIS UI code separate from canopy algorithm logic.
- Use descriptive names for settings and thresholds.
- Document non-obvious spatial assumptions.
- Do not commit local datasets unless they are tiny test fixtures.
