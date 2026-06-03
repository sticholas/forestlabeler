# Development Workflow

## Recommended Tools

- PyCharm for editing and navigation
- Warp for commands
- QGIS for runtime testing
- GitHub issues for planned work

## Local Setup Notes

This project depends on QGIS Python modules such as `qgis.core`, `qgis.gui`, and `qgis.PyQt`. Those imports usually work only inside QGIS or inside QGIS' configured Python environment.

For now, use normal Python tooling for files that do not import QGIS directly, and use QGIS itself to test plugin loading and map interactions.

## Branching

Use short-lived branches:

```text
codex/foundation-scaffold
codex/core-extraction
codex/ui-layer-selection
codex/canopy-map-tool
```

## Commit Style

Prefer small, story-shaped commits:

```text
docs: define plugin roadmap and architecture
refactor: move canopy settings into config module
feat: add layer validation service
feat: wire canopy delineation map tool
test: cover radial smoothing helper
```

## Definition of Done

A task is done when:

- code is committed on a branch
- behavior is documented or obvious from UI
- tests or manual verification notes exist
- QGIS plugin reloads without import errors
- the change is small enough to review

## Manual QGIS Verification

For every plugin behavior change, record:

- QGIS version
- plugin version
- test project or layers used
- steps performed
- expected result
- actual result
- any screenshots if behavior is visual

## Deploy To QGIS

From Warp/WSL:

```bash
cd "<your Forest Labeler checkout>"
bash scripts/deploy-plugin.sh
```

Restart QGIS or use Plugin Reloader after deployment.

## Unit Tests

QGIS-independent tests live in `unit_tests/` so they can run in ordinary Python:

```bash
python3 -m unittest discover -s unit_tests
```

## Local Check Command

Run the standard local checks before committing:

```bash
bash scripts/checks.sh
```

This currently runs Python syntax checks, QGIS-independent unit tests, and Qt UI XML parsing.
