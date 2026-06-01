# Contributing

Forest Labeler is built for clear, reviewable progress. Changes should be easy
for a GIS teammate to understand and easy for a developer to verify.

## Start Here

- Product direction: [docs/README.md](docs/README.md)
- Architecture: [docs/development/ARCHITECTURE.md](docs/development/ARCHITECTURE.md)
- Development workflow: [docs/development/DEVELOPMENT.md](docs/development/DEVELOPMENT.md)
- Quality gates: [docs/operations/QUALITY_GATES.md](docs/operations/QUALITY_GATES.md)

## Working Standards

- Keep pure logic in `forest_labeler_core/`.
- Keep QGIS-specific adapters in `forest_labeler_qgis/`.
- Keep dock-widget handlers focused on UI coordination.
- Validate project/layer state before writing data.
- Preserve existing user data.
- Keep prototype scripts in `prototypes/` until behavior is migrated,
  verified, or intentionally retired.

## Pull Requests

Each PR should explain:

- what changed
- why it matters to the workflow
- how it was tested
- whether QGIS manual verification is still needed

Run before opening or merging a PR:

```bash
bash scripts/checks.sh
```

If the change touches plugin loading, UI controls, map tools, or feature writes,
also deploy and test in QGIS:

```bash
bash scripts/deploy-plugin.sh
```
