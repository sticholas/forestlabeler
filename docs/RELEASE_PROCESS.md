# Release Process

This document keeps Forest Labeler releases calm and repeatable.

## Branch Strategy

`main` is the stable branch people should use.

Feature work should happen on short-lived branches or intentionally stacked
phase branches. Stacked branches are acceptable during active development, but
they should be merged in order before telling users to install from `main`.

Current preferred release flow:

1. Finish the active phase branch.
2. Run local checks.
3. Deploy to local QGIS and perform manual verification.
4. Merge stacked PRs from oldest to newest.
5. Retarget each next PR to `main` after its base merges.
6. Confirm `main` contains the intended plugin state.
7. Delete merged remote branches.
8. Tag a release when the plugin is ready for broader use.

## Required Checks

Run:

```bash
bash scripts/checks.sh
```

For QGIS verification, deploy locally:

```bash
bash scripts/deploy-plugin.sh
```

Then run the relevant manual checklist:

- [Track A QGIS Verification](TRACK_A_QGIS_VERIFICATION.md)

## Release Readiness Checklist

- README explains what the plugin does.
- Install guide is current.
- User guide covers the available workflows.
- `metadata.txt` version is updated when cutting a named release.
- QGIS plugin loads without traceback.
- Validate Project gives clear errors/warnings.
- Label Canopy can create a polygon in a real QGIS project.
- Canopy metadata fields are created or warnings are understandable.
- Review actions work on selected features.
- Feedback CSV records stable `attempt_id` and real `canopy_fid`.
- Known experimental workflows are clearly marked experimental.

## User Install Source

During development, users can install from the latest stable `main`.

For formal release, provide a zip whose root plugin folder is:

```text
forest_labeler_qgis_plugin
```

Do not ask users to install from a temporary phase branch unless they are testing
a specific unreleased feature.
