# Canopy Learning Log

Forest Labeler records canopy lifecycle events in a project-local SQLite
database:

```text
forest_labeler_tool_files/forest_labeler_feedback.sqlite3
```

This event store is the durable feedback trail for future tuning, QA summaries,
and learning systems. A readable CSV can be exported from **Review & QA** when a
user wants one:

```text
forest_labeler_tool_files/forest_labeler_canopy_attempts.csv
```

The CSV is a snapshot generated from SQLite, not a second source of truth.

## Identity Model

- `attempt_id` is the stable Forest Labeler identity for one canopy generation
  attempt. It is globally unique and is written to the canopy feature when the
  target layer has an `attempt_id` field.
- `canopy_fid` is the real canopy row identity from the target layer `fid`
  attribute. This is the field users see in the QGIS attribute table.
- `qgis_feature_id` is QGIS' internal feature ID. During edit sessions this can
  be negative or temporary, so it is useful for debugging but must not be used as
  the long-term learning identity.
- `project_id` is stored as the QGIS project variable
  `forest_labeler_project_id`. This keeps identity stable for a shared project
  even when different users keep the project folder in different local paths.

## Project-Scoped Learning

The current learning store is scoped to a QGIS project folder. That is
deliberate: canopy behavior depends on imagery, CHM resolution, forest type,
digitizing standards, and local user goals. A project-scoped store lets each
project adapt without mixing incompatible training signals.

Future team learning should promote these project-local logs into a shared
GeoPackage table, database, or review service. That shared layer should use
`attempt_id`, `project_id`, and `canopy_fid` as join keys instead of relying on
local file paths or QGIS temporary feature IDs.

## Timestamps

Events use UTC timestamps for machine-safe ordering across users and time zones.
Human-facing review tools should display local time later, but the stored log
should remain UTC so merged logs sort reliably.
