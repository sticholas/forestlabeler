# Install Guide

Forest Labeler is a QGIS 3 plugin. It is currently developed and tested against
QGIS 3.44 LTR on Windows with the plugin source managed from WSL.

## Recommended User Install

Until Forest Labeler is published in an official plugin repository, install it
from a repository checkout or a release zip.

1. Download or clone the repository.
2. Copy the plugin folder into your QGIS profile plugin directory.
3. Restart QGIS.
4. Open **Plugins > Manage and Install Plugins**.
5. Enable **Forest Labeler**.

Typical Windows QGIS plugin directory:

```text
C:\Users\<your-user>\AppData\Roaming\QGIS\QGIS3\profiles\default\python\plugins
```

The installed plugin folder should be named:

```text
forest_labeler_qgis_plugin
```

## Local Developer Deploy

From WSL/Warp:

```bash
cd "/mnt/c/Users/Milo/Documents/Forest Labeler"
bash scripts/deploy-plugin.sh
```

The deploy script backs up the previous local install and copies the current
source into the QGIS plugin profile.

After deploying, restart QGIS or use Plugin Reloader.

## Required QGIS Project Layers

For **Label Canopy**, the project should include:

- A canopy height model raster, commonly named `chm`.
- A polygon target layer for canopy labels.
- An optional point layer for species labels.

The target canopy layer should be editable before labeling.

Recommended canopy fields can be added from the plugin with:

```text
Label Canopy > Add Canopy Metadata Fields
```

Important recommended fields include:

- `fid`
- `attempt_id`
- `num_trees`
- `radius_m`
- `diam_m`
- `area_m2`
- `apex_h`
- `mode`
- `tightness`
- `species`
- `reviewed`
- `review_status`
- `review_note`
- `refined`
- `chm_id`
- `ortho_id`

## Verify Install

1. Open QGIS.
2. Enable the plugin.
3. Open the Forest Labeler dock from the plugin toolbar/menu.
4. Select layers.
5. Click **Validate**.
6. Confirm validation passes or gives clear instructions about what to fix.

If QGIS reports an import error, redeploy the plugin and confirm the installed
folder contains `forest_labeler_core/`, `forest_labeler_qgis/`, and
`forest_labeler_dockwidget.py`.
