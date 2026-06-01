#!/usr/bin/env bash
set -euo pipefail

PROJECT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${PROJECT_ROOT}"

echo "== Python syntax =="
python3 -m py_compile \
  forest_labeler.py \
  forest_labeler_dockwidget.py \
  forest_labeler_core/*.py \
  forest_labeler_qgis/*.py

echo "== Unit tests =="
python3 -m unittest discover -s unit_tests

echo "== Qt UI XML =="
python3 -c "import xml.etree.ElementTree as ET; ET.parse('forest_labeler_dockwidget_base.ui'); print('ui ok')"

echo "All local checks passed."
