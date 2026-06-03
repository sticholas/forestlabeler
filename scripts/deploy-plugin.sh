#!/usr/bin/env bash
set -euo pipefail

PLUGIN_NAME="forest_labeler_qgis_plugin"
SOURCE_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
WINDOWS_USER="${WINDOWS_USER:-${USER:-}}"
DEFAULT_QGIS_PLUGIN_DIR="/mnt/c/Users/${WINDOWS_USER}/AppData/Roaming/QGIS/QGIS3/profiles/default/python/plugins"
TARGET_BASE_DIR="${QGIS_PLUGIN_DIR:-${DEFAULT_QGIS_PLUGIN_DIR}}"
TARGET_DIR="${TARGET_BASE_DIR}/${PLUGIN_NAME}"
BACKUP_DIR="${TARGET_DIR}.backup.$(date +%Y%m%d%H%M%S)"

if [[ -z "${TARGET_BASE_DIR}" ]]; then
  echo "Set QGIS_PLUGIN_DIR to your QGIS profile plugin directory." >&2
  exit 1
fi

if [[ ! -f "${SOURCE_DIR}/metadata.txt" ]]; then
  echo "Could not find metadata.txt in ${SOURCE_DIR}" >&2
  exit 1
fi

if [[ -d "${TARGET_DIR}" ]]; then
  cp -a "${TARGET_DIR}" "${BACKUP_DIR}"
fi

rm -rf "${TARGET_DIR}"
mkdir -p "${TARGET_DIR}"

tar \
  --exclude='.git' \
  --exclude='.github' \
  --exclude='.gitattributes' \
  --exclude='.gitignore' \
  --exclude='docs' \
  --exclude='prototypes' \
  --exclude='test' \
  --exclude='unit_tests' \
  --exclude='scripts' \
  --exclude='README.md' \
  --exclude='CONTRIBUTING.md' \
  --exclude='scratch' \
  --exclude='data' \
  --exclude='exports' \
  --exclude='*.zip' \
  --exclude='__pycache__' \
  -C "${SOURCE_DIR}" \
  -cf - . | tar -C "${TARGET_DIR}" -xf -

echo "Deployed ${PLUGIN_NAME} to ${TARGET_DIR}"
if [[ -d "${BACKUP_DIR}" ]]; then
  echo "Previous install backed up at ${BACKUP_DIR}"
fi
