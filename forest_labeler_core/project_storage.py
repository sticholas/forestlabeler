"""Project-local storage naming policy for Forest Labeler."""

from __future__ import annotations

import re


DEFAULT_PROJECT_STORAGE_PREFIX = "forest_labeler_project"
PROJECT_STORAGE_SUFFIX = "forest_labeler_files"
LEGACY_PROJECT_STORAGE_FOLDER = "forest_labeler_tool_files"


def project_storage_folder_name(project_file_name):
    """Return the project-specific Forest Labeler storage folder name."""
    stem = _project_stem(project_file_name)
    return f"{stem}_{PROJECT_STORAGE_SUFFIX}"


def _project_stem(project_file_name):
    raw_name = str(project_file_name or "").strip()
    if not raw_name:
        return DEFAULT_PROJECT_STORAGE_PREFIX
    name = raw_name.rsplit("/", 1)[-1].rsplit("\\", 1)[-1]
    stem = name.rsplit(".", 1)[0] if "." in name else name
    normalized = re.sub(r"[^A-Za-z0-9_-]+", "_", stem).strip("_")
    return normalized or DEFAULT_PROJECT_STORAGE_PREFIX
