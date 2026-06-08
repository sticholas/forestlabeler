import unittest

from forest_labeler_core.project_storage import project_storage_folder_name


class ProjectStorageTest(unittest.TestCase):
    def test_uses_project_name_in_storage_folder(self):
        self.assertEqual(
            project_storage_folder_name("Labelling.qgz"),
            "Labelling_forest_labeler_files",
        )

    def test_sanitizes_project_name_for_folder(self):
        self.assertEqual(
            project_storage_folder_name("Big Island / Labelling Draft.qgs"),
            "Labelling_Draft_forest_labeler_files",
        )

    def test_has_default_for_unsaved_project(self):
        self.assertEqual(
            project_storage_folder_name(""),
            "forest_labeler_project_forest_labeler_files",
        )


if __name__ == "__main__":
    unittest.main()
