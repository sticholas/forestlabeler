# QGIS
qgis-build:
	@cp -r forestlabeler forest_labeler_qgis_plugin
	@echo "Removing __pycache__..."
	rm -rf forest_labeler_qgis_plugin/__pycache__
	@echo "Creating plugin zip..."
	zip -r forest_labeler_qgis_plugin.zip forest_labeler_qgis_plugin/ \
	  -x "*.DS_Store" "*__MACOSX*"