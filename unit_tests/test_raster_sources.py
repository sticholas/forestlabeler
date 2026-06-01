import unittest

from forest_labeler_core.raster_sources import is_probable_ortho_source


class RasterSourceTest(unittest.TestCase):
    def test_accepts_local_gdal_ortho_extensions(self):
        self.assertTrue(
            is_probable_ortho_source(
                name="Dry Forest Ortho",
                source="X:/imagery/dry_forest_ortho.tif",
                provider_type="gdal",
                excluded_names=["chm"],
            )
        )

    def test_rejects_chm_or_other_excluded_layers(self):
        self.assertFalse(
            is_probable_ortho_source(
                name="chm",
                source="X:/rasters/chm.tif",
                provider_type="gdal",
                excluded_names=["chm"],
            )
        )
        self.assertFalse(
            is_probable_ortho_source(
                name="CAH_LandCover",
                source="X:/rasters/landcover.tif",
                provider_type="gdal",
                excluded_names=["CAH_LandCover"],
            )
        )

    def test_rejects_web_and_tile_sources(self):
        self.assertFalse(
            is_probable_ortho_source(
                name="Google Satellite",
                source="type=xyz&url=https://tiles.example.com/{z}/{x}/{y}.png",
                provider_type="wms",
            )
        )
        self.assertFalse(
            is_probable_ortho_source(
                name="Local tiles",
                source="X:/imagery/tiles/index.tif",
                provider_type="gdal",
            )
        )

    def test_rejects_non_gdal_or_unknown_extensions(self):
        self.assertFalse(
            is_probable_ortho_source(
                name="Ortho",
                source="X:/imagery/ortho.tif",
                provider_type="wms",
            )
        )
        self.assertFalse(
            is_probable_ortho_source(
                name="Ortho",
                source="X:/imagery/ortho.png",
                provider_type="gdal",
            )
        )


if __name__ == "__main__":
    unittest.main()
