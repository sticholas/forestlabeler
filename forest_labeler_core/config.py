"""Default project settings for Forest Labeler."""

CHM_LAYER_NAME = "chm"
TARGET_LAYER_NAME = "training_canopies_existing_imagery"
SPECIES_POINT_LAYER_NAME = "TrainingMerge2"
SPECIES_CODE_FIELD = "code"

TARGET_REQUIRED_FIELDS = ("species",)
TARGET_RECOMMENDED_FIELDS = (
    "fid",
    "radius_m",
    "diam_m",
    "area_m2",
    "apex_h",
    "mode",
    "tightness",
    "reviewed",
    "review_status",
    "review_note",
    "refined",
    "ortho_id",
)
