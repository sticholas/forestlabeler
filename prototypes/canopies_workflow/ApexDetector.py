from qgis.PyQt.QtWidgets import QMessageBox
from qgis.core import (
    QgsProject,
    QgsFeature,
    QgsGeometry,
    QgsPointXY,
    QgsVectorLayer,
    QgsRasterLayer,
    QgsCoordinateTransform
)
import math

# ============================================================
# LAYER NAMES
# ============================================================

TRAINING_SQUARE_LAYER_NAME = "training_squares"
APEX_OUTPUT_LAYER_NAME = "training_apexes"
CHM_LAYER_NAME = "chm"

CANOPY_MODE = "DENSE"   # "DENSE", "SPARSE", "MIXED"

# ============================================================
# DETECTOR SETTINGS
# ============================================================

MAX_TOTAL_CANDIDATES = 180

MIN_GRID_SIZE_M = 1.0
MAX_GRID_SIZE_M = 1.5

# Stricter multi-scale search
APEX_SCALES_M = [1.5, 2.5, 3.5, 4.5]
MIN_APEX_HEIGHT_M = 1.1
MIN_PROMINENCE_M = 0.75
MIN_APEX_SEPARATION_M = 2.2
MIN_APEX_NEIGHBOR_SUPPORT_RATIO = 0.45

SECONDARY_APEX_MIN_PROMINENCE = 0.38
SECONDARY_APEX_MIN_SUPPORT = 0.40

# extra precision filters
APEX_LOCAL_DOMINANCE_RADIUS_M = 1.5
APEX_LOCAL_DOMINANCE_MIN_RATIO = 0.55

# overwrite behavior
CLEAR_OLD_AUTO_POINTS_FOR_SELECTED_SQUARE = True
PRESERVE_MANUAL_POINTS = True

# ============================================================
# MODE PRESETS
# ============================================================

if CANOPY_MODE == "DENSE":
    MIN_CANOPY_SUPPORT_M = 1.7
elif CANOPY_MODE == "SPARSE":
    MIN_CANOPY_SUPPORT_M = 0.9
else:
    MIN_CANOPY_SUPPORT_M = 1.2


# ============================================================
# HELPERS
# ============================================================

def get_layer(name):
    layers = QgsProject.instance().mapLayersByName(name)
    return layers[0] if layers else None

def layer_has_field(layer, field_name):
    return layer.fields().indexOf(field_name) != -1

def safe_set_attr(feat, field_name, value):
    idx = feat.fields().indexOf(field_name)
    if idx != -1:
        feat[field_name] = value

def transform_geom(geom, src_crs, dst_crs):
    if src_crs == dst_crs:
        return QgsGeometry(geom)
    tr = QgsCoordinateTransform(src_crs, dst_crs, QgsProject.instance())
    g = QgsGeometry(geom)
    g.transform(tr)
    return g

def transform_point_xy(point_xy, src_crs, dst_crs):
    if src_crs == dst_crs:
        return QgsPointXY(point_xy)
    tr = QgsCoordinateTransform(src_crs, dst_crs, QgsProject.instance())
    return tr.transform(QgsPointXY(point_xy))

def sample_raster_value(raster_layer, point_xy, band=1):
    try:
        provider = raster_layer.dataProvider()
        val, ok = provider.sample(point_xy, band)
        if ok and val is not None:
            return float(val)
    except Exception:
        return None
    return None

def point_in_geom(geom, pt):
    return geom.contains(QgsGeometry.fromPointXY(pt))

def polygon_bbox_points(geom):
    rect = geom.boundingBox()
    return rect.xMinimum(), rect.yMinimum(), rect.xMaximum(), rect.yMaximum()

def xy_of(pt):
    if isinstance(pt, (tuple, list)) and len(pt) >= 2:
        return float(pt[0]), float(pt[1])
    try:
        return float(pt.x()), float(pt.y())
    except Exception:
        pass
    try:
        p = QgsPointXY(pt)
        return float(p.x()), float(p.y())
    except Exception:
        pass
    raise TypeError(f"Could not read coordinates from point object: {type(pt)}")

def distance_xy(p1, p2):
    x1, y1 = xy_of(p1)
    x2, y2 = xy_of(p2)
    return math.hypot(x2 - x1, y2 - y1)

def median(values):
    if not values:
        return None
    s = sorted(values)
    n = len(s)
    m = n // 2
    return s[m] if n % 2 == 1 else (s[m - 1] + s[m]) / 2.0

def next_numeric_id(layer, field_name):
    if not layer_has_field(layer, field_name):
        return None
    max_val = 0
    for f in layer.getFeatures():
        try:
            v = f[field_name]
            if v is None:
                continue
            max_val = max(max_val, int(v))
        except Exception:
            continue
    return max_val + 1


# ============================================================
# APEX PREVIEW EXTRACTOR
# ============================================================

class ReviewedApexExtractor:
    def __init__(self, chm_layer, square_geom_project, project_crs):
        self.chm = chm_layer
        self.square_geom_project = square_geom_project
        self.project_crs = project_crs
        self.square_geom_chm = transform_geom(square_geom_project, project_crs, chm_layer.crs())

        try:
            px = abs(chm_layer.rasterUnitsPerPixelX())
            py = abs(chm_layer.rasterUnitsPerPixelY())
            cell = max(px, py)
        except Exception:
            cell = 1.0

        self.cell = max(MIN_GRID_SIZE_M, min(MAX_GRID_SIZE_M, cell))
        self.grid = self.build_grid()

    def build_grid(self):
        xmin, ymin, xmax, ymax = polygon_bbox_points(self.square_geom_chm)
        grid = []
        x = xmin + self.cell * 0.5
        while x <= xmax + 1e-9:
            y = ymin + self.cell * 0.5
            while y <= ymax + 1e-9:
                pt = QgsPointXY(x, y)
                if point_in_geom(self.square_geom_chm, pt):
                    v = sample_raster_value(self.chm, pt, 1)
                    if v is not None:
                        grid.append((float(x), float(y), float(v)))
                y += self.cell
            x += self.cell
        return grid

    def values_within_radius(self, center_pt, radius):
        vals = []
        cx, cy = xy_of(center_pt)
        for x, y, v in self.grid:
            if math.hypot(x - cx, y - cy) <= radius:
                vals.append(v)
        return vals

    def support_ratio_within_radius(self, center_pt, radius, threshold):
        cx, cy = xy_of(center_pt)
        total = 0
        good = 0
        for x, y, v in self.grid:
            if math.hypot(x - cx, y - cy) <= radius:
                total += 1
                if v >= threshold:
                    good += 1
        return (good / total) if total else 0.0

    def local_prominence(self, center_pt, center_val, radius):
        vals = self.values_within_radius(center_pt, radius)
        med = median(vals)
        if med is None:
            return 0.0
        return center_val - med

    def is_local_max_at_scale(self, px, py, val, radius):
        for x, y, v in self.grid:
            if math.hypot(x - px, y - py) <= radius and v > val + 1e-9:
                return False
        return True

    def local_dominance_ratio(self, center_pt, center_val, radius):
        vals = self.values_within_radius(center_pt, radius)
        if not vals:
            return 0.0
        strong = 0
        for v in vals:
            if v >= center_val * 0.80:
                strong += 1
        return strong / max(len(vals), 1)

    def classify_candidate(self, pt, val, prom, scale):
        local_threshold = max(MIN_CANOPY_SUPPORT_M, val * 0.25)
        local_support = self.support_ratio_within_radius(pt, max(scale, 1.5), local_threshold)
        dominance = self.local_dominance_ratio(pt, val, APEX_LOCAL_DOMINANCE_RADIUS_M)

        if (
            prom >= MIN_PROMINENCE_M and
            local_support >= MIN_APEX_NEIGHBOR_SUPPORT_RATIO and
            dominance >= APEX_LOCAL_DOMINANCE_MIN_RATIO
        ):
            return "strong", local_support, dominance

        if (
            prom >= SECONDARY_APEX_MIN_PROMINENCE and
            local_support >= SECONDARY_APEX_MIN_SUPPORT and
            dominance >= (APEX_LOCAL_DOMINANCE_MIN_RATIO * 0.80)
        ):
            return "secondary", local_support, dominance

        return None, local_support, dominance

    def find_candidate_centers(self):
        candidates = []

        for scale in APEX_SCALES_M:
            for x, y, v in self.grid:
                if v < MIN_APEX_HEIGHT_M:
                    continue
                if not self.is_local_max_at_scale(x, y, v, scale):
                    continue

                pt = QgsPointXY(x, y)
                prom = self.local_prominence(pt, v, max(scale, 2.0))
                cls, local_support, dominance = self.classify_candidate(pt, v, prom, scale)
                if cls is None:
                    continue

                class_rank = {"strong": 3, "secondary": 2}[cls]
                candidates.append((pt, v, prom, scale, local_support, dominance, cls, class_rank))

        candidates.sort(key=lambda t: (t[7], t[1], t[2], t[4], t[5]), reverse=True)

        filtered = []
        for cand in candidates:
            pt = cand[0]
            keep = True
            for old in filtered:
                if distance_xy(pt, old[0]) < MIN_APEX_SEPARATION_M:
                    keep = False
                    break
            if keep:
                filtered.append(cand)
            if len(filtered) >= MAX_TOTAL_CANDIDATES:
                break

        return filtered


# ============================================================
# DELETE OLD AUTO POINTS FOR SELECTED SQUARE
# ============================================================

def delete_old_auto_points_for_square(apex_layer, square_fid):
    if square_fid is None:
        return 0

    ids_to_delete = []
    for f in apex_layer.getFeatures():
        try:
            f_square = f["square_fid"] if layer_has_field(apex_layer, "square_fid") else None
            if f_square != square_fid:
                continue

            cls_val = str(f["cls"]).strip().lower() if layer_has_field(apex_layer, "cls") and f["cls"] is not None else ""

            if PRESERVE_MANUAL_POINTS and cls_val == "manual":
                continue

            ids_to_delete.append(f.id())
        except Exception:
            continue

    if ids_to_delete:
        apex_layer.deleteFeatures(ids_to_delete)

    return len(ids_to_delete)


# ============================================================
# RUN
# ============================================================

square_layer = get_layer(TRAINING_SQUARE_LAYER_NAME)
apex_layer = get_layer(APEX_OUTPUT_LAYER_NAME)
chm = get_layer(CHM_LAYER_NAME)

if not square_layer or not isinstance(square_layer, QgsVectorLayer):
    QMessageBox.warning(None, "Missing square layer", f"Could not find square layer named '{TRAINING_SQUARE_LAYER_NAME}'.")
elif not apex_layer or not isinstance(apex_layer, QgsVectorLayer):
    QMessageBox.warning(None, "Missing apex layer", f"Could not find apex layer named '{APEX_OUTPUT_LAYER_NAME}'.")
elif not chm or not isinstance(chm, QgsRasterLayer):
    QMessageBox.warning(None, "Missing CHM", f"Could not find CHM layer named '{CHM_LAYER_NAME}'.")
elif not apex_layer.isEditable():
    QMessageBox.warning(None, "Apex layer not editable", "Turn editing on for the apex point layer.")
else:
    selected = square_layer.selectedFeatures()
    if len(selected) != 1:
        QMessageBox.warning(None, "Select one square", "Select exactly one feature in training_squares, then run this script.")
    else:
        project_crs = iface.mapCanvas().mapSettings().destinationCrs()
        square_feat = selected[0]
        square_geom_project = transform_geom(square_feat.geometry(), square_layer.crs(), project_crs)
        square_fid = square_feat["fid"] if layer_has_field(square_layer, "fid") else None

        deleted_count = 0
        if CLEAR_OLD_AUTO_POINTS_FOR_SELECTED_SQUARE:
            deleted_count = delete_old_auto_points_for_square(apex_layer, square_fid)

        extractor = ReviewedApexExtractor(chm, square_geom_project, project_crs)
        apexes = extractor.find_candidate_centers()

        apex_fid = next_numeric_id(apex_layer, "fid")
        if apex_fid is None:
            apex_fid = 1

        added = 0
        for pt_chm, apex_h, prom, scale_m, support, dominance, cls, class_rank in apexes:
            pt_layer = transform_point_xy(pt_chm, chm.crs(), apex_layer.crs())

            feat = QgsFeature(apex_layer.fields())
            feat.setGeometry(QgsGeometry.fromPointXY(pt_layer))

            safe_set_attr(feat, "fid", apex_fid)
            apex_fid += 1
            safe_set_attr(feat, "square_fid", square_fid)
            safe_set_attr(feat, "apex_h", round(apex_h, 2))
            safe_set_attr(feat, "prom", round(prom, 3))
            safe_set_attr(feat, "scale_m", round(scale_m, 2))
            safe_set_attr(feat, "support", round(support, 3))
            safe_set_attr(feat, "cls", cls)
            safe_set_attr(feat, "keep", 1)
            safe_set_attr(feat, "notes", None)

            if apex_layer.addFeature(feat):
                added += 1

        apex_layer.updateExtents()
        apex_layer.triggerRepaint()
        iface.mapCanvas().refresh()

        iface.messageBar().pushInfo(
            "Reviewed Apex Preview",
            f"Deleted {deleted_count} old auto points, added {added} apex points for the selected square."
        )