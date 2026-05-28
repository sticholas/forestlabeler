from qgis.PyQt.QtCore import Qt, QTimer
from qgis.PyQt.QtGui import QColor
from qgis.PyQt.QtWidgets import QMessageBox
from qgis.core import (
    Qgis,
    QgsProject,
    QgsFeature,
    QgsGeometry,
    QgsPointXY,
    QgsVectorLayer,
    QgsRasterLayer,
    QgsWkbTypes,
    QgsCoordinateTransform
)
from qgis.gui import QgsMapTool, QgsRubberBand
import math

canvas = iface.mapCanvas()

# ============================================================
# GLOBAL SETTINGS
# ============================================================

CHM_LAYER_NAME = "chm"

# Choose one: "DENSE", "SPARSE", "MIXED"
CANOPY_MODE = "DENSE"

# Seed growth
START_RADIUS_M = 0.75
MAX_RADIUS_M = 35.0
GROWTH_PER_TICK_M = 0.35
TIMER_INTERVAL_MS = 60

# Apex search
LOCAL_APEX_SEARCH_RADIUS_M = 2.0

# Radial sampling
NUM_ANGLES = 48
PROFILE_STEP_M = 0.35

# Inner support neighborhood
INNER_SUPPORT_RADIUS_FACTOR = 0.20
INNER_SUPPORT_RADIUS_MIN_M = 1.0

# Ownership / apex spacing
COMPETING_APEX_MIN_SEPARATION_M = 1.5
OWNERSHIP_DISTANCE_WEIGHT = 0.10
OWNERSHIP_DROP_WEIGHT = 0.12

# Envelope / region
ENVELOPE_MARGIN_FACTOR = 1.10

# Final radial smoothing
GAUSSIAN_SMOOTH_RADIUS = 2
GAUSSIAN_SMOOTH_SIGMA = 1.1
GAUSSIAN_SMOOTH_PASSES = 1
FINAL_BUFFER_SMOOTH_M = 0.35

# Grid sizing
MIN_GRID_SIZE_M = 0.25
MAX_GRID_SIZE_M = 1.50

# Metadata
FILL_ORTHO_ID = True


# ============================================================
# CANOPY PRESETS
# ============================================================

if CANOPY_MODE == "DENSE":
    MIN_CANOPY_HEIGHT_M = 1.5
    CENTER_HEIGHT_FRACTION = 0.12

    INNER_SUPPORT_FRACTION = 0.18

    PROFILE_MAX_FACTOR = 1.60
    PROFILE_MAX_EXTRA_M = 4.0
    PROFILE_MIN_SEARCH_M = 3.0

    MIN_DESCENT_SLOPE = 0.015
    REBOUND_RISE_M = 0.80
    REBOUND_STEPS = 2

    EDGE_DROP_WEIGHT = 2.1
    SHOULDER_CURVATURE_WEIGHT = 1.5
    EDGE_HEIGHT_RATIO_LOW = 0.08
    EDGE_HEIGHT_RATIO_HIGH = 0.30
    EDGE_HEIGHT_BAND_BONUS = 1.8

    COMPETING_APEX_SEARCH_FACTOR = 1.80
    COMPETING_APEX_EXTRA_M = 3.0
    COMPETING_APEX_MIN_RELATIVE_HEIGHT = 0.30
    OWNERSHIP_MARGIN = 0.18

    SEED_RADIUS_PENALTY = 0.08
    LOW_OUTSIDE_PENALTY = 0.55
    PROFILE_COMPETITOR_PENALTY = 1.25

    SMOOTH_PROFILE_PASSES = 3
    SMOOTH_RADIUS_PASSES = 2
    SMOOTH_RADIUS_WINDOW = 2

elif CANOPY_MODE == "SPARSE":
    MIN_CANOPY_HEIGHT_M = 0.8
    CENTER_HEIGHT_FRACTION = 0.06

    INNER_SUPPORT_FRACTION = 0.10

    PROFILE_MAX_FACTOR = 2.30
    PROFILE_MAX_EXTRA_M = 8.0
    PROFILE_MIN_SEARCH_M = 4.0

    MIN_DESCENT_SLOPE = 0.006
    REBOUND_RISE_M = 1.40
    REBOUND_STEPS = 2

    EDGE_DROP_WEIGHT = 1.7
    SHOULDER_CURVATURE_WEIGHT = 1.3
    EDGE_HEIGHT_RATIO_LOW = 0.04
    EDGE_HEIGHT_RATIO_HIGH = 0.45
    EDGE_HEIGHT_BAND_BONUS = 1.5

    COMPETING_APEX_SEARCH_FACTOR = 1.40
    COMPETING_APEX_EXTRA_M = 2.5
    COMPETING_APEX_MIN_RELATIVE_HEIGHT = 0.45
    OWNERSHIP_MARGIN = 0.40

    SEED_RADIUS_PENALTY = 0.08
    LOW_OUTSIDE_PENALTY = 0.55
    PROFILE_COMPETITOR_PENALTY = 0.50

    SMOOTH_PROFILE_PASSES = 3
    SMOOTH_RADIUS_PASSES = 2
    SMOOTH_RADIUS_WINDOW = 2

elif CANOPY_MODE == "MIXED":
    MIN_CANOPY_HEIGHT_M = 1.2
    CENTER_HEIGHT_FRACTION = 0.10

    INNER_SUPPORT_FRACTION = 0.16

    PROFILE_MAX_FACTOR = 1.90
    PROFILE_MAX_EXTRA_M = 5.0
    PROFILE_MIN_SEARCH_M = 3.0

    MIN_DESCENT_SLOPE = 0.010
    REBOUND_RISE_M = 1.10
    REBOUND_STEPS = 2

    EDGE_DROP_WEIGHT = 1.9
    SHOULDER_CURVATURE_WEIGHT = 1.4
    EDGE_HEIGHT_RATIO_LOW = 0.06
    EDGE_HEIGHT_RATIO_HIGH = 0.35
    EDGE_HEIGHT_BAND_BONUS = 1.6

    COMPETING_APEX_SEARCH_FACTOR = 1.60
    COMPETING_APEX_EXTRA_M = 3.0
    COMPETING_APEX_MIN_RELATIVE_HEIGHT = 0.35
    OWNERSHIP_MARGIN = 0.28

    SEED_RADIUS_PENALTY = 0.08
    LOW_OUTSIDE_PENALTY = 0.55
    PROFILE_COMPETITOR_PENALTY = 0.90

    SMOOTH_PROFILE_PASSES = 3
    SMOOTH_RADIUS_PASSES = 2
    SMOOTH_RADIUS_WINDOW = 2

else:
    raise ValueError("CANOPY_MODE must be 'DENSE', 'SPARSE', or 'MIXED'")


# ============================================================
# HELPERS
# ============================================================

def get_layer(name):
    layers = QgsProject.instance().mapLayersByName(name)
    return layers[0] if layers else None


def safe_set_attr(feat, field_name, value):
    idx = feat.fields().indexOf(field_name)
    if idx != -1:
        feat[field_name] = value


def layer_has_field(layer, field_name):
    return layer.fields().indexOf(field_name) != -1


def transform_point(point_xy, src_crs, dst_crs):
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
        pass
    return None


def is_probable_ortho_layer(raster_layer):
    if not isinstance(raster_layer, QgsRasterLayer):
        return False

    src = (raster_layer.source() or "").lower()
    name = (raster_layer.name() or "").lower()
    provider = (raster_layer.providerType() or "").lower()

    if raster_layer.name().lower() == CHM_LAYER_NAME.lower():
        return False

    bad_tokens = [
        "google", "xyz", "wmts", "wms", "tiles", "arcgisonline",
        "openstreetmap", "mapbox", "bing", "esri"
    ]
    if any(t in src for t in bad_tokens) or any(t in name for t in bad_tokens):
        return False

    if provider != "gdal":
        return False

    good_exts = [".tif", ".tiff", ".vrt", ".img", ".jp2"]
    if not any(src.endswith(ext) for ext in good_exts):
        return False

    return True


def median(values):
    if not values:
        return None
    s = sorted(values)
    n = len(s)
    mid = n // 2
    if n % 2 == 1:
        return s[mid]
    return (s[mid - 1] + s[mid]) / 2.0


def gaussian_kernel(radius, sigma):
    vals = []
    for k in range(-radius, radius + 1):
        vals.append(math.exp(-(k * k) / (2.0 * sigma * sigma)))
    s = sum(vals)
    return [v / s for v in vals]


def circular_gaussian_smooth(values, radius=3, sigma=1.5, passes=2):
    if not values:
        return []
    kernel = gaussian_kernel(radius, sigma)
    out = list(values)
    n = len(out)

    for _ in range(passes):
        tmp = []
        for i in range(n):
            acc = 0.0
            for kk, w in zip(range(-radius, radius + 1), kernel):
                acc += out[(i + kk) % n] * w
            tmp.append(acc)
        out = tmp
    return out


def circular_moving_average(values, window):
    window = int(round(window))
    if window <= 0:
        return list(values)

    n = len(values)
    out = []
    for i in range(n):
        vals = []
        for k in range(-window, window + 1):
            vals.append(values[(i + k) % n])
        out.append(sum(vals) / len(vals))
    return out


# ============================================================
# TOOL
# ============================================================

class CanopyCrownProfileTool(QgsMapTool):
    def __init__(self, canvas, target_layer):
        super().__init__(canvas)
        self.canvas = canvas
        self.target_layer = target_layer
        self.project_crs = self.canvas.mapSettings().destinationCrs()

        self.chm_layer = get_layer(CHM_LAYER_NAME)

        self.is_holding = False
        self.center_project = None
        self.current_radius_m = 0.0
        self.last_mouse_project = None

        self.timer = QTimer()
        self.timer.timeout.connect(self.grow_circle)

        self.preview_rb = QgsRubberBand(self.canvas, QgsWkbTypes.PolygonGeometry)
        self.preview_rb.setStrokeColor(QColor(0, 255, 255, 220))
        self.preview_rb.setFillColor(QColor(0, 255, 255, 40))
        self.preview_rb.setWidth(2)
        self.preview_rb.hide()

    def activate(self):
        super().activate()
        self.canvas.setFocus()

        if self.chm_layer:
            iface.messageBar().pushInfo(
                "Canopy Crown Tool",
                f"Mode: {CANOPY_MODE}. Tap or press-hold near canopy apex. Esc exits."
            )
        else:
            iface.messageBar().pushInfo(
                "Canopy Crown Tool",
                "CHM layer not found. Tool will only create rough circles. Esc exits."
            )

    def deactivate(self):
        self.stop_hold()
        self.preview_rb.hide()
        super().deactivate()

    def keyPressEvent(self, event):
        if event.key() == Qt.Key.Key_Escape:
            self.stop_hold()
            self.preview_rb.hide()
            self.canvas.unsetMapTool(self)
        else:
            super().keyPressEvent(event)

    def canvasPressEvent(self, event):
        if event.button() != Qt.MouseButton.LeftButton:
            return

        if not self.target_layer.isEditable():
            QMessageBox.warning(None, "Layer not editable", "Turn editing on for the target canopy polygon layer.")
            return

        self.center_project = self.toMapCoordinates(event.pos())
        self.last_mouse_project = self.center_project
        self.current_radius_m = START_RADIUS_M
        self.is_holding = True
        self.refresh_preview()
        self.timer.start(TIMER_INTERVAL_MS)

    def canvasMoveEvent(self, event):
        if not self.is_holding or self.center_project is None:
            return

        self.last_mouse_project = self.toMapCoordinates(event.pos())
        drag_radius = self.distance_map_units(self.center_project, self.last_mouse_project)

        if drag_radius > self.current_radius_m:
            self.current_radius_m = min(drag_radius, MAX_RADIUS_M)
            self.refresh_preview()

    def canvasReleaseEvent(self, event):
        if event.button() != Qt.MouseButton.LeftButton:
            return

        if not self.is_holding or self.center_project is None:
            return

        self.timer.stop()

        seed_radius = self.current_radius_m
        center_project = self.center_project
        center_target = transform_point(center_project, self.project_crs, self.target_layer.crs())

        ortho_layer = self.find_ortho_under_point(center_project) if FILL_ORTHO_ID else None

        if self.chm_layer:
            center_chm = transform_point(center_project, self.project_crs, self.chm_layer.crs())
            geom_target = self.build_crown_profile_geometry(
                center_target=center_target,
                center_chm=center_chm,
                seed_radius=seed_radius
            )
            refined_flag = 1
        else:
            geom_target = self.make_circle_geometry(center_target, seed_radius, 72)
            refined_flag = 0

        feat = QgsFeature(self.target_layer.fields())
        feat.setGeometry(geom_target)

        next_fid = self.get_next_fid()
        if next_fid is not None:
            safe_set_attr(feat, "fid", next_fid)

        safe_set_attr(feat, "radius_m", round(seed_radius, 2))
        safe_set_attr(feat, "diam_m", round(seed_radius * 2.0, 2))
        safe_set_attr(feat, "area_m2", round(geom_target.area(), 2))
        safe_set_attr(feat, "refined", refined_flag)

        if ortho_layer:
            safe_set_attr(feat, "ortho_id", ortho_layer.source())

        ok = self.target_layer.addFeature(feat)
        if ok:
            self.target_layer.updateExtents()
            self.target_layer.triggerRepaint()
            self.canvas.refresh()

            try:
                self.target_layer.removeSelection()
                self.target_layer.selectByIds([feat.id()])
            except Exception:
                pass

            iface.messageBar().pushInfo(
                "Canopy Crown Tool",
                f"Canopy polygon added. fid={next_fid if next_fid is not None else 'n/a'}"
            )
        else:
            QMessageBox.warning(None, "Add feature failed", "Could not add the canopy polygon to the layer.")

        self.stop_hold()
        self.preview_rb.hide()

    def find_ortho_under_point(self, center_project):
        root = QgsProject.instance().layerTreeRoot()
        layer_order = root.layerOrder()

        for lyr in layer_order:
            if not isinstance(lyr, QgsRasterLayer):
                continue
            if not is_probable_ortho_layer(lyr):
                continue

            center_lyr = transform_point(center_project, self.project_crs, lyr.crs())
            if lyr.extent().contains(center_lyr):
                return lyr

        return None

    def build_crown_profile_geometry(self, center_target, center_chm, seed_radius):
        chm = self.chm_layer

        try:
            px = abs(chm.rasterUnitsPerPixelX())
            py = abs(chm.rasterUnitsPerPixelY())
            cell = max(px, py)
        except Exception:
            cell = 1.0

        cell = max(MIN_GRID_SIZE_M, min(MAX_GRID_SIZE_M, cell))

        apex_pt, apex_val = self.find_local_apex(center_chm, LOCAL_APEX_SEARCH_RADIUS_M, cell)
        if apex_pt is None or apex_val is None:
            return self.make_circle_geometry(center_target, seed_radius, 72)

        threshold = self.inner_support_threshold(apex_pt, apex_val, seed_radius, cell)

        competing_search_radius = max(seed_radius * COMPETING_APEX_SEARCH_FACTOR, seed_radius + COMPETING_APEX_EXTRA_M)
        competing_apexes = self.find_competing_apexes(apex_pt, apex_val, competing_search_radius, cell, threshold)

        radii = self.infer_crown_radii(
            apex_pt=apex_pt,
            apex_val=apex_val,
            seed_radius=seed_radius,
            threshold=threshold,
            competing_apexes=competing_apexes
        )

        # first a light circular moving average
        for _ in range(int(SMOOTH_RADIUS_PASSES)):
            radii = circular_moving_average(radii, SMOOTH_RADIUS_WINDOW)

        # then Gaussian smoothing for crown-like perimeter
        radii = circular_gaussian_smooth(
            radii,
            radius=GAUSSIAN_SMOOTH_RADIUS,
            sigma=GAUSSIAN_SMOOTH_SIGMA,
            passes=GAUSSIAN_SMOOTH_PASSES
        )

        geom = self.radii_to_polygon_geometry(
            apex_pt=apex_pt,
            radii=radii,
            source_crs=self.chm_layer.crs(),
            target_crs=self.target_layer.crs()
        )

        if geom is None or geom.isEmpty():
            return self.make_circle_geometry(center_target, seed_radius, 72)

        try:
            geom = geom.buffer(FINAL_BUFFER_SMOOTH_M, 16).buffer(-FINAL_BUFFER_SMOOTH_M, 16)
        except Exception:
            pass

        if geom is None or geom.isEmpty():
            return self.make_circle_geometry(center_target, seed_radius, 72)

        return geom

    def radii_to_polygon_geometry(self, apex_pt, radii, source_crs, target_crs):
        pts = []
        n = len(radii)
        if n < 8:
            return None

        for i, r in enumerate(radii):
            angle = (2.0 * math.pi * i) / n
            x = apex_pt.x() + r * math.cos(angle)
            y = apex_pt.y() + r * math.sin(angle)
            pts.append(QgsPointXY(x, y))

        pts.append(pts[0])

        geom = QgsGeometry.fromPolygonXY([pts])

        if source_crs != target_crs:
            try:
                tr = QgsCoordinateTransform(source_crs, target_crs, QgsProject.instance())
                geom.transform(tr)
            except Exception:
                return None

        return geom

    def inner_support_threshold(self, apex_pt, apex_val, seed_radius, step):
        radius = max(INNER_SUPPORT_RADIUS_MIN_M, seed_radius * INNER_SUPPORT_RADIUS_FACTOR)
        vals = self.sample_ring(apex_pt, radius, step)
        med = median(vals)

        candidates = [MIN_CANOPY_HEIGHT_M, apex_val * CENTER_HEIGHT_FRACTION]
        if med is not None:
            candidates.append(med * INNER_SUPPORT_FRACTION)
        return max(candidates)

    def ownership_score(self, pt, val, apex_pt, apex_val):
        d = self.distance_xy(pt, apex_pt)
        drop = max(0.0, apex_val - val)
        return val - OWNERSHIP_DISTANCE_WEIGHT * d - OWNERSHIP_DROP_WEIGHT * drop

    def competitor_penalty(self, pt, val, apex_pt, apex_val, competing_apexes):
        target_score = self.ownership_score(pt, val, apex_pt, apex_val)

        best_other = None
        for c_pt, c_val in competing_apexes:
            if self.distance_xy(c_pt, apex_pt) < 1e-6:
                continue
            s = self.ownership_score(pt, val, c_pt, c_val)
            if best_other is None or s > best_other:
                best_other = s

        if best_other is None:
            return 0.0

        exceed = best_other - (target_score + OWNERSHIP_MARGIN)
        return max(0.0, exceed)

    def find_competing_apexes(self, apex_pt, apex_val, search_radius, step, threshold):
        candidates = []
        xmin = apex_pt.x() - search_radius
        xmax = apex_pt.x() + search_radius
        ymin = apex_pt.y() - search_radius
        ymax = apex_pt.y() + search_radius

        x = xmin
        while x <= xmax + 1e-9:
            y = ymin
            while y <= ymax + 1e-9:
                pt = QgsPointXY(x, y)
                if self.distance_xy(pt, apex_pt) <= search_radius:
                    v = sample_raster_value(self.chm_layer, pt, 1)
                    if v is not None and v >= threshold and v >= apex_val * COMPETING_APEX_MIN_RELATIVE_HEIGHT:
                        candidates.append((pt, v))
                y += step
            x += step

        candidates.sort(key=lambda t: t[1], reverse=True)

        apexes = []
        for pt, val in candidates:
            keep = True
            for a_pt, _ in apexes:
                if self.distance_xy(pt, a_pt) < COMPETING_APEX_MIN_SEPARATION_M:
                    keep = False
                    break
            if keep:
                apexes.append((pt, val))

        has_target = any(self.distance_xy(apex_pt, a_pt) < 1e-6 for a_pt, _ in apexes)
        if not has_target:
            apexes.insert(0, (apex_pt, apex_val))

        return apexes

    def infer_crown_radii(self, apex_pt, apex_val, seed_radius, threshold, competing_apexes):
        max_search = max(PROFILE_MIN_SEARCH_M, seed_radius * PROFILE_MAX_FACTOR + PROFILE_MAX_EXTRA_M)
        radii = []

        for i in range(NUM_ANGLES):
            angle = (2.0 * math.pi * i) / NUM_ANGLES
            rs, vals = self.sample_profile(apex_pt, angle, max_search, PROFILE_STEP_M)

            if len(vals) < 6:
                radii.append(seed_radius)
                continue

            smooth_vals = list(vals)
            for _ in range(int(SMOOTH_PROFILE_PASSES)):
                smooth_vals = self.simple_line_smooth(smooth_vals)

            slopes = self.compute_first_derivative(smooth_vals, PROFILE_STEP_M)
            curvs = self.compute_second_derivative(smooth_vals, PROFILE_STEP_M)

            best_score = -1e18
            best_r = seed_radius
            rebound_count = 0

            for j in range(2, len(smooth_vals) - 2):
                rj = rs[j]
                hj = smooth_vals[j]
                s_now = slopes[j]
                c_now = curvs[j]

                if hj < threshold * 0.40:
                    break

                if s_now > REBOUND_RISE_M:
                    rebound_count += 1
                else:
                    rebound_count = 0

                outside_h = smooth_vals[j + 1]
                edge_drop = max(0.0, hj - outside_h)
                curvature_signal = abs(c_now)

                h_ratio = hj / max(apex_val, 0.001)
                band_bonus = 0.0
                if EDGE_HEIGHT_RATIO_LOW <= h_ratio <= EDGE_HEIGHT_RATIO_HIGH:
                    center_of_band = (EDGE_HEIGHT_RATIO_LOW + EDGE_HEIGHT_RATIO_HIGH) / 2.0
                    band_bonus = EDGE_HEIGHT_BAND_BONUS * (
                        1.0 - abs(h_ratio - center_of_band) / max(center_of_band, 0.001)
                    )
                    band_bonus = max(0.0, band_bonus)

                score = 0.0
                score += EDGE_DROP_WEIGHT * edge_drop
                score += SHOULDER_CURVATURE_WEIGHT * curvature_signal
                score += band_bonus
                score -= SEED_RADIUS_PENALTY * abs(rj - seed_radius)
                score -= LOW_OUTSIDE_PENALTY * max(0.0, threshold * 0.40 - outside_h)

                if s_now < -MIN_DESCENT_SLOPE:
                    score += 0.5 * abs(s_now)

                cand_pt = QgsPointXY(
                    apex_pt.x() + rj * math.cos(angle),
                    apex_pt.y() + rj * math.sin(angle)
                )
                comp_pen = self.competitor_penalty(cand_pt, hj, apex_pt, apex_val, competing_apexes)
                score -= PROFILE_COMPETITOR_PENALTY * comp_pen

                if rebound_count >= REBOUND_STEPS and comp_pen > 0.35:
                    break

                if score > best_score:
                    best_score = score
                    best_r = rj

            if best_score < -1e10:
                last_good = seed_radius
                for rj, hj in zip(rs, smooth_vals):
                    if hj >= threshold * 0.40:
                        last_good = rj
                best_r = last_good

            radii.append(best_r)

        return radii

    def sample_profile(self, apex_pt, angle, max_search, step):
        rs = []
        vals = []
        r = step
        while r <= max_search + 1e-9:
            x = apex_pt.x() + r * math.cos(angle)
            y = apex_pt.y() + r * math.sin(angle)
            pt = QgsPointXY(x, y)
            v = sample_raster_value(self.chm_layer, pt, 1)
            if v is None:
                break
            rs.append(r)
            vals.append(v)
            r += step
        return rs, vals

    def compute_first_derivative(self, vals, step):
        n = len(vals)
        out = [0.0] * n
        if n < 2:
            return out
        out[0] = (vals[1] - vals[0]) / step
        out[-1] = (vals[-1] - vals[-2]) / step
        for i in range(1, n - 1):
            out[i] = (vals[i + 1] - vals[i - 1]) / (2.0 * step)
        return out

    def compute_second_derivative(self, vals, step):
        n = len(vals)
        out = [0.0] * n
        if n < 3:
            return out
        for i in range(1, n - 1):
            out[i] = (vals[i + 1] - 2.0 * vals[i] + vals[i - 1]) / (step * step)
        return out

    def simple_line_smooth(self, arr):
        if len(arr) < 3:
            return list(arr)
        out = [arr[0]]
        for i in range(1, len(arr) - 1):
            out.append((arr[i - 1] + arr[i] + arr[i + 1]) / 3.0)
        out.append(arr[-1])
        return out

    def sample_ring(self, center_pt, radius, step):
        vals = []
        xmin = center_pt.x() - radius
        xmax = center_pt.x() + radius
        ymin = center_pt.y() - radius
        ymax = center_pt.y() + radius

        x = xmin
        while x <= xmax + 1e-9:
            y = ymin
            while y <= ymax + 1e-9:
                pt = QgsPointXY(x, y)
                if self.distance_xy(pt, center_pt) <= radius:
                    v = sample_raster_value(self.chm_layer, pt, 1)
                    if v is not None:
                        vals.append(v)
                y += step
            x += step

        return vals

    def find_local_apex(self, center_chm, search_radius, step):
        best_pt = None
        best_val = None

        xmin = center_chm.x() - search_radius
        xmax = center_chm.x() + search_radius
        ymin = center_chm.y() - search_radius
        ymax = center_chm.y() + search_radius

        x = xmin
        while x <= xmax + 1e-9:
            y = ymin
            while y <= ymax + 1e-9:
                pt = QgsPointXY(x, y)
                if self.distance_xy(pt, center_chm) <= search_radius:
                    v = sample_raster_value(self.chm_layer, pt, 1)
                    if v is not None:
                        if best_val is None or v > best_val:
                            best_val = v
                            best_pt = pt
                y += step
            x += step

        return best_pt, best_val

    def get_next_fid(self):
        if not layer_has_field(self.target_layer, "fid"):
            return None

        max_fid = 0
        for f in self.target_layer.getFeatures():
            try:
                val = f["fid"]
                if val is None:
                    continue
                num = int(val)
                if num > max_fid:
                    max_fid = num
            except Exception:
                continue

        return max_fid + 1

    def grow_circle(self):
        if not self.is_holding or self.center_project is None:
            return

        self.current_radius_m += GROWTH_PER_TICK_M
        if self.current_radius_m > MAX_RADIUS_M:
            self.current_radius_m = MAX_RADIUS_M

        self.refresh_preview()

    def stop_hold(self):
        self.timer.stop()
        self.is_holding = False
        self.center_project = None
        self.last_mouse_project = None
        self.current_radius_m = 0.0

    def distance_map_units(self, p1, p2):
        dx = p2.x() - p1.x()
        dy = p2.y() - p1.y()
        return math.sqrt(dx * dx + dy * dy)

    def distance_xy(self, p1, p2):
        dx = p2.x() - p1.x()
        dy = p2.y() - p1.y()
        return math.sqrt(dx * dx + dy * dy)

    def make_circle_geometry(self, center_xy, radius_m, segments=72):
        pts = []
        for i in range(segments + 1):
            a = (2.0 * math.pi * i) / segments
            x = center_xy.x() + radius_m * math.cos(a)
            y = center_xy.y() + radius_m * math.sin(a)
            pts.append(QgsPointXY(x, y))
        return QgsGeometry.fromPolygonXY([pts])

    def refresh_preview(self):
        if self.center_project is None:
            return

        center_target = transform_point(
            self.center_project,
            self.project_crs,
            self.target_layer.crs()
        )
        geom_target = self.make_circle_geometry(center_target, self.current_radius_m, 72)
        self.preview_rb.setToGeometry(geom_target, self.target_layer)
        self.preview_rb.show()


def get_active_polygon_layer():
    lyr = iface.activeLayer()
    if lyr is None or not isinstance(lyr, QgsVectorLayer):
        QMessageBox.warning(None, "No active polygon layer", "Select your canopy polygon layer first.")
        return None
    if lyr.geometryType() != Qgis.GeometryType.Polygon:
        QMessageBox.warning(None, "Wrong layer type", "The active layer must be a polygon layer.")
        return None
    return lyr


target = get_active_polygon_layer()
if target:
    iface.canopy_crown_profile_tool = CanopyCrownProfileTool(canvas, target)
    canvas.setMapTool(iface.canopy_crown_profile_tool)