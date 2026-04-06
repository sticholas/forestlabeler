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
from collections import deque

canvas = iface.mapCanvas()

# ============================================================
# CONFIG
# ============================================================

CHM_LAYER_NAME = "chm"

# Seed growth
START_RADIUS_M = 0.75
MAX_RADIUS_M = 35.0
GROWTH_PER_TICK_M = 0.35
TIMER_INTERVAL_MS = 60

# Apex search
LOCAL_APEX_SEARCH_RADIUS_M = 2.0

# Crown profile inference
NUM_ANGLES = 72
PROFILE_STEP_M = 0.35
PROFILE_MAX_FACTOR = 1.85
PROFILE_MAX_EXTRA_M = 4.0
PROFILE_MIN_SEARCH_M = 3.0

# Hard canopy support thresholds
MIN_CANOPY_HEIGHT_M = 2.0
CENTER_HEIGHT_FRACTION = 0.20

# Crown-curve logic
SMOOTH_PROFILE_PASSES = 3
SLOPE_WINDOW = 1
MIN_DESCENT_SLOPE = 0.03          # minimum expected outward decline
REBOUND_RISE_M = 0.90             # outward rise this strong suggests another tree
REBOUND_STEPS = 2                 # consecutive outward rising steps to trigger stop
SHOULDER_CURVATURE_WEIGHT = 1.8   # favors crown shoulder / edge zone
EDGE_DROP_WEIGHT = 2.2            # favors strong outward drop
SEED_RADIUS_PENALTY = 0.20        # keeps inferred radius near seed unless CHM says otherwise
LOW_OUTSIDE_PENALTY = 1.8         # penalize continuing into low-value outside canopy

# Envelope + connected component
ENVELOPE_MARGIN_FACTOR = 1.10
MIN_CONNECTED_PIXELS = 4

# Geometry cleanup
SMOOTH_RADIUS_PASSES = 4
SMOOTH_RADIUS_WINDOW = 2
BUFFER_SMOOTH_FACTOR = 0.35
SIMPLIFY_FACTOR = 0.12

# Grid sizing
MIN_GRID_SIZE_M = 0.25
MAX_GRID_SIZE_M = 1.50

# Metadata
FILL_ORTHO_ID = True


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


def circular_moving_average(values, window):
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


def largest_part(geom):
    if geom is None or geom.isEmpty():
        return geom
    if not geom.isMultipart():
        return geom

    polys = geom.asMultiPolygon()
    if not polys:
        return geom

    best = None
    best_area = -1
    for poly in polys:
        g = QgsGeometry.fromPolygonXY(poly)
        a = g.area()
        if a > best_area:
            best_area = a
            best = g
    return best if best is not None else geom


def remove_holes(geom):
    if geom is None or geom.isEmpty():
        return geom

    try:
        if geom.isMultipart():
            parts = geom.asMultiPolygon()
            out_geoms = []
            for poly in parts:
                if poly and len(poly) > 0:
                    outer = poly[0]
                    out_geoms.append(QgsGeometry.fromPolygonXY([outer]))
            if not out_geoms:
                return geom
            merged = QgsGeometry.unaryUnion(out_geoms)
            return largest_part(merged)
        else:
            poly = geom.asPolygon()
            if poly and len(poly) > 0:
                return QgsGeometry.fromPolygonXY([poly[0]])
    except Exception:
        pass

    return geom


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

    # --------------------------------------------------------
    # UI
    # --------------------------------------------------------
    def activate(self):
        super().activate()
        self.canvas.setFocus()

        if self.chm_layer:
            iface.messageBar().pushInfo(
                "Canopy Crown Tool",
                "Press and hold to grow seed. Release to delineate canopy from CHM crown curvature. Esc exits."
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

    # --------------------------------------------------------
    # ORTHO LOOKUP
    # --------------------------------------------------------
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

    # --------------------------------------------------------
    # MAIN GEOMETRY LOGIC
    # --------------------------------------------------------
    def build_crown_profile_geometry(self, center_target, center_chm, seed_radius):
        chm = self.chm_layer

        # CHM grid size
        try:
            px = abs(chm.rasterUnitsPerPixelX())
            py = abs(chm.rasterUnitsPerPixelY())
            cell = max(px, py)
        except Exception:
            cell = 1.0

        cell = max(MIN_GRID_SIZE_M, min(MAX_GRID_SIZE_M, cell))

        # local apex
        apex_pt, apex_val = self.find_local_apex(center_chm, LOCAL_APEX_SEARCH_RADIUS_M, cell)
        if apex_pt is None or apex_val is None:
            return self.make_circle_geometry(center_target, seed_radius, 72)

        threshold = max(MIN_CANOPY_HEIGHT_M, apex_val * CENTER_HEIGHT_FRACTION)

        # infer directional radii from radial crown profiles
        radii = self.infer_crown_radii(apex_pt, apex_val, seed_radius, threshold)

        # smooth the envelope so neighboring angles are biologically plausible
        for _ in range(SMOOTH_RADIUS_PASSES):
            radii = circular_moving_average(radii, SMOOTH_RADIUS_WINDOW)

        max_env = max(radii) if radii else seed_radius
        search_radius = max_env * ENVELOPE_MARGIN_FACTOR

        xmin = apex_pt.x() - search_radius
        xmax = apex_pt.x() + search_radius
        ymin = apex_pt.y() - search_radius
        ymax = apex_pt.y() + search_radius

        nx = int(math.ceil((xmax - xmin) / cell))
        ny = int(math.ceil((ymax - ymin) / cell))

        values = {}
        for ix in range(nx):
            x = xmin + (ix + 0.5) * cell
            for iy in range(ny):
                y = ymin + (iy + 0.5) * cell
                pt = QgsPointXY(x, y)

                d = self.distance_xy(pt, apex_pt)
                if d > search_radius:
                    continue

                # envelope gate
                if d > self.max_radius_for_point(pt, apex_pt, radii) * ENVELOPE_MARGIN_FACTOR:
                    continue

                v = sample_raster_value(chm, pt, 1)
                if v is None:
                    continue

                values[(ix, iy)] = v

        if not values:
            return self.make_circle_geometry(center_target, seed_radius, 72)

        # nearest seed cell above threshold
        seed_cell = None
        best_seed_dist = 1e18
        for (ix, iy), v in values.items():
            if v < threshold:
                continue
            x = xmin + (ix + 0.5) * cell
            y = ymin + (iy + 0.5) * cell
            d = math.hypot(x - apex_pt.x(), y - apex_pt.y())
            if d < best_seed_dist:
                best_seed_dist = d
                seed_cell = (ix, iy)

        if seed_cell is None:
            return self.make_circle_geometry(center_target, seed_radius, 72)

        included = self.connected_component(values, seed_cell, threshold, xmin, ymin, cell, apex_pt, radii)

        if len(included) < MIN_CONNECTED_PIXELS:
            return self.make_circle_geometry(center_target, seed_radius, 72)

        geoms = []
        for (ix, iy) in included:
            x0 = xmin + ix * cell
            x1 = x0 + cell
            y0 = ymin + iy * cell
            y1 = y0 + cell

            rect = [
                QgsPointXY(x0, y0),
                QgsPointXY(x1, y0),
                QgsPointXY(x1, y1),
                QgsPointXY(x0, y1),
                QgsPointXY(x0, y0),
            ]
            geoms.append(QgsGeometry.fromPolygonXY([rect]))

        if not geoms:
            return self.make_circle_geometry(center_target, seed_radius, 72)

        try:
            merged = QgsGeometry.unaryUnion(geoms)
        except Exception:
            merged = geoms[0]
            for g in geoms[1:]:
                merged = merged.combine(g)

        merged = largest_part(merged)
        merged = remove_holes(merged)

        if merged is None or merged.isEmpty():
            return self.make_circle_geometry(center_target, seed_radius, 72)

        # light cleanup
        smooth_dist = cell * BUFFER_SMOOTH_FACTOR
        simplify_dist = cell * SIMPLIFY_FACTOR

        try:
            merged = merged.buffer(smooth_dist, 8).buffer(-smooth_dist, 8)
        except Exception:
            pass

        merged = remove_holes(merged)

        try:
            merged = merged.simplify(simplify_dist)
        except Exception:
            pass

        merged = remove_holes(merged)

        if merged is None or merged.isEmpty():
            return self.make_circle_geometry(center_target, seed_radius, 72)

        if self.chm_layer.crs() != self.target_layer.crs():
            try:
                tr = QgsCoordinateTransform(self.chm_layer.crs(), self.target_layer.crs(), QgsProject.instance())
                merged.transform(tr)
            except Exception:
                return self.make_circle_geometry(center_target, seed_radius, 72)

        return merged

    # --------------------------------------------------------
    # CROWN PROFILE INFERENCE
    # --------------------------------------------------------
    def infer_crown_radii(self, apex_pt, apex_val, seed_radius, threshold):
        """
        For each angle:
        - sample outward height profile
        - smooth it
        - compute slope and curvature
        - find likely crown edge before a rebound into another tree
        """
        max_search = max(PROFILE_MIN_SEARCH_M, seed_radius * PROFILE_MAX_FACTOR + PROFILE_MAX_EXTRA_M)
        radii = []

        for i in range(NUM_ANGLES):
            angle = (2.0 * math.pi * i) / NUM_ANGLES
            rs, vals = self.sample_profile(apex_pt, angle, max_search, PROFILE_STEP_M)

            if len(vals) < 6:
                radii.append(seed_radius)
                continue

            smooth_vals = list(vals)
            for _ in range(SMOOTH_PROFILE_PASSES):
                smooth_vals = self.simple_line_smooth(smooth_vals)

            slopes = self.compute_first_derivative(smooth_vals, PROFILE_STEP_M)
            curvs = self.compute_second_derivative(smooth_vals, PROFILE_STEP_M)

            best_score = -1e18
            best_r = seed_radius
            rebound_count = 0

            for j in range(2, len(smooth_vals) - 2):
                rj = rs[j]
                hj = smooth_vals[j]
                s_prev = slopes[j - 1]
                s_now = slopes[j]
                c_now = curvs[j]

                if hj < threshold:
                    break

                if apex_val > 0 and hj < (apex_val * CENTER_HEIGHT_FRACTION):
                    break

                # detect rebound = slope becomes positive after decline
                if s_now > REBOUND_RISE_M:
                    rebound_count += 1
                else:
                    rebound_count = 0

                if rebound_count >= REBOUND_STEPS:
                    break

                # crown-edge score:
                # - prefer meaningful outward decline
                # - prefer a shoulder / change in curvature
                # - penalize far departure from seed
                # - penalize low outside support
                outside_h = smooth_vals[j + 1]
                edge_drop = max(0.0, hj - outside_h)
                curvature_signal = abs(c_now)

                score = 0.0
                score += EDGE_DROP_WEIGHT * edge_drop
                score += SHOULDER_CURVATURE_WEIGHT * curvature_signal
                score -= SEED_RADIUS_PENALTY * abs(rj - seed_radius)
                score -= LOW_OUTSIDE_PENALTY * max(0.0, threshold - outside_h)

                # favor natural outward decline, disfavor flat or rising profiles
                if s_now < -MIN_DESCENT_SLOPE:
                    score += 0.8 * abs(s_now)
                elif s_now > 0:
                    score -= 2.0 * s_now

                if score > best_score:
                    best_score = score
                    best_r = rj

            # fallback: last good support above threshold
            if best_score < -1e10:
                last_good = seed_radius
                for rj, hj in zip(rs, smooth_vals):
                    if hj >= threshold:
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

    def max_radius_for_point(self, pt, apex_pt, radii):
        dx = pt.x() - apex_pt.x()
        dy = pt.y() - apex_pt.y()
        angle = math.atan2(dy, dx)
        if angle < 0:
            angle += 2.0 * math.pi

        idx_f = angle / (2.0 * math.pi) * len(radii)
        i0 = int(math.floor(idx_f)) % len(radii)
        i1 = (i0 + 1) % len(radii)
        t = idx_f - math.floor(idx_f)

        return radii[i0] * (1.0 - t) + radii[i1] * t

    def connected_component(self, values, seed_cell, threshold, xmin, ymin, cell, apex_pt, radii):
        q = deque([seed_cell])
        visited = set([seed_cell])
        included = set()

        while q:
            cell_ixiy = q.popleft()
            v = values.get(cell_ixiy, None)
            if v is None or v < threshold:
                continue

            ix, iy = cell_ixiy
            cx = xmin + (ix + 0.5) * cell
            cy = ymin + (iy + 0.5) * cell
            pt = QgsPointXY(cx, cy)

            if self.distance_xy(pt, apex_pt) > self.max_radius_for_point(pt, apex_pt, radii) * ENVELOPE_MARGIN_FACTOR:
                continue

            included.add(cell_ixiy)

            for dx in (-1, 0, 1):
                for dy in (-1, 0, 1):
                    if dx == 0 and dy == 0:
                        continue
                    nb = (ix + dx, iy + dy)
                    if nb in visited:
                        continue
                    if nb not in values:
                        continue
                    visited.add(nb)
                    if values[nb] >= threshold:
                        q.append(nb)

        return included

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

    # --------------------------------------------------------
    # IDS
    # --------------------------------------------------------
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

    # --------------------------------------------------------
    # PREVIEW / GEOMETRY
    # --------------------------------------------------------
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