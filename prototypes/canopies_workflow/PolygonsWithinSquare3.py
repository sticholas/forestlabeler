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
CANOPY_OUTPUT_LAYER_NAME = "training_canopies"
CHM_LAYER_NAME = "chm"

# Choose one: "DENSE", "SPARSE", "MIXED"
CANOPY_MODE = "DENSE"

# ============================================================
# CRASH-SAFE LIMITS
# ============================================================

MAX_TOTAL_CANDIDATES = 220
MAX_FINAL_CANOPIES = 120

# processing grid
MIN_GRID_SIZE_M = 1.0
MAX_GRID_SIZE_M = 1.5

# ============================================================
# PROPOSAL STAGE
# ============================================================

APEX_SCALES_M = [1.5, 3.0, 4.5]
MIN_APEX_HEIGHT_M = 1.0
MIN_PROMINENCE_M = 0.65
MIN_APEX_SEPARATION_M = 2.0
MIN_APEX_NEIGHBOR_SUPPORT_RATIO = 0.40

SECONDARY_APEX_MIN_PROMINENCE = 0.30
SECONDARY_APEX_MIN_SUPPORT = 0.34

# ============================================================
# LIKELIHOOD / OWNERSHIP
# ============================================================

LIKELIHOOD_MIN_HEIGHT_FACTOR = 0.25
LIKELIHOOD_CENTER_WEIGHT = 0.40
LIKELIHOOD_LOCAL_SUPPORT_WEIGHT = 0.35
LIKELIHOOD_RADIAL_SUPPORT_WEIGHT = 0.25
LIKELIHOOD_MIN_SCORE = 0.48

OWNERSHIP_DISTANCE_WEIGHT = 0.18
OWNERSHIP_DROP_WEIGHT = 0.14
OWNERSHIP_MARGIN = 0.16
MAX_OWNERSHIP_RADIUS_FACTOR = 1.05

# ============================================================
# FINAL SHAPE
# ============================================================

NUM_ANGLES = 40
PROFILE_STEP_M = 0.6
MIN_PROFILE_POINTS = 4

GAUSSIAN_SMOOTH_RADIUS = 2
GAUSSIAN_SMOOTH_SIGMA = 1.1
GAUSSIAN_SMOOTH_PASSES = 1

MAX_RADIUS_JUMP_FACTOR = 1.16
MAX_RADIUS_JUMP_M = 0.9

FINAL_SHRINK_PASSES = 1
UNSUPPORTED_RADIUS_SHRINK_FACTOR = 0.90

MIN_CANOPY_AREA_M2 = 5.0
MIN_COMPACTNESS = 0.30
MAX_ELONGATION = 2.6
MIN_SUPPORT_RATIO = 0.52

SKIP_APEX_IF_INSIDE_ACCEPTED = True
ACCEPTED_BUFFER_M = 1.0
MAX_OVERLAP_FRAC_SELF = 0.18
MAX_OVERLAP_FRAC_OTHER = 0.30

# ============================================================
# MODE PRESETS
# ============================================================

if CANOPY_MODE == "DENSE":
    MIN_CANOPY_SUPPORT_M = 1.6
    CENTER_HEIGHT_FRACTION = 0.14
    INNER_SUPPORT_FRACTION = 0.20
    PROFILE_MAX_FACTOR = 1.35
    PROFILE_MAX_EXTRA_M = 2.0
    PROFILE_MIN_SEARCH_M = 2.5
    MIN_DESCENT_SLOPE = 0.020
    REBOUND_RISE_M = 0.65
    EDGE_DROP_WEIGHT = 2.2
    CURVATURE_WEIGHT = 1.6
    EDGE_HEIGHT_RATIO_LOW = 0.08
    EDGE_HEIGHT_RATIO_HIGH = 0.26
    RELAXED_THRESHOLD_FACTOR = 0.58
    RADIAL_COMPETITOR_PENALTY = 1.25

elif CANOPY_MODE == "SPARSE":
    MIN_CANOPY_SUPPORT_M = 0.9
    CENTER_HEIGHT_FRACTION = 0.06
    INNER_SUPPORT_FRACTION = 0.10
    PROFILE_MAX_FACTOR = 1.9
    PROFILE_MAX_EXTRA_M = 5.0
    PROFILE_MIN_SEARCH_M = 4.0
    MIN_DESCENT_SLOPE = 0.007
    REBOUND_RISE_M = 1.2
    EDGE_DROP_WEIGHT = 1.5
    CURVATURE_WEIGHT = 1.2
    EDGE_HEIGHT_RATIO_LOW = 0.04
    EDGE_HEIGHT_RATIO_HIGH = 0.40
    RELAXED_THRESHOLD_FACTOR = 0.70
    RADIAL_COMPETITOR_PENALTY = 0.50
    MIN_SUPPORT_RATIO = 0.42

else:  # MIXED
    MIN_CANOPY_SUPPORT_M = 1.2
    CENTER_HEIGHT_FRACTION = 0.10
    INNER_SUPPORT_FRACTION = 0.16
    PROFILE_MAX_FACTOR = 1.65
    PROFILE_MAX_EXTRA_M = 3.5
    PROFILE_MIN_SEARCH_M = 3.0
    MIN_DESCENT_SLOPE = 0.012
    REBOUND_RISE_M = 0.95
    EDGE_DROP_WEIGHT = 1.9
    CURVATURE_WEIGHT = 1.35
    EDGE_HEIGHT_RATIO_LOW = 0.06
    EDGE_HEIGHT_RATIO_HIGH = 0.32
    RELAXED_THRESHOLD_FACTOR = 0.64
    RADIAL_COMPETITOR_PENALTY = 0.90
    MIN_SUPPORT_RATIO = 0.47


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

def gaussian_kernel(radius, sigma):
    vals = []
    for k in range(-radius, radius + 1):
        vals.append(math.exp(-(k * k) / (2.0 * sigma * sigma)))
    s = sum(vals)
    return [v / s for v in vals]

def circular_gaussian_smooth(values, radius=2, sigma=1.1, passes=1):
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

def polygon_compactness(geom):
    try:
        a = geom.area()
        p = geom.length()
        if p <= 0:
            return 0.0
        return 4.0 * math.pi * a / (p * p)
    except Exception:
        return 0.0

def bbox_elongation(geom):
    try:
        rect = geom.boundingBox()
        w = rect.width()
        h = rect.height()
        mn = max(min(w, h), 1e-6)
        mx = max(w, h)
        return mx / mn
    except Exception:
        return 999.0


# ============================================================
# EXTRACTOR
# ============================================================

class CrashSafeCanopyExtractor:
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

    def classify_candidate(self, pt, val, prom, scale):
        local_threshold = max(MIN_CANOPY_SUPPORT_M, val * LIKELIHOOD_MIN_HEIGHT_FACTOR)
        local_support = self.support_ratio_within_radius(pt, max(scale, 1.5), local_threshold)

        if prom >= MIN_PROMINENCE_M and local_support >= MIN_APEX_NEIGHBOR_SUPPORT_RATIO:
            return "strong", local_support

        if prom >= SECONDARY_APEX_MIN_PROMINENCE and local_support >= SECONDARY_APEX_MIN_SUPPORT:
            return "secondary", local_support

        return None, local_support

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
                cls, local_support = self.classify_candidate(pt, v, prom, scale)
                if cls is None:
                    continue

                class_rank = {"strong": 3, "secondary": 2}[cls]
                candidates.append((pt, v, prom, scale, local_support, cls, class_rank))

        candidates.sort(key=lambda t: (t[6], t[1], t[2], t[4]), reverse=True)

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

    def inner_support_threshold(self, apex_pt, apex_val, seed_radius):
        radius = max(1.0, seed_radius * 0.20)
        vals = self.values_within_radius(apex_pt, radius)
        med = median(vals)
        candidates = [MIN_CANOPY_SUPPORT_M, apex_val * CENTER_HEIGHT_FRACTION]
        if med is not None:
            candidates.append(med * INNER_SUPPORT_FRACTION)
        return max(candidates)

    def ownership_score(self, pt, val, apex_pt, apex_val):
        d = distance_xy(pt, apex_pt)
        drop = max(0.0, apex_val - val)
        return val - OWNERSHIP_DISTANCE_WEIGHT * d - OWNERSHIP_DROP_WEIGHT * drop

    def find_competing_centers(self, apex_pt, apex_val, search_radius, threshold, candidates):
        out = []
        for pt, val, prom, scale, local_support, cls, rank in candidates:
            if distance_xy(pt, apex_pt) <= search_radius and val >= threshold and val >= apex_val * 0.35:
                out.append((pt, val))
        out.sort(key=lambda t: t[1], reverse=True)

        filtered = []
        for pt, val in out:
            keep = True
            for pt2, _ in filtered:
                if distance_xy(pt, pt2) < 1.5:
                    keep = False
                    break
            if keep:
                filtered.append((pt, val))

        if not any(distance_xy(apex_pt, pt2) < 1e-6 for pt2, _ in filtered):
            filtered.insert(0, (apex_pt, apex_val))
        return filtered

    def competitor_penalty(self, pt, val, apex_pt, apex_val, competing):
        target_score = self.ownership_score(pt, val, apex_pt, apex_val)
        best_other = None
        for c_pt, c_val in competing:
            if distance_xy(c_pt, apex_pt) < 1e-6:
                continue
            s = self.ownership_score(pt, val, c_pt, c_val)
            if best_other is None or s > best_other:
                best_other = s
        if best_other is None:
            return 0.0
        return max(0.0, best_other - (target_score + OWNERSHIP_MARGIN))

    def sample_profile(self, apex_pt, angle, max_search):
        rs, vals = [], []
        ax, ay = xy_of(apex_pt)
        r = PROFILE_STEP_M
        while r <= max_search + 1e-9:
            x = ax + r * math.cos(angle)
            y = ay + r * math.sin(angle)
            pt = QgsPointXY(x, y)
            if not point_in_geom(self.square_geom_chm, pt):
                break
            v = sample_raster_value(self.chm, pt, 1)
            if v is None:
                break
            rs.append(r)
            vals.append(v)
            r += PROFILE_STEP_M
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

    def infer_crown_radii(self, apex_pt, apex_val, seed_radius, threshold, competing):
        max_search = max(PROFILE_MIN_SEARCH_M, seed_radius * PROFILE_MAX_FACTOR + PROFILE_MAX_EXTRA_M)
        radii = []

        for i in range(NUM_ANGLES):
            angle = (2.0 * math.pi * i) / NUM_ANGLES
            rs, vals = self.sample_profile(apex_pt, angle, max_search)

            if len(vals) < MIN_PROFILE_POINTS:
                radii.append(seed_radius * 0.85)
                continue

            smooth_vals = list(vals)
            for _ in range(3):
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

                if hj < threshold * 0.58:
                    break

                if s_now > REBOUND_RISE_M:
                    rebound_count += 1
                else:
                    rebound_count = 0

                outside_h = smooth_vals[j + 1]
                edge_drop = max(0.0, hj - outside_h)
                h_ratio = hj / max(apex_val, 0.001)

                band_bonus = 0.0
                if EDGE_HEIGHT_RATIO_LOW <= h_ratio <= EDGE_HEIGHT_RATIO_HIGH:
                    center = (EDGE_HEIGHT_RATIO_LOW + EDGE_HEIGHT_RATIO_HIGH) / 2.0
                    band_bonus = 1.0 - abs(h_ratio - center) / max(center, 0.001)
                    band_bonus = max(0.0, band_bonus)

                ax, ay = xy_of(apex_pt)
                cand_pt = QgsPointXY(ax + rj * math.cos(angle), ay + rj * math.sin(angle))
                comp_pen = self.competitor_penalty(cand_pt, hj, apex_pt, apex_val, competing)

                score = 0.0
                score += EDGE_DROP_WEIGHT * edge_drop
                score += CURVATURE_WEIGHT * abs(c_now)
                score += band_bonus
                if s_now < -MIN_DESCENT_SLOPE:
                    score += 0.45 * abs(s_now)
                score -= RADIAL_COMPETITOR_PENALTY * comp_pen

                if rebound_count >= 2 and comp_pen > 0.20:
                    break

                if score > best_score:
                    best_score = score
                    best_r = rj

            radii.append(best_r)

        radii = circular_gaussian_smooth(
            radii,
            radius=GAUSSIAN_SMOOTH_RADIUS,
            sigma=GAUSSIAN_SMOOTH_SIGMA,
            passes=GAUSSIAN_SMOOTH_PASSES
        )
        return self.constrain_radii(radii)

    def constrain_radii(self, radii):
        if not radii:
            return radii
        out = list(radii)
        n = len(out)

        for _ in range(2):
            tmp = list(out)
            for i in range(n):
                prev_r = out[(i - 1) % n]
                curr_r = out[i]
                next_r = out[(i + 1) % n]

                local_ref = max((prev_r + next_r) / 2.0, 0.5)
                upper = min(local_ref * MAX_RADIUS_JUMP_FACTOR, local_ref + MAX_RADIUS_JUMP_M)
                lower = max(local_ref / MAX_RADIUS_JUMP_FACTOR, local_ref - MAX_RADIUS_JUMP_M, 0.40)

                tmp[i] = min(max(curr_r, lower), upper)
            out = tmp

        return out

    def crown_seed_radius(self, apex_val, cls):
        if cls == "strong":
            return max(2.5, min(16.0, apex_val * 0.65))
        return max(2.0, min(12.0, apex_val * 0.55))

    def build_owner_models(self, candidates):
        models = []
        for pt, val, prom, scale, local_support, cls, rank in candidates:
            seed_radius = self.crown_seed_radius(val, cls)
            threshold = self.inner_support_threshold(pt, val, seed_radius)
            comp_radius = max(seed_radius * 1.25, seed_radius + 2.0)
            competing = self.find_competing_centers(pt, val, comp_radius, threshold, candidates)
            radii = self.infer_crown_radii(pt, val, seed_radius, threshold, competing)
            models.append({
                "pt": pt,
                "val": val,
                "cls": cls,
                "threshold": threshold,
                "radii": radii,
                "seed_radius": seed_radius
            })
        return models

    def max_radius_for_point(self, pt, apex_pt, radii):
        px, py = xy_of(pt)
        ax, ay = xy_of(apex_pt)

        dx = px - ax
        dy = py - ay

        angle = math.atan2(dy, dx)
        if angle < 0:
            angle += 2.0 * math.pi

        idx_f = angle / (2.0 * math.pi) * len(radii)
        i0 = int(math.floor(idx_f)) % len(radii)
        i1 = (i0 + 1) % len(radii)
        t = idx_f - math.floor(idx_f)

        return radii[i0] * (1.0 - t) + radii[i1] * t

    def canopy_likelihood(self, pt, v, model):
        d = distance_xy(pt, model["pt"])
        max_r = self.max_radius_for_point(pt, model["pt"], model["radii"])

        if d > max_r * MAX_OWNERSHIP_RADIUS_FACTOR:
            return 0.0

        local_thresh = max(
            model["threshold"] * RELAXED_THRESHOLD_FACTOR,
            model["val"] * LIKELIHOOD_MIN_HEIGHT_FACTOR
        )
        if v < local_thresh:
            return 0.0

        center_score = max(0.0, 1.0 - (d / max(max_r, 0.5)))
        local_support = 1.0 if v >= model["threshold"] else max(0.0, v / max(model["threshold"], 0.001))
        radial_support = max(0.0, 1.0 - d / max(max_r, 0.5))

        score = (
            LIKELIHOOD_CENTER_WEIGHT * center_score
            + LIKELIHOOD_LOCAL_SUPPORT_WEIGHT * local_support
            + LIKELIHOOD_RADIAL_SUPPORT_WEIGHT * radial_support
        )
        return score

    def assign_pixels(self, models):
        owned = {i: [] for i in range(len(models))}

        for x, y, v in self.grid:
            pt = QgsPointXY(x, y)

            best_idx = None
            best_score = None
            second_score = None

            for i, model in enumerate(models):
                lik = self.canopy_likelihood(pt, v, model)
                if lik < LIKELIHOOD_MIN_SCORE:
                    continue

                own = self.ownership_score(pt, v, model["pt"], model["val"])
                score = own + lik

                if best_score is None or score > best_score:
                    second_score = best_score
                    best_score = score
                    best_idx = i
                elif second_score is None or score > second_score:
                    second_score = score

            if best_idx is None:
                continue

            if second_score is not None and best_score < second_score + OWNERSHIP_MARGIN:
                continue

            owned[best_idx].append((x, y, v))

        return owned

    def radii_to_polygon_geometry(self, apex_pt, radii):
        if not radii or len(radii) < 8:
            return None

        ax, ay = xy_of(apex_pt)
        pts = []
        n = len(radii)
        for i, r in enumerate(radii):
            angle = (2.0 * math.pi * i) / n
            x = ax + r * math.cos(angle)
            y = ay + r * math.sin(angle)
            pts.append(QgsPointXY(x, y))
        pts.append(pts[0])

        geom = QgsGeometry.fromPolygonXY([pts])

        try:
            geom = geom.simplify(0.15)
        except Exception:
            pass

        return geom

    def shrink_unsupported_radii(self, apex_pt, radii, threshold):
        out = list(radii)
        n = len(out)
        ax, ay = xy_of(apex_pt)

        for _ in range(FINAL_SHRINK_PASSES):
            changed = False
            for i, r in enumerate(out):
                angle = (2.0 * math.pi * i) / n
                x = ax + r * math.cos(angle)
                y = ay + r * math.sin(angle)
                pt = QgsPointXY(x, y)
                v = sample_raster_value(self.chm, pt, 1)

                if v is None or v < threshold * RELAXED_THRESHOLD_FACTOR:
                    out[i] = max(0.5, out[i] * UNSUPPORTED_RADIUS_SHRINK_FACTOR)
                    changed = True

            out = circular_gaussian_smooth(
                out,
                radius=GAUSSIAN_SMOOTH_RADIUS,
                sigma=GAUSSIAN_SMOOTH_SIGMA,
                passes=1
            )
            out = self.constrain_radii(out)
            if not changed:
                break

        return out

    def support_ratio_inside_geom(self, geom, threshold):
        rect = geom.boundingBox()
        hits = 0
        good = 0
        x = rect.xMinimum() + self.cell * 0.5
        while x <= rect.xMaximum() + 1e-9:
            y = rect.yMinimum() + self.cell * 0.5
            while y <= rect.yMaximum() + 1e-9:
                pt = QgsPointXY(x, y)
                if geom.contains(QgsGeometry.fromPointXY(pt)):
                    hits += 1
                    v = sample_raster_value(self.chm, pt, 1)
                    if v is not None and v >= threshold * RELAXED_THRESHOLD_FACTOR:
                        good += 1
                y += self.cell
            x += self.cell

        return (good / hits) if hits else 0.0

    def validate_shape(self, geom):
        if geom is None or geom.isEmpty():
            return False
        if geom.area() < MIN_CANOPY_AREA_M2:
            return False
        if polygon_compactness(geom) < MIN_COMPACTNESS:
            return False
        if bbox_elongation(geom) > MAX_ELONGATION:
            return False
        return True

    def region_area_from_owned_pixels(self, owned_pixels):
        return len(owned_pixels) * (self.cell * self.cell)

    def extract_all(self):
        candidates = self.find_candidate_centers()
        models = self.build_owner_models(candidates)
        owned = self.assign_pixels(models)

        accepted = []

        for i, model in enumerate(models):
            if i not in owned or not owned[i]:
                continue

            region_area = self.region_area_from_owned_pixels(owned[i])
            if model["cls"] == "secondary" and region_area < 4.0:
                continue

            radii = self.shrink_unsupported_radii(model["pt"], model["radii"], model["threshold"])
            geom = self.radii_to_polygon_geometry(model["pt"], radii)

            if not self.validate_shape(geom):
                continue

            support_ratio = self.support_ratio_inside_geom(geom, model["threshold"])
            if support_ratio < MIN_SUPPORT_RATIO:
                continue

            if SKIP_APEX_IF_INSIDE_ACCEPTED:
                skip = False
                apex_geom = QgsGeometry.fromPointXY(model["pt"])
                for _, _, acc_geom in accepted:
                    try:
                        test_geom = acc_geom.buffer(ACCEPTED_BUFFER_M, 8)
                        if test_geom.contains(apex_geom):
                            skip = True
                            break
                    except Exception:
                        if acc_geom.contains(apex_geom):
                            skip = True
                            break
                if skip:
                    continue

            reject = False
            for _, _, acc_geom in accepted:
                try:
                    inter = geom.intersection(acc_geom)
                    if not inter.isEmpty():
                        inter_area = inter.area()
                        frac_self = inter_area / max(geom.area(), 0.001)
                        frac_other = inter_area / max(acc_geom.area(), 0.001)
                        if frac_self > MAX_OVERLAP_FRAC_SELF or frac_other > MAX_OVERLAP_FRAC_OTHER:
                            reject = True
                            break
                except Exception:
                    pass

            if reject:
                continue

            accepted.append((model["pt"], model["val"], geom))
            if len(accepted) >= MAX_FINAL_CANOPIES:
                break

        return accepted


# ============================================================
# RUN
# ============================================================

square_layer = get_layer(TRAINING_SQUARE_LAYER_NAME)
canopy_layer = get_layer(CANOPY_OUTPUT_LAYER_NAME)
chm = get_layer(CHM_LAYER_NAME)

if not square_layer or not isinstance(square_layer, QgsVectorLayer):
    QMessageBox.warning(None, "Missing square layer", f"Could not find square layer named '{TRAINING_SQUARE_LAYER_NAME}'.")
elif not canopy_layer or not isinstance(canopy_layer, QgsVectorLayer):
    QMessageBox.warning(None, "Missing canopy layer", f"Could not find canopy layer named '{CANOPY_OUTPUT_LAYER_NAME}'.")
elif not chm or not isinstance(chm, QgsRasterLayer):
    QMessageBox.warning(None, "Missing CHM", f"Could not find CHM layer named '{CHM_LAYER_NAME}'.")
elif not canopy_layer.isEditable():
    QMessageBox.warning(None, "Canopy layer not editable", "Turn editing on for the canopy layer.")
else:
    selected = square_layer.selectedFeatures()
    if len(selected) != 1:
        QMessageBox.warning(None, "Select one square", "Select exactly one feature in training_squares, then run this script.")
    else:
        project_crs = iface.mapCanvas().mapSettings().destinationCrs()
        square_feat = selected[0]
        square_geom_project = transform_geom(square_feat.geometry(), square_layer.crs(), project_crs)
        square_fid = square_feat["fid"] if layer_has_field(square_layer, "fid") else None
        ortho_id_value = square_feat["ortho_id"] if layer_has_field(square_layer, "ortho_id") else None

        extractor = CrashSafeCanopyExtractor(chm, square_geom_project, project_crs)
        canopies = extractor.extract_all()

        canopy_fid = next_numeric_id(canopy_layer, "fid")
        if canopy_fid is None:
            canopy_fid = 1

        canopy_added = 0
        for _, apex_val, geom_chm in canopies:
            geom_layer = transform_geom(geom_chm, chm.crs(), canopy_layer.crs())

            feat = QgsFeature(canopy_layer.fields())
            feat.setGeometry(geom_layer)

            safe_set_attr(feat, "fid", canopy_fid)
            canopy_fid += 1
            safe_set_attr(feat, "square_fid", square_fid)
            safe_set_attr(feat, "apex_h", round(apex_val, 2))
            safe_set_attr(feat, "area_m2", round(geom_layer.area(), 2))
            safe_set_attr(feat, "mode", CANOPY_MODE)
            safe_set_attr(feat, "ortho_id", ortho_id_value)
            safe_set_attr(feat, "species", None)
            safe_set_attr(feat, "species_conf", None)
            safe_set_attr(feat, "reviewed", 0)
            safe_set_attr(feat, "notes", None)

            if canopy_layer.addFeature(feat):
                canopy_added += 1

        canopy_layer.updateExtents()
        canopy_layer.triggerRepaint()
        iface.mapCanvas().refresh()

        iface.messageBar().pushInfo(
            "Canopy Extraction",
            f"Added {canopy_added} canopy polygons from selected square."
        )