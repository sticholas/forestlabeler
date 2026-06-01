from qgis.PyQt.QtCore import Qt
from qgis.PyQt.QtWidgets import QInputDialog, QMessageBox
from qgis.PyQt.QtGui import QColor
from qgis.core import (
    Qgis,
    QgsProject,
    QgsWkbTypes,
    QgsFeature,
    QgsGeometry,
    QgsPointXY,
    QgsVectorLayer,
    QgsRasterLayer,
    QgsCoordinateTransform
)
from qgis.gui import QgsMapTool, QgsRubberBand
import math
from collections import Counter

canvas = iface.mapCanvas()


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


def is_probable_ortho_layer(raster_layer):
    if not isinstance(raster_layer, QgsRasterLayer):
        return False

    src = (raster_layer.source() or "").lower()
    name = (raster_layer.name() or "").lower()
    provider = (raster_layer.providerType() or "").lower()

    if raster_layer.name() == "CAH_LandCover":
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


class SquareStampTool(QgsMapTool):
    def __init__(self, canvas, target_layer):
        super().__init__(canvas)
        self.canvas = canvas
        self.target_layer = target_layer

        self.size_m = 100
        self.angle_deg = 0.0
        self.angle_step_deg = 3.0

        self.project_crs = self.canvas.mapSettings().destinationCrs()
        self.current_center_project = None

        self.area_layer = get_layer("BigIsland_CustomVegitationAreas — Areas")
        self.landcover_layer = get_layer("CAH_LandCover")

        self.rb = QgsRubberBand(self.canvas, QgsWkbTypes.PolygonGeometry)
        self.rb.setStrokeColor(QColor(255, 0, 0, 220))
        self.rb.setFillColor(QColor(255, 0, 0, 40))
        self.rb.setWidth(2)
        self.rb.hide()

    def activate(self):
        super().activate()
        self.canvas.setFocus()
        iface.messageBar().pushInfo(
            "Square Stamp",
            "100 m square active. Move mouse for preview. Left-click stamps. Q/E rotate by 3°. R exact angle. Esc exit."
        )
        self.refresh_preview()

    def deactivate(self):
        self.rb.hide()
        super().deactivate()

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

    def keyPressEvent(self, event):
        key = event.key()

        if key == Qt.Key.Key_Q:
            self.angle_deg = (self.angle_deg - self.angle_step_deg) % 360.0
            self.refresh_preview()
            self.show_status()

        elif key == Qt.Key.Key_E:
            self.angle_deg = (self.angle_deg + self.angle_step_deg) % 360.0
            self.refresh_preview()
            self.show_status()

        elif key == Qt.Key.Key_R:
            val, ok = QInputDialog.getDouble(
                None,
                "Set rotation",
                "Rotation angle in degrees:",
                self.angle_deg,
                0.0,
                360.0,
                2
            )
            if ok:
                self.angle_deg = val % 360.0
                self.refresh_preview()
                self.show_status()

        elif key == Qt.Key.Key_Escape:
            self.canvas.unsetMapTool(self)

        else:
            super().keyPressEvent(event)

    def canvasMoveEvent(self, event):
        self.current_center_project = self.toMapCoordinates(event.pos())
        self.refresh_preview()

    def canvasPressEvent(self, event):
        if event.button() != Qt.MouseButton.LeftButton:
            return

        if not self.target_layer.isEditable():
            QMessageBox.warning(None, "Layer not editable", "Turn editing on for the target polygon layer.")
            return

        center_project = self.toMapCoordinates(event.pos())
        self.current_center_project = center_project
        center_target = transform_point(center_project, self.project_crs, self.target_layer.crs())
        geom_target = self.make_square_geometry(center_target, self.size_m, self.angle_deg)

        feat = QgsFeature(self.target_layer.fields())
        feat.setGeometry(geom_target)

        next_fid = self.get_next_fid()
        if next_fid is not None:
            safe_set_attr(feat, "fid", next_fid)

        safe_set_attr(feat, "angle", float(self.angle_deg))

        self.populate_plot_area(feat, center_project)
        self.populate_ortho_path(feat, center_project)
        self.populate_landcover(feat, center_project)

        ok = self.target_layer.addFeature(feat)
        if ok:
            self.target_layer.updateExtents()
            self.target_layer.triggerRepaint()
            self.canvas.refresh()
            iface.messageBar().pushInfo("Square Stamp", f"Polygon added. fid={next_fid if next_fid is not None else 'n/a'}")
        else:
            QMessageBox.warning(None, "Add feature failed", "Could not add the square polygon to the layer.")

    def show_status(self):
        iface.messageBar().pushInfo(
            "Square Stamp",
            f"Angle: {self.angle_deg:.1f}° | Size: {self.size_m:.0f} m"
        )

    def refresh_preview(self):
        if self.current_center_project is None:
            return

        center_target = transform_point(
            self.current_center_project,
            self.project_crs,
            self.target_layer.crs()
        )
        geom_target = self.make_square_geometry(center_target, self.size_m, self.angle_deg)
        self.rb.setToGeometry(geom_target, self.target_layer)
        self.rb.show()

    def make_square_geometry(self, center_xy, size_m, angle_deg):
        h = size_m / 2.0
        corners = [
            (-h, -h),
            ( h, -h),
            ( h,  h),
            (-h,  h),
            (-h, -h)
        ]

        a = math.radians(angle_deg)
        ca = math.cos(a)
        sa = math.sin(a)

        pts = []
        for dx, dy in corners:
            rx = dx * ca - dy * sa
            ry = dx * sa + dy * ca
            pts.append(QgsPointXY(center_xy.x() + rx, center_xy.y() + ry))

        return QgsGeometry.fromPolygonXY([pts])

    def populate_plot_area(self, feat, center_project):
        if not self.area_layer or not layer_has_field(self.area_layer, "name"):
            return

        center_area = transform_point(center_project, self.project_crs, self.area_layer.crs())
        center_geom = QgsGeometry.fromPointXY(center_area)

        for f in self.area_layer.getFeatures():
            if f.geometry() and f.geometry().contains(center_geom):
                safe_set_attr(feat, "plot_area", f["name"])
                return

    def populate_ortho_path(self, feat, center_project):
        root = QgsProject.instance().layerTreeRoot()
        layer_order = root.layerOrder()

        for lyr in layer_order:
            if not isinstance(lyr, QgsRasterLayer):
                continue
            if not is_probable_ortho_layer(lyr):
                continue

            center_lyr = transform_point(center_project, self.project_crs, lyr.crs())
            if lyr.extent().contains(center_lyr):
                safe_set_attr(feat, "ortho_id", lyr.source())
                return

    def landcover_label_lookup(self, raster_value):
        if not self.landcover_layer:
            return str(raster_value)

        try:
            provider = self.landcover_layer.dataProvider()
            rat = provider.attributeTable(1)

            if rat is None:
                return str(raster_value)

            try:
                rat_fields = rat.qgisFields()
            except Exception:
                rat_fields = rat.fields()

            label_idx = rat_fields.indexOf("Detailed_L")
            if label_idx == -1:
                return str(raster_value)

            row = rat.row(float(raster_value))
            if not row:
                return str(raster_value)

            label_val = row[label_idx]
            if label_val is None:
                return str(raster_value)

            label_text = str(label_val).strip()
            return label_text if label_text else str(raster_value)

        except Exception:
            return str(raster_value)

    def populate_landcover(self, feat, center_project):
        if not self.landcover_layer:
            return

        rlayer = self.landcover_layer
        provider = rlayer.dataProvider()

        center_lc = transform_point(center_project, self.project_crs, rlayer.crs())
        geom_lc = self.make_square_geometry(center_lc, self.size_m, self.angle_deg)
        bbox = geom_lc.boundingBox()

        try:
            step_x = abs(rlayer.rasterUnitsPerPixelX())
            step_y = abs(rlayer.rasterUnitsPerPixelY())
            step = max(min(max(step_x, step_y), 10.0), 1.0)
        except Exception:
            step = 2.0

        value_counts = Counter()

        x = bbox.xMinimum() + step / 2.0
        while x < bbox.xMaximum():
            y = bbox.yMinimum() + step / 2.0
            while y < bbox.yMaximum():
                pt = QgsPointXY(x, y)
                if geom_lc.contains(QgsGeometry.fromPointXY(pt)):
                    val, ok = provider.sample(pt, 1)
                    if ok and val is not None:
                        try:
                            v = int(round(float(val)))
                            value_counts[v] += 1
                        except Exception:
                            pass
                y += step
            x += step

        if not value_counts:
            return

        total = sum(value_counts.values())

        label_counts = Counter()
        for value, count in value_counts.items():
            label = self.landcover_label_lookup(value)
            label_counts[label] += count

        ranked = label_counts.most_common()
        safe_set_attr(feat, "Detailed_L_count", len(ranked))

        labels_pcts = []
        for label, count in ranked[:3]:
            pct = round(100.0 * count / total, 1)
            labels_pcts.append((label, pct))

        if len(labels_pcts) >= 1:
            safe_set_attr(feat, "Detailed_L_majority", labels_pcts[0][0])
            safe_set_attr(feat, "Detailed_L_majority_pct", labels_pcts[0][1])
            safe_set_attr(feat, "Detailed_L1", labels_pcts[0][0])
            safe_set_attr(feat, "Detailed_L1_pct", labels_pcts[0][1])

        if len(labels_pcts) >= 2:
            safe_set_attr(feat, "Detailed_L2", labels_pcts[1][0])
            safe_set_attr(feat, "Detailed_L2_pct", labels_pcts[1][1])

        if len(labels_pcts) >= 3:
            safe_set_attr(feat, "Detailed_L3", labels_pcts[2][0])
            safe_set_attr(feat, "Detailed_L3_pct", labels_pcts[2][1])

        top3_sum = round(sum(p for _, p in labels_pcts), 1)
        other_pct = max(0.0, round(100.0 - top3_sum, 1))
        safe_set_attr(feat, "Detailed_L_other_pct", other_pct)


def get_active_polygon_layer():
    lyr = iface.activeLayer()
    if lyr is None or not isinstance(lyr, QgsVectorLayer):
        QMessageBox.warning(None, "No active polygon layer", "Select your target polygon layer first.")
        return None
    if lyr.geometryType() != Qgis.GeometryType.Polygon:
        QMessageBox.warning(None, "Wrong layer type", "The active layer must be a polygon layer.")
        return None
    return lyr


target = get_active_polygon_layer()
if target:
    iface.square_stamp_tool = SquareStampTool(canvas, target)
    canvas.setMapTool(iface.square_stamp_tool)