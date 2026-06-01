"""Interactive QGIS map tool for stamping training polygons."""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
import math

from qgis.PyQt.QtCore import Qt
from qgis.PyQt.QtGui import QColor
from qgis.PyQt.QtWidgets import QInputDialog, QMessageBox
from qgis.core import (
    QgsCoordinateTransform,
    QgsGeometry,
    QgsPointXY,
    QgsProject,
    QgsRasterLayer,
    QgsVectorLayer,
    QgsWkbTypes,
)
from qgis.gui import QgsMapTool, QgsRubberBand

from ..forest_labeler_core.training_square import (
    build_training_shape_parameters,
    side_lengths_label,
    training_shape_ring_points,
)
from .geometry_adapter import polygon_geometry_from_points
from .feature_writer import add_training_shape_feature
from ..forest_labeler_core.raster_sources import is_probable_ortho_source


@dataclass(frozen=True)
class TrainingShapeMapToolSettings:
    target_layer: object
    segment_length_m: float
    vertex_count: int
    angle_deg: float
    side_lengths_m: tuple = ()


class TrainingShapeMapTool(QgsMapTool):
    """Preview and stamp regular training polygons."""

    ROTATION_STEP_DEG = 3.0

    def __init__(self, iface, settings: TrainingShapeMapToolSettings):
        super().__init__(iface.mapCanvas())
        self.iface = iface
        self.canvas = iface.mapCanvas()
        self.settings = settings
        self.params = build_training_shape_parameters(
            settings.segment_length_m,
            settings.vertex_count,
            settings.angle_deg,
            side_lengths=settings.side_lengths_m,
        )
        self.project_crs = self.canvas.mapSettings().destinationCrs()
        self.current_center_project = None

        self.preview_band = QgsRubberBand(self.canvas, QgsWkbTypes.PolygonGeometry)
        self.preview_band.setStrokeColor(QColor(255, 80, 40, 230))
        self.preview_band.setFillColor(QColor(255, 80, 40, 45))
        self.preview_band.setWidth(2)
        self.preview_band.hide()

    def activate(self):
        super().activate()
        self.canvas.setFocus()
        self.iface.messageBar().pushInfo(
            "Forest Labeler",
            (
                f"Create Training Polygon active: {self.params.shape_name}, "
                "move to preview, click to stamp. Q/E rotates; R sets an exact angle."
            ),
        )

    def deactivate(self):
        self.preview_band.hide()
        super().deactivate()

    def keyPressEvent(self, event):
        if event.key() == Qt.Key.Key_Escape:
            self.preview_band.hide()
            self.canvas.unsetMapTool(self)
            return
        if event.key() == Qt.Key.Key_Q:
            self.rotate_preview(-self.ROTATION_STEP_DEG)
            return
        if event.key() == Qt.Key.Key_E:
            self.rotate_preview(self.ROTATION_STEP_DEG)
            return
        if event.key() == Qt.Key.Key_R:
            self.request_exact_angle()
            return
        super().keyPressEvent(event)

    def canvasMoveEvent(self, event):
        self.current_center_project = self.toMapCoordinates(event.pos())
        self.refresh_preview()

    def canvasPressEvent(self, event):
        if event.button() != Qt.MouseButton.LeftButton:
            return

        target_layer = self.settings.target_layer
        if target_layer is None or not target_layer.isEditable():
            QMessageBox.warning(
                None,
                "Layer not editable",
                "Turn editing on for the target training polygon layer before stamping.",
            )
            return

        center_project = self.toMapCoordinates(event.pos())
        geometry = self._geometry_for_project_center(center_project)
        if geometry is None or geometry.isEmpty():
            QMessageBox.warning(None, "No polygon geometry", "Could not build a training polygon here.")
            return

        write_result = add_training_shape_feature(
            target_layer,
            geometry,
            segment_length_m=self.params.segment_length_m,
            side_lengths_label=side_lengths_label(self.params),
            vertex_count=self.params.vertex_count,
            shape_name=self.params.shape_name,
            angle_deg=self.params.angle_deg,
            ortho_id=self._find_ortho_source(center_project),
            plot_area=self._find_plot_area(center_project),
            landcover_summary=self._summarize_landcover(geometry),
        )
        if not write_result.ok:
            QMessageBox.warning(None, "Add feature failed", "\n".join(write_result.errors))
            return

        self.canvas.refresh()
        self.iface.messageBar().pushSuccess(
            "Forest Labeler",
            f"Training polygon added: {self.params.shape_name}.",
        )
        if write_result.warnings:
            self.iface.messageBar().pushWarning("Forest Labeler", " ".join(write_result.warnings))

    def refresh_preview(self):
        if self.current_center_project is None:
            return
        geometry = self._geometry_for_project_center(self.current_center_project)
        if geometry is None:
            self.preview_band.hide()
            return
        self.preview_band.setToGeometry(QgsGeometry(geometry), self.settings.target_layer)
        self.preview_band.show()

    def rotate_preview(self, delta_degrees):
        self.params = build_training_shape_parameters(
            self.params.segment_length_m,
            self.params.vertex_count,
            self.params.angle_deg + delta_degrees,
            side_lengths=self.params.side_lengths_m,
        )
        self.refresh_preview()
        self.iface.messageBar().pushInfo(
            "Forest Labeler",
            f"Training polygon angle: {self.params.angle_deg:.1f}°",
        )

    def request_exact_angle(self):
        angle, accepted = QInputDialog.getDouble(
            None,
            "Training Polygon Rotation",
            "Angle in degrees",
            self.params.angle_deg,
            0.0,
            359.99,
            2,
        )
        if not accepted:
            return
        self.params = build_training_shape_parameters(
            self.params.segment_length_m,
            self.params.vertex_count,
            angle,
            side_lengths=self.params.side_lengths_m,
        )
        self.refresh_preview()
        self.iface.messageBar().pushInfo(
            "Forest Labeler",
            f"Training polygon angle: {self.params.angle_deg:.2f}°",
        )

    def _geometry_for_project_center(self, center_project):
        target_center = self._transform_point(
            center_project,
            self.project_crs,
            self.settings.target_layer.crs(),
        )
        points = training_shape_ring_points((target_center.x(), target_center.y()), self.params)
        return polygon_geometry_from_points(points)

    def _transform_point(self, point, source_crs, target_crs):
        if source_crs == target_crs:
            return QgsPointXY(point)
        transform = QgsCoordinateTransform(source_crs, target_crs, QgsProject.instance())
        return transform.transform(QgsPointXY(point))

    def _find_ortho_source(self, center_project):
        for layer in QgsProject.instance().layerTreeRoot().layerOrder():
            if not isinstance(layer, QgsRasterLayer):
                continue
            if not is_probable_ortho_source(
                layer.name(),
                layer.source(),
                layer.providerType(),
                excluded_names={"CAH_LandCover", "chm", "canopy height model"},
            ):
                continue
            center_layer = self._transform_point(center_project, self.project_crs, layer.crs())
            if layer.extent().contains(center_layer):
                return layer.source()
        return None

    def _find_plot_area(self, center_project):
        area_layer = self._find_plot_area_layer()
        if area_layer is None or area_layer.fields().indexOf("name") == -1:
            return None

        center_area = self._transform_point(center_project, self.project_crs, area_layer.crs())
        center_geometry = QgsGeometry.fromPointXY(center_area)
        for feature in area_layer.getFeatures():
            geometry = feature.geometry()
            if geometry and geometry.contains(center_geometry):
                value = feature["name"]
                return str(value) if value is not None else None
        return None

    def _find_plot_area_layer(self):
        for layer in QgsProject.instance().mapLayers().values():
            if not isinstance(layer, QgsVectorLayer):
                continue
            layer_name = layer.name().lower()
            if "customvegitationareas" in layer_name or "customvegetationareas" in layer_name:
                return layer
        return None

    def _find_landcover_layer(self):
        for layer in QgsProject.instance().mapLayers().values():
            if isinstance(layer, QgsRasterLayer) and layer.name() == "CAH_LandCover":
                return layer
        return None

    def _summarize_landcover(self, target_geometry):
        landcover_layer = self._find_landcover_layer()
        if landcover_layer is None:
            return None

        geometry = QgsGeometry(target_geometry)
        if self.settings.target_layer.crs() != landcover_layer.crs():
            transform = QgsCoordinateTransform(
                self.settings.target_layer.crs(),
                landcover_layer.crs(),
                QgsProject.instance(),
            )
            geometry.transform(transform)

        bbox = geometry.boundingBox()
        try:
            step = max(
                min(
                    max(
                        abs(landcover_layer.rasterUnitsPerPixelX()),
                        abs(landcover_layer.rasterUnitsPerPixelY()),
                    ),
                    10.0,
                ),
                1.0,
            )
        except Exception:
            step = 2.0
        step = self._bounded_landcover_sample_step(bbox, step)

        provider = landcover_layer.dataProvider()
        value_counts = Counter()

        x_coord = bbox.xMinimum() + step / 2.0
        while x_coord < bbox.xMaximum():
            y_coord = bbox.yMinimum() + step / 2.0
            while y_coord < bbox.yMaximum():
                point = QgsPointXY(x_coord, y_coord)
                if geometry.contains(QgsGeometry.fromPointXY(point)):
                    value, ok = provider.sample(point, 1)
                    if ok and value is not None:
                        try:
                            value_counts[int(round(float(value)))] += 1
                        except Exception:
                            pass
                y_coord += step
            x_coord += step

        if not value_counts:
            return None

        total = sum(value_counts.values())
        label_counts = Counter()
        for raster_value, count in value_counts.items():
            label_counts[self._landcover_label_lookup(landcover_layer, raster_value)] += count

        ranked = label_counts.most_common()
        summary = {"Detailed_L_count": len(ranked)}
        labels_pcts = [
            (label, round(100.0 * count / total, 1))
            for label, count in ranked[:3]
        ]

        if labels_pcts:
            summary["Detailed_L_majority"] = labels_pcts[0][0]
            summary["Detailed_L_majority_pct"] = labels_pcts[0][1]

        for index, (label, pct) in enumerate(labels_pcts, start=1):
            summary[f"Detailed_L{index}"] = label
            summary[f"Detailed_L{index}_pct"] = pct

        top3_pct = round(sum(pct for _, pct in labels_pcts), 1)
        summary["Detailed_L_other_pct"] = max(0.0, round(100.0 - top3_pct, 1))
        return summary

    def _bounded_landcover_sample_step(self, bbox, base_step):
        max_samples = 5000
        width = max(0.0, bbox.width())
        height = max(0.0, bbox.height())
        estimated_samples = (width / base_step) * (height / base_step)
        if estimated_samples <= max_samples:
            return base_step
        return max(base_step, math.sqrt((width * height) / max_samples))

    def _landcover_label_lookup(self, landcover_layer, raster_value):
        try:
            provider = landcover_layer.dataProvider()
            rat = provider.attributeTable(1)
            if rat is None:
                return str(raster_value)
            try:
                fields = rat.qgisFields()
            except Exception:
                fields = rat.fields()
            label_index = fields.indexOf("Detailed_L")
            if label_index == -1:
                return str(raster_value)
            row = rat.row(float(raster_value))
            if not row:
                return str(raster_value)
            label = row[label_index]
            if label is None:
                return str(raster_value)
            label_text = str(label).strip()
            return label_text if label_text else str(raster_value)
        except Exception:
            return str(raster_value)
