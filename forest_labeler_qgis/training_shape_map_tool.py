"""Interactive QGIS map tool for stamping training shapes."""

from __future__ import annotations

from dataclasses import dataclass

from qgis.PyQt.QtCore import Qt
from qgis.PyQt.QtGui import QColor
from qgis.PyQt.QtWidgets import QMessageBox
from qgis.core import QgsCoordinateTransform, QgsFeature, QgsGeometry, QgsPointXY, QgsProject, QgsWkbTypes
from qgis.gui import QgsMapTool, QgsRubberBand

from ..forest_labeler_core.training_square import (
    build_training_shape_parameters,
    training_shape_ring_points,
)
from .geometry_adapter import polygon_geometry_from_points


@dataclass(frozen=True)
class TrainingShapeMapToolSettings:
    target_layer: object
    segment_length_m: float
    vertex_count: int
    angle_deg: float


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
                f"Create Training Shape active: {self.params.shape_name}, "
                f"{self.params.segment_length_m:.2f} m sides. Move to preview, click to stamp."
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
                "Turn editing on for the target training shape polygon layer before stamping.",
            )
            return

        center_project = self.toMapCoordinates(event.pos())
        geometry = self._geometry_for_project_center(center_project)
        if geometry is None or geometry.isEmpty():
            QMessageBox.warning(None, "No shape geometry", "Could not build a training shape here.")
            return

        feature = QgsFeature(target_layer.fields())
        feature.setGeometry(geometry)
        self._safe_set_attr(feature, "angle", self.params.angle_deg)
        self._safe_set_attr(feature, "segment_m", self.params.segment_length_m)
        self._safe_set_attr(feature, "nodes", self.params.vertex_count)
        self._safe_set_attr(feature, "shape", self.params.shape_name)

        if not target_layer.addFeature(feature):
            QMessageBox.warning(None, "Add feature failed", "Could not add the training shape.")
            return

        target_layer.updateExtents()
        target_layer.triggerRepaint()
        self.canvas.refresh()
        self.iface.messageBar().pushSuccess(
            "Forest Labeler",
            f"Training {self.params.shape_name} added.",
        )

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
        )
        self.refresh_preview()
        self.iface.messageBar().pushInfo(
            "Forest Labeler",
            f"Training shape angle: {self.params.angle_deg:.1f}°",
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

    def _safe_set_attr(self, feature, field_name, value):
        if feature.fields().indexOf(field_name) != -1:
            feature[field_name] = value
