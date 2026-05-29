"""Interactive QGIS map tool for Track A canopy labeling."""

from __future__ import annotations

from dataclasses import dataclass

from qgis.PyQt.QtCore import QTimer, Qt
from qgis.PyQt.QtGui import QColor
from qgis.PyQt.QtWidgets import QMessageBox
from qgis.core import QgsCoordinateTransform, QgsGeometry, QgsPointXY, QgsProject, QgsWkbTypes
from qgis.gui import QgsMapTool, QgsRubberBand

from ..forest_labeler_core.canopy_presets import build_canopy_parameters
from .canopy_service import CanopyCreationRequest, create_canopy_feature
from .crown_preview_service import (
    CrownPreviewRequest,
    build_crown_preview_geometry,
)


@dataclass(frozen=True)
class CanopyMapToolSettings:
    chm_layer: object
    target_layer: object
    species_layer: object | None
    canopy_mode: str
    crown_tightness: int


class CanopyLabelMapTool(QgsMapTool):
    """Click/hold map tool that previews and writes canopy crown polygons."""

    def __init__(self, iface, settings: CanopyMapToolSettings):
        super().__init__(iface.mapCanvas())
        self.iface = iface
        self.canvas = iface.mapCanvas()
        self.settings = settings
        self.params = build_canopy_parameters(settings.canopy_mode, settings.crown_tightness)

        self.is_holding = False
        self.center_project = None
        self.current_radius_m = 0.0
        self.current_geometry = None
        self.current_build_result = None

        self.timer = QTimer()
        self.timer.timeout.connect(self.grow_circle)

        self.preview_band = QgsRubberBand(self.canvas, QgsWkbTypes.PolygonGeometry)
        self.preview_band.setStrokeColor(QColor(0, 180, 220, 230))
        self.preview_band.setFillColor(QColor(0, 180, 220, 45))
        self.preview_band.setWidth(2)
        self.preview_band.hide()

    def activate(self):
        super().activate()
        self.canvas.setFocus()
        self.iface.messageBar().pushInfo(
            "Forest Labeler",
            (
                f"Label Canopy active: {self.settings.canopy_mode}, "
                f"tightness {self.settings.crown_tightness}. Click or press-hold to create a crown."
            ),
        )

    def deactivate(self):
        self.stop_hold()
        self.preview_band.hide()
        super().deactivate()

    def keyPressEvent(self, event):
        if event.key() == Qt.Key.Key_Escape:
            self.stop_hold()
            self.preview_band.hide()
            self.canvas.unsetMapTool(self)
            return
        super().keyPressEvent(event)

    def canvasPressEvent(self, event):
        if event.button() != Qt.MouseButton.LeftButton:
            return

        target_layer = self.settings.target_layer
        if target_layer is None or not target_layer.isEditable():
            QMessageBox.warning(
                None,
                "Layer not editable",
                "Turn editing on for the target canopy polygon layer before labeling.",
            )
            return

        self.center_project = self.toMapCoordinates(event.pos())
        self.current_radius_m = self.params.start_radius_m
        self.is_holding = True
        self.refresh_preview()
        self.timer.start(self.params.timer_interval_ms)

    def canvasMoveEvent(self, event):
        if not self.is_holding or self.center_project is None:
            return

        mouse_project = self.toMapCoordinates(event.pos())
        drag_radius = self.center_project.distance(mouse_project)
        if drag_radius > self.current_radius_m:
            self.current_radius_m = min(drag_radius, self.params.max_radius_m)
            self.refresh_preview()

    def canvasReleaseEvent(self, event):
        if event.button() != Qt.MouseButton.LeftButton:
            return
        if not self.is_holding or self.center_project is None:
            return

        self.timer.stop()
        self.refresh_preview()

        if self.current_geometry is None or self.current_geometry.isEmpty():
            QMessageBox.warning(None, "No crown geometry", "Could not build a canopy polygon at this location.")
            self.stop_hold()
            self.preview_band.hide()
            return

        build_result = self.current_build_result
        creation = create_canopy_feature(
            CanopyCreationRequest(
                target_layer=self.settings.target_layer,
                geometry=self.current_geometry,
                seed_radius_m=self.current_radius_m,
                canopy_mode=self.settings.canopy_mode,
                refined=1 if build_result is not None and build_result.refined else 0,
                apex_height_m=build_result.apex_height_m if build_result is not None else None,
                species_layer=self.settings.species_layer,
            )
        )

        if creation.ok:
            self.canvas.refresh()
            self.iface.messageBar().pushSuccess(
                "Forest Labeler",
                f"Canopy polygon added. Feature id: {creation.feature_id}.",
            )
            if creation.warnings:
                self.iface.messageBar().pushWarning(
                    "Forest Labeler",
                    " ".join(creation.warnings),
                )
        else:
            QMessageBox.warning(None, "Canopy not added", "\n".join(creation.errors))

        self.stop_hold()
        self.preview_band.hide()

    def grow_circle(self):
        if not self.is_holding:
            return
        self.current_radius_m = min(
            self.current_radius_m + self.params.growth_per_tick_m,
            self.params.max_radius_m,
        )
        self.refresh_preview()

    def refresh_preview(self):
        if self.center_project is None:
            return

        center_chm = self._transform_point(
            self.center_project,
            self.canvas.mapSettings().destinationCrs(),
            self.settings.chm_layer.crs(),
        )
        result = build_crown_preview_geometry(
            CrownPreviewRequest(
                chm_layer=self.settings.chm_layer,
                target_layer=self.settings.target_layer,
                center_xy=(center_chm.x(), center_chm.y()),
                seed_radius_m=self.current_radius_m,
                canopy_mode=self.settings.canopy_mode,
                crown_tightness=self.settings.crown_tightness,
            )
        )

        if result.ok:
            self.current_geometry = result.geometry
            self.current_build_result = result.build_result
            self.preview_band.setToGeometry(QgsGeometry(result.geometry), self.settings.target_layer)
            self.preview_band.show()
        else:
            self.current_geometry = None
            self.current_build_result = None
            self.preview_band.hide()

    def stop_hold(self):
        self.timer.stop()
        self.is_holding = False
        self.center_project = None
        self.current_radius_m = 0.0
        self.current_geometry = None
        self.current_build_result = None

    def _transform_point(self, point, source_crs, target_crs):
        if source_crs == target_crs:
            return QgsPointXY(point)
        transform = QgsCoordinateTransform(source_crs, target_crs, QgsProject.instance())
        return transform.transform(QgsPointXY(point))
