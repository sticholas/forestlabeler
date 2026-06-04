"""Interactive QGIS map tool for Track A canopy labeling."""

from __future__ import annotations

from dataclasses import dataclass

from qgis.PyQt.QtCore import QCoreApplication, QEvent, QTimer, Qt
from qgis.PyQt.QtGui import QColor
from qgis.PyQt.QtWidgets import QMessageBox
from qgis.core import QgsCoordinateTransform, QgsGeometry, QgsPointXY, QgsProject, QgsRasterLayer, QgsWkbTypes
from qgis.gui import QgsMapTool, QgsRubberBand

from ..forest_labeler_core.canopy_presets import build_canopy_parameters
from ..forest_labeler_core.raster_sources import is_probable_ortho_source
from .canopy_service import CanopyCreationRequest, create_canopy_feature
from .canopy_review import reject_and_remove_recent_canopy, reject_and_remove_selected_canopies
from .crown_preview_service import (
    CrownPreviewRequest,
    build_crown_preview_geometry,
)
from .geometry_adapter import circle_geometry


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
        self.preview_is_refined = False
        self.quick_reject_filter_active = False
        self.last_created_feature_id = None
        self.last_created_attempt_id = None

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
        self._enable_quick_reject_shortcut()
        self.iface.messageBar().pushInfo(
            "Forest Labeler",
            (
                f"Label Canopy active: {self.settings.canopy_mode}, "
                f"tightness {self.settings.crown_tightness}. Click or press-hold to create a crown. "
                "Ctrl+Z logs and removes selected canopy attempts."
            ),
        )

    def deactivate(self):
        self._disable_quick_reject_shortcut()
        self.stop_hold()
        self.preview_band.hide()
        super().deactivate()

    def keyPressEvent(self, event):
        if self._is_quick_reject_shortcut(event):
            if self._quick_reject_selected_canopies():
                event.accept()
                return

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
        self.refresh_seed_preview()
        self.timer.start(self.params.timer_interval_ms)

    def canvasMoveEvent(self, event):
        if not self.is_holding or self.center_project is None:
            return

        mouse_project = self.toMapCoordinates(event.pos())
        drag_radius = self.center_project.distance(mouse_project)
        if drag_radius > self.current_radius_m:
            self.current_radius_m = min(drag_radius, self.params.max_radius_m)
            self.refresh_seed_preview()

    def canvasReleaseEvent(self, event):
        if event.button() != Qt.MouseButton.LeftButton:
            return
        if not self.is_holding or self.center_project is None:
            return

        self.timer.stop()
        self.build_refined_preview()

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
                crown_tightness=self.settings.crown_tightness,
                refined=1 if build_result is not None and build_result.refined else 0,
                apex_height_m=build_result.apex_height_m if build_result is not None else None,
                species_layer=self.settings.species_layer,
                chm_id=self._layer_source(self.settings.chm_layer),
                ortho_id=self._find_ortho_source(self.center_project),
            )
        )

        if creation.ok:
            self._remember_created_canopy(creation)
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
            if build_result is not None and build_result.refined:
                self.iface.messageBar().pushInfo(
                    "Forest Labeler",
                    "Crown snapped to the local canopy apex and refined from CHM structure.",
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
        self.refresh_seed_preview()

    def refresh_seed_preview(self):
        """Show stable press-hold sizing feedback without running crown inference."""
        if self.center_project is None:
            return

        center_target = self._transform_point(
            self.center_project,
            self.canvas.mapSettings().destinationCrs(),
            self.settings.target_layer.crs(),
        )
        geometry = circle_geometry(
            (center_target.x(), center_target.y()),
            self.current_radius_m,
            segments=72,
        )
        if geometry is None:
            self.preview_band.hide()
            return

        self.current_geometry = geometry
        self.current_build_result = None
        self.preview_is_refined = False
        self.preview_band.setToGeometry(QgsGeometry(geometry), self.settings.target_layer)
        self.preview_band.show()

    def build_refined_preview(self):
        """Run canopy inference once at release so the final crown can snap to tree structure."""
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
            self.preview_is_refined = True
            self.preview_band.setToGeometry(QgsGeometry(result.geometry), self.settings.target_layer)
            self.preview_band.show()
        else:
            self.current_geometry = None
            self.current_build_result = None
            self.preview_is_refined = False
            self.preview_band.hide()

    def stop_hold(self):
        self.timer.stop()
        self.is_holding = False
        self.center_project = None
        self.current_radius_m = 0.0
        self.current_geometry = None
        self.current_build_result = None
        self.preview_is_refined = False

    def _is_quick_reject_shortcut(self, event):
        modifiers = event.modifiers()
        return (
            event.key() == Qt.Key.Key_Z
            and bool(modifiers & Qt.KeyboardModifier.ControlModifier)
            and not bool(modifiers & Qt.KeyboardModifier.ShiftModifier)
            and not bool(modifiers & Qt.KeyboardModifier.AltModifier)
        )

    def _quick_reject_selected_canopies(self):
        target_layer = self.settings.target_layer
        if target_layer is None:
            return False

        if target_layer.selectedFeatureIds():
            result = reject_and_remove_selected_canopies(
                target_layer,
                note="Ctrl+Z quick reject",
            )
        else:
            result = reject_and_remove_recent_canopy(
                target_layer,
                feature_id=self.last_created_feature_id,
                attempt_id=self.last_created_attempt_id,
                note="Ctrl+Z quick reject",
            )
        if result.ok:
            self.last_created_feature_id = None
            self.last_created_attempt_id = None
            self.canvas.refresh()
            self.iface.messageBar().pushSuccess(
                "Forest Labeler",
                f"Logged and removed {result.updated_count} rejected canopy attempt(s).",
            )
            if result.warnings:
                self.iface.messageBar().pushWarning("Forest Labeler", " ".join(result.warnings))
            return True

        self.iface.messageBar().pushWarning(
            "Forest Labeler",
            " ".join(result.errors + result.warnings),
        )
        return True

    def _remember_created_canopy(self, creation):
        self.last_created_feature_id = creation.feature_id
        self.last_created_attempt_id = None
        if creation.write_result is None or creation.write_result.attribute_plan is None:
            return
        self.last_created_attempt_id = creation.write_result.attribute_plan.values.get("attempt_id")

    def _enable_quick_reject_shortcut(self):
        if self.quick_reject_filter_active:
            return
        application = QCoreApplication.instance()
        if application is not None:
            application.installEventFilter(self)
            self.quick_reject_filter_active = True

    def _disable_quick_reject_shortcut(self):
        if not self.quick_reject_filter_active:
            return
        application = QCoreApplication.instance()
        if application is not None:
            application.removeEventFilter(self)
        self.quick_reject_filter_active = False

    def eventFilter(self, watched, event):
        if event.type() == QEvent.Type.KeyPress and self._is_quick_reject_shortcut(event):
            if self._quick_reject_selected_canopies():
                event.accept()
                return True
            self._trigger_qgis_undo_fallback()
            event.accept()
            return True
        return super().eventFilter(watched, event)

    def _trigger_qgis_undo_fallback(self):
        try:
            undo_action = self.iface.actionUndo()
        except Exception:
            undo_action = None
        if undo_action is not None and undo_action.isEnabled():
            undo_action.trigger()

    def _transform_point(self, point, source_crs, target_crs):
        if source_crs == target_crs:
            return QgsPointXY(point)
        transform = QgsCoordinateTransform(source_crs, target_crs, QgsProject.instance())
        return transform.transform(QgsPointXY(point))

    def _layer_source(self, layer):
        if layer is None:
            return None
        return layer.source()

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
            center_layer = self._transform_point(
                center_project,
                self.canvas.mapSettings().destinationCrs(),
                layer.crs(),
            )
            if layer.extent().contains(center_layer):
                return layer.source()
        return None
