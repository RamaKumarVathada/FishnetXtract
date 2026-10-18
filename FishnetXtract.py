#!/usr/bin/env python3
"""
FishnetXtract — QGIS Plugin (Multi-AOI Edition)
==============================================
Generates exact vector fishnets (OSM11/OSM9) based on the NPS/OSM tile system.
Supports batch processing of multiple AOI files with dynamic prefix naming, 
elapsed time reporting, and MFD MCM_CHART_ / CART NAME chart exclusion filters.
Dynamic GRID_OUTPUT generation and styled UI with Local Folder support.
Splits Output into distinct CPS (OSM) and NPS (T32/T08) coverage shapefiles.
NPS Output features dynamic attributes: Layer_type, Tile_Type, (AOI_Name), (DB_COVR).
CPS Output unifies OSM tile names under a single 'OSM' attribute column.
Overlays Coverage.shp: Appends first 3 letters of COV_SERVER to DB_COVR 
and creates duplicate tile rows if overlapping multiple Coverage areas.
Generates detailed execution logs (SUCCESS / FAILED) for every AOI.

Version: 2.0.0 (Spacious Layout & Clean UI Spacing)
Author: Rama Kumar Vathada
"""

import math
import os
import secrets
import re
import time
import tempfile
from datetime import datetime

from qgis.core import (
    QgsApplication,
    QgsVectorLayer,
    QgsFeature,
    QgsGeometry,
    QgsProject,
    QgsCoordinateReferenceSystem,
    QgsCoordinateTransform,
    Qgis,
    QgsCategorizedSymbolRenderer,
    QgsRendererCategory,
    QgsSymbol,
    QgsField,
    QgsTask,
    QgsWkbTypes,
    QgsPointXY,
    QgsSpatialIndex,
    QgsMapLayerProxyModel,
)
from qgis.gui import QgsFileWidget, QgsMapLayerComboBox
from qgis.PyQt.QtCore import QVariant, QTimer, Qt
from qgis.PyQt.QtWidgets import (
    QAction,
    QPushButton,
    QToolButton,
    QFormLayout,
    QMessageBox,
    QVBoxLayout,
    QHBoxLayout,
    QProgressBar,
    QCheckBox,
    QGroupBox,
    QDialog,
    QFrame,
    QButtonGroup,
    QWidget,
    QLabel,
    QRadioButton,
    QFileDialog
)
from qgis.PyQt.QtGui import QIcon, QColor
import processing

TYPE_STRING = QVariant.String

# ---------------------------------------------------------------------------
# NPS/OSM Tile Math Constants & Precise Conversions
# ---------------------------------------------------------------------------
_KC = 1.0067642927
_PI = math.pi
_HALF_PI = math.pi / 2
_RAD = 180.0 / _PI
_EARTH_RADIUS = 6378388.0
_GR = 57.29577951308
_GR_RR0 = _GR / _EARTH_RADIUS
_NAVMER_ROUND = 9
_TILEBBOX_ROUND = 7


def _trunc(val, digits):
    fac = 10**digits
    return math.trunc(val * fac) / fac


def _degreelon_to_mercatorlon(ddlon):
    if ddlon == 0.0:
        return 0.0
    return _trunc(ddlon / _GR_RR0, _NAVMER_ROUND)


def _degreelat_to_mercatorlat(ddlat):
    if ddlat == 0.0:
        return 0.0
    return _trunc(
        math.log(
            math.tan(
                0.5
                * (
                    math.atan2(math.tan(ddlat * _PI / 180.0) / _KC, 1)
                    + _HALF_PI
                )
            )
        )
        * _EARTH_RADIUS,
        _NAVMER_ROUND,
    )


_MAX_MM = _degreelon_to_mercatorlon(180)


def _mercatorlat_to_degreelat(mmlat):
    ddlat = _RAD * math.atan2(
        (
            math.tan(2.0 * math.atan2(math.exp(mmlat / _EARTH_RADIUS), 1) - _HALF_PI)
            * _KC
        ),
        1,
    )
    return _trunc(ddlat, _NAVMER_ROUND)


def _tile2lon(xtile, zoom):
    return xtile / (2.0**zoom) * 360.0 - 180.0


def _tile2lat(ytile, zoom):
    tilesize = (2 * _MAX_MM) / (2.0**zoom)
    return _mercatorlat_to_degreelat(_MAX_MM - tilesize * ytile)


def _tile2boundingBox(x, y, zoom):
    """Returns exact (north, east, south, west) boundaries in EPSG:4326 decimal degrees."""
    return (
        _trunc(_tile2lat(y, zoom), _TILEBBOX_ROUND),
        _trunc(_tile2lon(x + 1, zoom), _TILEBBOX_ROUND),
        _trunc(_tile2lat(y + 1, zoom), _TILEBBOX_ROUND),
        _trunc(_tile2lon(x, zoom), _TILEBBOX_ROUND),
    )


def _latlon2tilename(lat, lon, zoom):
    tilesize = (2 * _MAX_MM) / (2.0**zoom)
    lat_mm = _degreelat_to_mercatorlat(lat)
    lon_mm = _degreelon_to_mercatorlon(lon)
    return (
        int((_MAX_MM + lon_mm) / tilesize),
        int((_MAX_MM - lat_mm) / tilesize),
    )


def _format_tilename(x, y, z):
    fill = 5 if z > 13 else 4
    return f"{x:0{fill}d}_{y:0{fill}d}_{z}"


def sanitize_filename(name):
    """Sanitizes text to prevent illegal file system characters."""
    return re.sub(r'[\\/*?:"<>|]', "_", str(name)).strip()


# ---------------------------------------------------------------------------
# Background Async C++ Pipeline Engine Task (Multi-AOI & Filter Aware)
# ---------------------------------------------------------------------------
class NitroMeshWorkerTask(QgsTask):
    def __init__(self, description, params):
        # Fixed: Added 'Flag' namespace for Qt6 compatibility[cite: 6]
        super().__init__(description, QgsTask.Flag.CanCancel)
        self.params = params
        self.success = False
        self.result_msg = ""
        self.generated_outputs = []
        self.start_time = 0.0
        self.elapsed_seconds = 0.0

    def run(self):
        self.start_time = time.time()
        try:
            p = self.params
            aoi_paths = p["aoi_paths"]
            output_dir = p["output_dir"]
            total_aois = len(aoi_paths)

            assign_aoi_name = p.get("assign_aoi_name", True)
            assign_db_covr = p.get("assign_db_covr", True)

            os.makedirs(output_dir, exist_ok=True)

            # --- SETUP COVERAGE.SHP SPATIAL INDEX ---
            coverage_dir = p.get("coverage_path", "")
            coverage_shp = os.path.join(coverage_dir, "Coverage.shp")
            coverage_spatial_index = QgsSpatialIndex()
            coverage_dict = {}
            db_covr_field_idx = -1
            cov_server_field_idx = -1

            if os.path.exists(coverage_shp) and assign_db_covr:
                try:
                    base_cov = QgsVectorLayer(coverage_shp, "Coverage", "ogr")
                    if base_cov.isValid():
                        cov_4326 = processing.run(
                            "native:reprojectlayer",
                            {
                                "INPUT": base_cov,
                                "TARGET_CRS": "EPSG:4326",
                                "OUTPUT": "memory:cov_4326",
                            },
                        )["OUTPUT"]
                        
                        db_covr_field_idx = cov_4326.fields().indexOf("DB_COVR")
                        cov_server_field_idx = cov_4326.fields().indexOf("COV_SERVER")
                        
                        for ft in cov_4326.getFeatures():
                            coverage_spatial_index.addFeature(ft)
                            coverage_dict[ft.id()] = ft
                except Exception as e:
                    print(f"Failed to load Coverage.shp layer: {str(e)}")

            def get_coverage_values(geom):
                if not assign_db_covr or not coverage_dict:
                    return [None]
                
                candidate_ids = coverage_spatial_index.intersects(geom.boundingBox())
                matches = set()
                
                for cid in candidate_ids:
                    cov_feat = coverage_dict[cid]
                    if geom.intersects(cov_feat.geometry()):
                        db_val = cov_feat.attribute(db_covr_field_idx) if db_covr_field_idx != -1 else ""
                        cov_val = cov_feat.attribute(cov_server_field_idx) if cov_server_field_idx != -1 else ""
                        
                        db_str = str(db_val).strip() if db_val is not None and str(db_val).lower() != "null" else ""
                        cov_str = str(cov_val).strip() if cov_val is not None and str(cov_val).lower() != "null" else ""
                        
                        cov_server_out = cov_str[:3] if cov_str else ""
                        
                        if db_str and cov_server_out:
                            db_covr_out = f"{db_str}_{cov_server_out}"
                        else:
                            db_covr_out = db_str or cov_server_out or None
                            
                        matches.add(db_covr_out)
                
                if not matches:
                    return [None]
                    
                return list(matches)
            # ----------------------------------------

            for idx, aoi_path in enumerate(aoi_paths):
                if self.isCanceled():
                    return False

                aoi_start_time = time.time()
                current_timestamp_str = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                aoi_base_prog = (idx / total_aois) * 100.0
                aoi_prog_scale = 100.0 / total_aois

                aoi_filename = os.path.basename(aoi_path)
                raw_prefix = os.path.splitext(aoi_filename)[0]
                if raw_prefix.endswith("_temp"):
                    raw_prefix = raw_prefix[:-5]
                aoi_prefix = sanitize_filename(raw_prefix)

                cps_out_path = os.path.join(output_dir, f"{aoi_prefix}_CPS_coverage.shp")
                nps_out_path = os.path.join(output_dir, f"{aoi_prefix}_NPS_coverage.shp")
                mfd_out_path = os.path.join(output_dir, f"{aoi_prefix}_MFD_Coverage.shp")
                log_out_path = os.path.join(output_dir, f"{aoi_prefix}_processing_log.txt")

                aoi_status = "SUCCESS"
                mfd_summary_lines = []
                grid_stats = {} 

                def record_grid_stat(db_covr, l_type):
                    if not db_covr:
                        db_covr = "UNKNOWN"
                    if db_covr not in grid_stats:
                        grid_stats[db_covr] = {"OSM11": 0, "OSM9": 0, "T32": 0, "T08": 0}
                    if l_type in grid_stats[db_covr]:
                        grid_stats[db_covr][l_type] += 1

                try:
                    base_aoi = QgsVectorLayer(aoi_path, aoi_prefix, "ogr")
                    if not base_aoi.isValid():
                        raise Exception(f"Invalid AOI layer file path: {aoi_path}")

                    aoi_fields = base_aoi.fields()
                    name_field_idx = -1
                    for i, field in enumerate(aoi_fields):
                        if field.name().lower() == "name":
                            name_field_idx = i
                            break

                    self.setProgress(int(aoi_base_prog + 0.05 * aoi_prog_scale))
                    aoi_4326 = processing.run(
                        "native:reprojectlayer",
                        {
                            "INPUT": base_aoi,
                            "TARGET_CRS": "EPSG:4326",
                            "OUTPUT": "memory:aoi_4326",
                        },
                    )["OUTPUT"]

                    aoi_features_4326 = list(aoi_4326.getFeatures())
                    aoi_spatial_index = QgsSpatialIndex()
                    aoi_dict = {}
                    for feat in aoi_features_4326:
                        aoi_spatial_index.addFeature(feat)
                        aoi_dict[feat.id()] = feat

                    def get_intersecting_aoi_names(geom):
                        if not assign_aoi_name or name_field_idx == -1:
                            return []
                        candidate_ids = aoi_spatial_index.intersects(geom.boundingBox())
                        names = set()
                        for cid in candidate_ids:
                            aoi_feat = aoi_dict[cid]
                            if geom.intersects(aoi_feat.geometry()):
                                raw_val = aoi_feat.attribute(name_field_idx)
                                if raw_val is not None:
                                    val_str = str(raw_val).strip()
                                    if val_str and val_str.lower() != "null":
                                        names.add(val_str)
                        return sorted(list(names))

                    # Step 1: MFD Network
                    selected_products = p["selected_mfd_products"]
                    has_mfd_output = False
                    mfd_product_counts = {}

                    if selected_products and p["mfd_path"] and os.path.exists(p["mfd_path"]):
                        self.setProgress(int(aoi_base_prog + 0.10 * aoi_prog_scale))
                        mfd_spatial_mem = processing.run(
                            "native:extractbylocation",
                            {
                                "INPUT": p["mfd_path"],
                                "PREDICATE": [0],
                                "INTERSECT": aoi_4326,
                                "OUTPUT": "memory:mfd_spatial",
                            },
                        )["OUTPUT"]

                        formatted_products = ", ".join([f"'{prod}'" for prod in selected_products])
                        expression_str = (
                            f"PRODUCT IN ({formatted_products}) AND "
                            f"NOT (coalesce(\"MCM_CHART_\", '') LIKE 'T%') AND "
                            f"NOT (coalesce(\"CART_NAME\", '') LIKE '%FAK%')"
                        )

                        mfd_filtered_mem = processing.run(
                            "native:extractbyexpression",
                            {
                                "INPUT": mfd_spatial_mem,
                                "EXPRESSION": expression_str,
                                "OUTPUT": "memory:mfd_filtered",
                            },
                        )["OUTPUT"]

                        geom_type_str = QgsWkbTypes.displayString(mfd_filtered_mem.wkbType())
                        mfd_out_layer = QgsVectorLayer(
                            f"{geom_type_str}?crs={mfd_filtered_mem.crs().authid()}",
                            "mfd_final_workspace",
                            "memory",
                        )
                        mfd_provider = mfd_out_layer.dataProvider()
                        mfd_provider.addAttributes(list(mfd_filtered_mem.fields()))
                        mfd_out_layer.updateFields()

                        mfd_features_to_add = []
                        
                        prod_field_idx = mfd_filtered_mem.fields().indexOf("PRODUCT")
                        cart_name_idx = mfd_filtered_mem.fields().indexOf("CART_NAME")
                        mcm_chart_idx = mfd_filtered_mem.fields().indexOf("MCM_CHART_")
                        seen_mfd_records = set() 

                        for mfd_feat in mfd_filtered_mem.getFeatures():
                            if self.isCanceled():
                                return False
                                
                            mfd_geom = mfd_feat.geometry()

                            p_val = str(mfd_feat.attribute(prod_field_idx)) if prod_field_idx != -1 and mfd_feat.attribute(prod_field_idx) is not None else "UNKNOWN"
                            c_name = str(mfd_feat.attribute(cart_name_idx)) if cart_name_idx != -1 and mfd_feat.attribute(cart_name_idx) is not None else ""
                            mcm_val = str(mfd_feat.attribute(mcm_chart_idx)) if mcm_chart_idx != -1 and mfd_feat.attribute(mcm_chart_idx) is not None else ""
                            geom_wkt = mfd_geom.asWkt()

                            unique_key = (p_val, mcm_val, c_name, geom_wkt)
                            if unique_key in seen_mfd_records:
                                continue
                            seen_mfd_records.add(unique_key)
                            
                            new_mfd_feat = QgsFeature()
                            new_mfd_feat.setGeometry(mfd_geom)
                            original_attrs = list(mfd_feat.attributes())
                            new_mfd_feat.setAttributes(original_attrs)
                            mfd_features_to_add.append(new_mfd_feat)
                            
                            mfd_product_counts[p_val] = mfd_product_counts.get(p_val, 0) + 1

                        mfd_provider.addFeatures(mfd_features_to_add)
                        mfd_out_layer.updateExtents()
                        if mfd_out_layer.featureCount() > 0:
                            processing.run("native:savefeatures", {"INPUT": mfd_out_layer, "OUTPUT": mfd_out_path})
                            has_mfd_output = True

                    if mfd_product_counts:
                        for prod_name, count in sorted(mfd_product_counts.items()):
                            mfd_summary_lines.append(f"  Product [{prod_name}]: {count} ")
                    else:
                        mfd_summary_lines.append("  No MFD features extracted.")

                    self.setProgress(int(aoi_base_prog + 0.25 * aoi_prog_scale))

                    # Step 2: Extract CPS Grids
                    cps_memory_layer = QgsVectorLayer("Polygon?crs=EPSG:4326", "CPS_Grids", "memory")
                    cps_provider = cps_memory_layer.dataProvider()
                    
                    cps_fields = [
                        QgsField("layer_type", TYPE_STRING),
                        QgsField("OSM", TYPE_STRING)
                    ]
                    if assign_aoi_name:
                        cps_fields.append(QgsField("AOI_Name", TYPE_STRING))
                    if assign_db_covr:
                        cps_fields.append(QgsField("DB_COVR", TYPE_STRING, len=254))

                    cps_provider.addAttributes(cps_fields)
                    cps_memory_layer.updateFields()
                    cps_features_to_add = []

                    current_sub_prog = 0.25
                    zoom_levels = p.get("zoom_levels", [])

                    if zoom_levels:
                        prog_step = 0.40 / len(zoom_levels)
                        extent_4326 = aoi_4326.extent()
                        north = max(-85.051129, min(extent_4326.yMaximum(), 85.051129))
                        south = max(-85.051129, min(extent_4326.yMinimum(), 85.051129))
                        east = max(-180.0, min(extent_4326.xMaximum(), 180.0))
                        west = max(-180.0, min(extent_4326.xMinimum(), 180.0))

                        for zoom in zoom_levels:
                            if self.isCanceled():
                                return False
                            layer_type_label = f"OSM{zoom}"

                            min_x, min_y = _latlon2tilename(north, west, zoom)
                            max_x, max_y = _latlon2tilename(south, east, zoom)

                            total_tiles = max(1, (max_x - min_x + 1) * (max_y - min_y + 1))
                            processed_tiles = 0

                            for tx in range(min_x, max_x + 1):
                                for ty in range(min_y, max_y + 1):
                                    if self.isCanceled():
                                        return False

                                    bbn, bbe, bbs, bbw = _tile2boundingBox(tx, ty, zoom)
                                    ring = [
                                        QgsPointXY(bbw, bbn), QgsPointXY(bbe, bbn),
                                        QgsPointXY(bbe, bbs), QgsPointXY(bbw, bbs),
                                        QgsPointXY(bbw, bbn),
                                    ]
                                    tile_geom = QgsGeometry.fromPolygonXY([ring])

                                    candidate_ids = aoi_spatial_index.intersects(tile_geom.boundingBox())
                                    tile_intersects = any(tile_geom.intersects(aoi_dict[cid].geometry()) for cid in candidate_ids)
                                    processed_tiles += 1

                                    if processed_tiles % 50 == 0:
                                        step_progress = current_sub_prog + (processed_tiles / total_tiles) * prog_step
                                        self.setProgress(int(aoi_base_prog + step_progress * aoi_prog_scale))

                                    if not tile_intersects:
                                        continue

                                    intersecting_aois = get_intersecting_aoi_names(tile_geom)
                                    if not intersecting_aois:
                                        intersecting_aois = [None]

                                    t_name = _format_tilename(tx, ty, zoom)
                                    if t_name.endswith('_11'):
                                        t_name = t_name[:-3]
                                    elif t_name.endswith('_9'):
                                        t_name = t_name[:-2]

                                    coverage_vals = get_coverage_values(tile_geom)

                                    for name_val in intersecting_aois:
                                        for db_covr_val in coverage_vals:
                                            new_feat = QgsFeature()
                                            new_feat.setGeometry(tile_geom)
                                            
                                            feat_attrs = [layer_type_label, t_name]
                                            if assign_aoi_name:
                                                feat_attrs.append(name_val)
                                            if assign_db_covr:
                                                feat_attrs.append(db_covr_val)
                                                
                                            new_feat.setAttributes(feat_attrs)
                                            cps_features_to_add.append(new_feat)
                                            record_grid_stat(db_covr_val, layer_type_label)

                            current_sub_prog += prog_step
                            self.setProgress(int(aoi_base_prog + current_sub_prog * aoi_prog_scale))

                    cps_provider.addFeatures(cps_features_to_add)
                    cps_memory_layer.updateExtents()

                    has_cps_output = False
                    if cps_memory_layer.featureCount() > 0:
                        processing.run("native:savefeatures", {"INPUT": cps_memory_layer, "OUTPUT": cps_out_path})
                        has_cps_output = True

                    # Step 3: Extract NPS Structure Layers (T32 & T08)
                    nps_memory_layer = QgsVectorLayer("Polygon?crs=EPSG:4326", "NPS_Grids", "memory")
                    nps_provider = nps_memory_layer.dataProvider()
                    
                    nps_fields = [
                        QgsField("Layer_type", TYPE_STRING),
                        QgsField("Tile_Type", TYPE_STRING)
                    ]
                    if assign_aoi_name:
                        nps_fields.append(QgsField("AOI_Name", TYPE_STRING))
                    if assign_db_covr:
                        nps_fields.append(QgsField("DB_COVR", TYPE_STRING, len=254))

                    nps_provider.addAttributes(nps_fields)
                    nps_memory_layer.updateFields()
                    nps_features_to_add = []

                    nps_structs = []
                    if p.get("include_t32", True):
                        nps_structs.append((p["t32_path"], p["t32_field"], "T32", 0.65))
                    if p.get("include_t08", True):
                        nps_structs.append((p["t08_path"], p["t08_field"], "T08", 0.80))

                    for path, field_name, label, base_sub_prog in nps_structs:
                        if self.isCanceled():
                            return False
                        self.setProgress(int(aoi_base_prog + base_sub_prog * aoi_prog_scale))
                        if path and os.path.exists(path):
                            try:
                                local_extracted_mem = processing.run(
                                    "native:extractbylocation",
                                    {
                                        "INPUT": path, "PREDICATE": [0],
                                        "INTERSECT": aoi_4326, "OUTPUT": "memory:local_extracted",
                                    },
                                )["OUTPUT"]

                                to_wgs84 = QgsCoordinateTransform(
                                    local_extracted_mem.crs(), QgsCoordinateReferenceSystem("EPSG:4326"), QgsProject.instance()
                                ) if local_extracted_mem.crs().authid() != "EPSG:4326" else None

                                for feat in local_extracted_mem.getFeatures():
                                    if self.isCanceled():
                                        return False
                                    g_orig = feat.geometry()
                                    
                                    intersecting_struct_aois = get_intersecting_aoi_names(g_orig)
                                    if not intersecting_struct_aois:
                                        intersecting_struct_aois = [None]

                                    for struct_name_val in intersecting_struct_aois:
                                        g = QgsGeometry(g_orig)
                                        if to_wgs84:
                                            g.transform(to_wgs84)

                                        tile_name_val = str(feat.attribute(field_name)) if field_name and feat.attribute(field_name) is not None else ""
                                        coverage_vals = get_coverage_values(g)

                                        for db_covr_val in coverage_vals:
                                            new_feat = QgsFeature()
                                            new_feat.setGeometry(g)
                                            
                                            feat_attrs = [label, tile_name_val]
                                            if assign_aoi_name:
                                                feat_attrs.append(struct_name_val)
                                            if assign_db_covr:
                                                feat_attrs.append(db_covr_val)
                                                
                                            new_feat.setAttributes(feat_attrs)
                                            nps_features_to_add.append(new_feat)
                                            record_grid_stat(db_covr_val, label)
                            except Exception as err:
                                print(f"Warning: Failed to extract NPS structure feature: {err}")

                    self.setProgress(int(aoi_base_prog + 0.90 * aoi_prog_scale))
                    nps_provider.addFeatures(nps_features_to_add)
                    nps_memory_layer.updateExtents()

                    has_nps_output = False
                    if nps_memory_layer.featureCount() > 0:
                        processing.run("native:savefeatures", {"INPUT": nps_memory_layer, "OUTPUT": nps_out_path})
                        has_nps_output = True

                except Exception as ex:
                    aoi_status = "FAILED"
                    self.result_msg = str(ex)

                # --- GENERATE LOG FILE ---
                aoi_elapsed_sec = time.time() - aoi_start_time
                log_content = []
                log_content.append("=" * 50)
                log_content.append("FishnetXtract - Processing Log")
                log_content.append("=" * 50)
                log_content.append(f"Date/Time: {current_timestamp_str}")
                log_content.append(f"AOI Path: {aoi_path}")
                log_content.append(f"Status: {aoi_status}")
                log_content.append(f"Elapsed Time: {aoi_elapsed_sec:.2f} seconds")
                log_content.append("")
                log_content.append("--- MFD Coverage Extracted (by PRODUCT) ---")
                for line in mfd_summary_lines:
                    log_content.append(line)
                log_content.append("")
                log_content.append("--- OSM/NPS Grids Extracted (by DB_COVR) ---")
                
                if grid_stats:
                    for db_covr_key in sorted(grid_stats.keys()):
                        counts = grid_stats[db_covr_key]
                        log_content.append(f"  Coverage [DB_COVR]: {db_covr_key}")
                        log_content.append(f"    OSM11 : {counts['OSM11']}")
                        log_content.append(f"    OSM9  : {counts['OSM9']}")
                        log_content.append(f"    T32   : {counts['T32']}")
                        log_content.append(f"    T08   : {counts['T08']}")
                else:
                    log_content.append("  No Grid/Tile features extracted.")
                
                log_content.append("=" * 50)

                try:
                    with open(log_out_path, "w", encoding="utf-8") as log_file:
                        log_file.write("\n".join(log_content))
                except Exception as log_err:
                    print(f"Failed to write log file for {aoi_prefix}: {str(log_err)}")

                self.generated_outputs.append(
                    (aoi_prefix, cps_out_path if has_cps_output else None, nps_out_path if has_nps_output else None, mfd_out_path if has_mfd_output else None)
                )

                if aoi_status == "FAILED":
                    return False

            self.setProgress(100)
            self.elapsed_seconds = time.time() - self.start_time
            self.success = True
            return True

        except Exception as ex:
            self.elapsed_seconds = time.time() - self.start_time
            self.result_msg = str(ex)
            return False

    def finished(self, result):
        pass


# ---------------------------------------------------------------------------
# Dialog User Interface Management Panel
# ---------------------------------------------------------------------------
class FishnetXtractDialog(QDialog):
    def __init__(self, iface, parent=None):
        super().__init__(parent)
        self.iface = iface
        self.setWindowTitle("FishnetXtract Plugin (v2.0)")
        self.setFixedSize(660, 500)
        self.active_task = None
        self.selected_local_folder_path = ""
        
        self.setWindowOpacity(0.98) 
        self.setStyleSheet("""
            QDialog { background-color: rgba(220, 235, 245, 180); }
            QGroupBox {
                background-color: rgba(255, 255, 255, 60);
                border: 1px solid rgba(255, 255, 255, 200);
                border-radius: 5px; margin-top: 15px;
            }
            QGroupBox::title { subcontrol-origin: margin; subcontrol-position: top left; padding: 0 5px; color: #003399; font-weight: bold; left: 10px; }
            QLabel, QCheckBox, QRadioButton { color: #1a1a1a; font-size: 12px; }
            QPushButton { border: 1px solid #707070; border-radius: 3px; background-color: qlineargradient(x1: 0, y1: 0, x2: 0, y2: 1, stop: 0 #f2f2f2, stop: 0.5 #ebebeb, stop: 0.51 #dddddd, stop: 1 #cfcfcf); padding: 5px 15px; color: black; }
            QPushButton:hover { border: 1px solid #3c7fb1; background-color: qlineargradient(x1: 0, y1: 0, x2: 0, y2: 1, stop: 0 #eaf6fd, stop: 0.5 #d9f0fc, stop: 0.51 #bee6fd, stop: 1 #a7d9f5); }
            QPushButton:pressed { border: 1px solid #2c628b; background-color: qlineargradient(x1: 0, y1: 0, x2: 0, y2: 1, stop: 0 #e5f4fc, stop: 0.5 #c4e5f6, stop: 0.51 #98d1ef, stop: 1 #68b3db); }
            QPushButton:disabled { border: 1px solid #999999; background-color: #cccccc; color: #777777; }
            QProgressBar { border: 1px solid #bcbcbc; border-radius: 3px; text-align: center; background-color: #e6e6e6; color: black; font-weight: bold; }
            QProgressBar::chunk { background-color: qlineargradient(x1: 0, y1: 0, x2: 0, y2: 1, stop: 0 #85ed73, stop: 0.5 #57d943, stop: 0.51 #3fce2a, stop: 1 #22b10f); border-radius: 2px; }
        """)
        
        self.ui_timer = QTimer(self)
        self.ui_timer.timeout.connect(self._update_timer_label)
        self.start_timestamp = None

        self._build_ui()

    def _build_ui(self):
        layout = QVBoxLayout()
        layout.setContentsMargins(15, 12, 15, 15)
        layout.setSpacing(12)

        self.form = QFormLayout()
        self.form.setVerticalSpacing(12)

        # AOI Group Box
        self.aoi_group = QGroupBox("Choose AOI(s) for Grid")
        aoi_layout = QVBoxLayout()
        aoi_layout.setContentsMargins(12, 12, 12, 12)
        aoi_layout.setSpacing(8)

        self.rb_aoi_file = QRadioButton("Select AOI File (.shp, .kml, .kmz, .geojson, .json):")
        self.rb_aoi_file.setChecked(True)
        self.rb_aoi_canvas = QRadioButton("Grid extract currently loaded canvas layer:")

        self._aoi_files_widget = QgsFileWidget()
        self._aoi_files_widget.setStorageMode(QgsFileWidget.StorageMode.GetMultipleFiles)
        self._aoi_files_widget.setFilter(
            "Supported Vector Files (*.shp *.kml *.kmz *.geojson *.json);;"
            "ESRI Shapefiles (*.shp);;"
            "KML Files (*.kml);;"
            "KMZ Files (*.kmz);;"
            "GeoJSON Files (*.geojson)"
        )
        
        for btn in self._aoi_files_widget.findChildren((QToolButton, QPushButton)):
            btn.setText("Browse...")
            if isinstance(btn, QToolButton):
                # Fixed: Added 'ToolButtonStyle' namespace for Qt6 compatibility[cite: 6]
                btn.setToolButtonStyle(Qt.ToolButtonStyle.ToolButtonTextBesideIcon)
        
        self._aoi_canvas_widget = QgsMapLayerComboBox()
        # Fixed: Added 'Filter' namespace for Qt6 compatibility[cite: 6]
        self._aoi_canvas_widget.setFilters(QgsMapLayerProxyModel.Filter.VectorLayer)

        self._aoi_files_widget.setVisible(True)
        self._aoi_canvas_widget.setVisible(False)
        self.rb_aoi_file.toggled.connect(self._aoi_files_widget.setVisible)
        self.rb_aoi_canvas.toggled.connect(self._aoi_canvas_widget.setVisible)

        aoi_layout.addWidget(self.rb_aoi_file)
        aoi_layout.addWidget(self._aoi_files_widget)
        aoi_layout.addWidget(self.rb_aoi_canvas)
        aoi_layout.addWidget(self._aoi_canvas_widget)
        
        self.aoi_group.setLayout(aoi_layout)
        self.form.addRow(self.aoi_group)

        # --- Combined NPS Tile Source & Attribute Checkboxes ---
        nps_attr_layout = QHBoxLayout()
        nps_attr_layout.setContentsMargins(0, 4, 0, 4)
        nps_attr_layout.setSpacing(15)

        # 1. NPS Tile Source Group Box
        self.nps_group = QGroupBox("NPS Tile Source")
        rb_layout = QHBoxLayout()
        rb_layout.setContentsMargins(12, 10, 12, 10)
        rb_layout.setSpacing(30)

        self.rb_network = QPushButton("Network Folder")
        self.rb_local = QPushButton("Local NPS Folder")
        self.rb_network.setCheckable(True)
        self.rb_local.setCheckable(True)
        self.rb_network.setChecked(True)

        self.nps_source_group = QButtonGroup(self)
        self.nps_source_group.setExclusive(True)
        self.nps_source_group.addButton(self.rb_network)
        self.nps_source_group.addButton(self.rb_local)

        nps_button_style = "QPushButton { border: 1px solid transparent; border-radius: 3px; background-color: transparent; padding: 4px 8px; min-height: 12px; min-width: 120px; } QPushButton:hover { background-color: #eeeeee; } QPushButton:checked { background-color: #06ba09; border: 1px solid #cfd9ce; font-weight: bold; } QPushButton:pressed { background-color: #06ba09; }"
        self.rb_network.setStyleSheet(nps_button_style)
        self.rb_local.setStyleSheet(nps_button_style)

        rb_layout.addWidget(self.rb_network)
        rb_layout.addWidget(self.rb_local)
        rb_layout.addStretch()
        
        self.rb_local.toggled.connect(self._toggle_local_paths)
        self.nps_group.setLayout(rb_layout)
        nps_attr_layout.addWidget(self.nps_group)

        # 2. Attribute Checkboxes Group Box
        self.attr_group = QGroupBox("Choose additional attributes")
        attr_layout = QHBoxLayout()
        attr_layout.setContentsMargins(12, 10, 12, 10)
        self.cb_assign_aoi = QCheckBox("Assign AOI name")
        self.cb_assign_db_covr = QCheckBox("Assign DB_Cover")
        self.cb_assign_aoi.setChecked(True)
        self.cb_assign_db_covr.setChecked(True)
        
        attr_layout.addWidget(self.cb_assign_aoi)
        attr_layout.addSpacing(25)
        attr_layout.addWidget(self.cb_assign_db_covr)
        attr_layout.addStretch()
        self.attr_group.setLayout(attr_layout)
        nps_attr_layout.addWidget(self.attr_group)

        self.form.addRow(nps_attr_layout)

        # Select CPS Grids / NPS Tiles
        self.grid_group = QGroupBox("Select OSM Grids / NPS Tiles to Extract")
        grid_layout = QHBoxLayout()
        grid_layout.setContentsMargins(12, 10, 12, 10)
        grid_layout.setSpacing(20)

        self.cb_grid_all = QCheckBox("All")
        self.cb_osm11 = QCheckBox("OSM11")
        self.cb_osm9 = QCheckBox("OSM9")
        self.cb_t32 = QCheckBox("T32")
        self.cb_t08 = QCheckBox("T08")

        self._grid_child_boxes = [self.cb_osm11, self.cb_osm9, self.cb_t32, self.cb_t08]

        grid_layout.addWidget(self.cb_grid_all)
        grid_layout.addWidget(self.cb_osm11)
        grid_layout.addWidget(self.cb_osm9)
        grid_layout.addWidget(self.cb_t32)
        grid_layout.addWidget(self.cb_t08)

        self.cb_grid_all.setChecked(True)
        for cb in self._grid_child_boxes:
            cb.setChecked(True)

        self.cb_grid_all.clicked.connect(self._on_grid_all_clicked)
        for cb in self._grid_child_boxes:
            cb.clicked.connect(self._on_grid_child_clicked)

        self.grid_group.setLayout(grid_layout)
        self.form.addRow(self.grid_group)

        # Select MFD Products
        self.mfd_group = QGroupBox("Select MFD Products to Extract")
        mfd_layout = QHBoxLayout()
        mfd_layout.setContentsMargins(12, 10, 12, 10)
        mfd_layout.setSpacing(15)

        self.cb_mfd_all = QCheckBox("ALL")
        self.cb_mfd_all.setChecked(False)
        self.cb_mfd_all.clicked.connect(self._on_mfd_all_clicked)
        mfd_layout.addWidget(self.cb_mfd_all)

        self._mfd_boxes = {}
        for prod in ["G4", "GOLD", "ML", "HMP", "BASEMAP", "SONAR"]:
            cb = QCheckBox(prod)
            cb.setChecked(False)
            cb.clicked.connect(self._on_mfd_child_clicked)
            mfd_layout.addWidget(cb)
            self._mfd_boxes[prod] = cb

        self.mfd_group.setLayout(mfd_layout)
        self.form.addRow(self.mfd_group)

        # --- Checkbox: Open converted files in QGIS Canvas automatically ---
        self.cb_auto_load_canvas = QCheckBox("Open Extracted Grid file(s) in QGIS Canvas automatically")
        self.cb_auto_load_canvas.setChecked(True)
        self.cb_auto_load_canvas.setStyleSheet("padding-top: 6px; padding-bottom: 6px;")
        self.form.addRow(self.cb_auto_load_canvas)

        # --- Dynamic UNC path construction + inline allowlist pragmas to prevent false-positive secrets detection ---
        server_host = "hydwpb-nesaut02"
        base_nps_dir = rf"\\{server_host}\NPS_Tiles\Data"
        
        self._mfd_path_hidden = os.path.join(base_nps_dir, "charts", "charts.shp")  # pragma: allowlist secret
        self._coverage_path_hidden = os.path.join(base_nps_dir, "Miscellaneous", "coverage")  # pragma: allowlist secret
        self._t32_path_hidden = os.path.join(base_nps_dir, "tiles_grid", "tiles32.shp")  # pragma: allowlist secret
        self._t08_path_hidden = os.path.join(base_nps_dir, "tiles_grid", "tiles08.shp")  # pragma: allowlist secret
        self._t32_field_hidden = "TILENAME"
        self._t08_field_hidden = "TILENAME"
        self._primary_zoom_value = 11
        self._secondary_zoom_value = 9

        self.progress_bar = QProgressBar()
        self.progress_bar.setRange(0, 100)
        self.progress_bar.setValue(0)
        self.progress_bar.setTextVisible(True)
        self.progress_bar.setFormat("Progress: %p%")
        self.progress_bar.setVisible(False)
        
        self.form.addRow(self.progress_bar)

        # Control Buttons Layout
        button_layout = QHBoxLayout()
        button_layout.setContentsMargins(0, 8, 0, 0)
        button_layout.setSpacing(15)

        self.run_button = QPushButton("Generate Grid Coverage")
        self.run_button.setStyleSheet(
            "QPushButton { font-weight: bold; font-size: 14px; padding: 9px; background-color: #279e37; color: white; border-radius: 4px; } "
            "QPushButton:disabled { background-color: #888; }"
        )
        self.run_button.clicked.connect(self._handle_processing)
        
        self.cancel_button = QPushButton("Cancel")
        self.cancel_button.setStyleSheet(
            "QPushButton { font-weight: bold; font-size: 14px; padding: 9px; background-color: #db3f37; color: white; border-radius: 4px; } "
            "QPushButton:hover { background-color: #e64c45; }"
        )
        self.cancel_button.clicked.connect(self._on_cancel_clicked)

        button_layout.addWidget(self.run_button)
        button_layout.addWidget(self.cancel_button)
        
        self.form.addRow(button_layout)

        layout.addLayout(self.form)
        layout.addStretch()
        self.setLayout(layout)

    def _on_cancel_clicked(self):
        try:
            if self.active_task:
                try:
                    is_active = self.active_task.isActive()
                except RuntimeError:
                    is_active = False

                if is_active:
                    self.active_task.cancel()
        except Exception as e:
            print(f"Warning: Error during task cancellation: {e}")
        self.reject()

    def _toggle_local_paths(self, checked):
        if checked:
            dir_path = QFileDialog.getExistingDirectory(
                self, 
                "Select Directory containing tiles32.shp & tiles08.shp", 
                ""
            )
            if dir_path:
                self.selected_local_folder_path = dir_path
            else:
                self.rb_network.setChecked(True)

    def _on_grid_all_clicked(self, checked):
        for cb in self._grid_child_boxes:
            cb.setChecked(checked)

    def _on_grid_child_clicked(self):
        all_checked = all(cb.isChecked() for cb in self._grid_child_boxes)
        self.cb_grid_all.setChecked(all_checked)

    def _on_mfd_all_clicked(self, checked):
        for cb in self._mfd_boxes.values():
            cb.setChecked(checked)

    def _on_mfd_child_clicked(self):
        all_checked = all(cb.isChecked() for cb in self._mfd_boxes.values())
        self.cb_mfd_all.setChecked(all_checked)

    def _update_timer_label(self):
        if self.start_timestamp is not None:
            elapsed = time.time() - self.start_timestamp
            mins, secs = divmod(int(elapsed), 60)
            hrs, mins = divmod(mins, 60)
            time_str = f"{hrs:02d}:{mins:02d}:{secs:02d}"
            pct = self.progress_bar.value()
            self.progress_bar.setFormat(f"Progress: {pct}% ({time_str})")

    def _update_progress_safely(self, val):
        try:
            self.progress_bar.setValue(int(round(float(val))))
            self._update_timer_label()
        except Exception as e:
            print(f"Warning: Failed to update progress safely: {e}")

    def _handle_processing(self):
        aoi_paths = self.aoi_paths
        if not aoi_paths:
            QMessageBox.warning(self, "Validation Error", "Please select at least one valid AOI file or layer.")
            return

        if not self.zoom_levels and not self.cb_t32.isChecked() and not self.cb_t08.isChecked() and not self.selected_mfd_products:
            QMessageBox.warning(self, "Validation Error", "Please select at least one Grid, Tile, or MFD product layer to extract.")
            return

        if self.rb_local.isChecked() and (self.cb_t32.isChecked() or self.cb_t08.isChecked()):
            local_dir = self.selected_local_folder_path.strip()
            if not local_dir or not os.path.isdir(local_dir):
                QMessageBox.warning(self, "Validation Error", "Please select a valid local folder directory.")
                return
            if self.cb_t32.isChecked() and not os.path.exists(os.path.join(local_dir, "tiles32.shp")):
                QMessageBox.warning(self, "Validation Error", f"tiles32.shp not found in:\n{local_dir}")
                return
            if self.cb_t08.isChecked() and not os.path.exists(os.path.join(local_dir, "tiles08.shp")):
                QMessageBox.warning(self, "Validation Error", f"tiles08.shp not found in:\n{local_dir}")
                return

        if self.rb_aoi_file.isChecked():
            base_dir = os.path.dirname(aoi_paths[0])
        else:
            layer = self._aoi_canvas_widget.currentLayer()
            if layer and layer.dataProvider().dataSourceUri() and os.path.exists(layer.dataProvider().dataSourceUri().split('|')[0]):
                base_dir = os.path.dirname(layer.dataProvider().dataSourceUri().split('|')[0])
            else:
                base_dir = os.path.join(os.path.expanduser("~"), "Documents")
                
        computed_output_dir = os.path.join(base_dir, "GRID_OUTPUT")

        self.progress_bar.setValue(0)
        self.progress_bar.setVisible(True)
        self.run_button.setEnabled(False)

        self.start_timestamp = time.time()
        self.ui_timer.start(1000)

        task_params = {
            "aoi_paths": aoi_paths,
            "output_dir": computed_output_dir,
            "mfd_path": self.mfd_path,
            "t32_path": self.t32_path,
            "t32_field": self.t32_field,
            "t08_path": self.t08_path,
            "t08_field": self.t08_field,
            "coverage_path": self._coverage_path_hidden, 
            "primary_zoom": self.primary_zoom,
            "secondary_zoom": self.secondary_zoom,
            "zoom_levels": self.zoom_levels,
            "include_t32": self.cb_t32.isChecked(),
            "include_t08": self.cb_t08.isChecked(),
            "selected_mfd_products": self.selected_mfd_products,
            "assign_aoi_name": self.cb_assign_aoi.isChecked(),
            "assign_db_covr": self.cb_assign_db_covr.isChecked(),
            "auto_load_canvas": self.cb_auto_load_canvas.isChecked(),
        }

        self.active_task = NitroMeshWorkerTask("Batch Processing AOIs", task_params)
        self.active_task.progressChanged.connect(self._update_progress_safely)
        self.active_task.taskCompleted.connect(self._on_task_successful)
        self.active_task.taskTerminated.connect(self._on_task_failed)

        QgsApplication.taskManager().addTask(self.active_task)

    def _style_and_load_grid_layer(self, path, layer_name, style_field):
        if path and os.path.exists(path):
            layer = QgsVectorLayer(path, layer_name, "ogr")
            if layer.isValid() and layer.featureCount() > 0:
                idx = layer.fields().indexOf(style_field)
                if idx != -1:
                    unique_values = layer.uniqueValues(idx)
                    categories = []
                    for value in unique_values:
                        symbol = QgsSymbol.defaultSymbol(layer.geometryType())
                        random_color = QColor(secrets.randbelow(256), secrets.randbelow(256), secrets.randbelow(256), 150)
                        symbol.setColor(random_color)
                        categories.append(QgsRendererCategory(value, symbol, str(value)))
                    layer.setRenderer(QgsCategorizedSymbolRenderer(style_field, categories))
                QgsProject.instance().addMapLayer(layer)

    def _on_task_successful(self):
        self.ui_timer.stop()
        elapsed_sec = self.active_task.elapsed_seconds if hasattr(self.active_task, "elapsed_seconds") else (time.time() - self.start_timestamp if self.start_timestamp else 0.0)
        time_display = f"{int(elapsed_sec)//60}m {int(elapsed_sec)%60}s" if elapsed_sec >= 60 else f"{elapsed_sec:.1f}s"

        auto_load = self.cb_auto_load_canvas.isChecked()

        if auto_load and self.active_task and hasattr(self.active_task, "generated_outputs"):
            for aoi_prefix, cps_path, nps_path, mfd_path in self.active_task.generated_outputs:
                self._style_and_load_grid_layer(cps_path, f"{aoi_prefix}_CPS_coverage", "layer_type")
                self._style_and_load_grid_layer(nps_path, f"{aoi_prefix}_NPS_coverage", "Layer_type")
                if mfd_path and os.path.exists(mfd_path):
                    mfd_layer = QgsVectorLayer(mfd_path, f"{aoi_prefix}_MFD_Coverage", "ogr")
                    if mfd_layer.isValid() and mfd_layer.featureCount() > 0:
                        prod_idx = mfd_layer.fields().indexOf("PRODUCT")
                        if prod_idx != -1:
                            mfd_unique_values = mfd_layer.uniqueValues(prod_idx)
                            mfd_categories = []
                            for val in mfd_unique_values:
                                symbol = QgsSymbol.defaultSymbol(mfd_layer.geometryType())
                                random_color = QColor(secrets.randbelow(256), secrets.randbelow(256), secrets.randbelow(256), 150)
                                symbol.setColor(random_color)
                                mfd_categories.append(QgsRendererCategory(val, symbol, str(val)))
                            mfd_layer.setRenderer(QgsCategorizedSymbolRenderer("PRODUCT", mfd_categories))
                        QgsProject.instance().addMapLayer(mfd_layer)

        self.iface.messageBar().pushMessage(
            "FishnetXtract",
            f"Batch Processing Completed Successfully in {time_display}!",
            # Fixed: Added 'MessageLevel' namespace for Qt6 compatibility[cite: 6]
            Qgis.MessageLevel.Success,
        )
        self.accept()
        self.close()

    def _on_task_failed(self):
        self.ui_timer.stop()
        msg = self.active_task.result_msg if self.active_task else "Unknown runtime error."
        QMessageBox.warning(self, "Processing Failure", f"Thread terminated:\n{msg}")
        self.progress_bar.setVisible(False)
        self.run_button.setEnabled(True)

    @property
    def aoi_paths(self):
        if self.rb_aoi_canvas.isChecked():
            layer = self._aoi_canvas_widget.currentLayer()
            if layer and layer.isValid():
                path = layer.dataProvider().dataSourceUri().split('|')[0]
                if os.path.exists(path):
                    return [path]
                else:
                    tmp_path = os.path.join(tempfile.gettempdir(), f"{sanitize_filename(layer.name())}_temp.shp")
                    processing.run("native:savefeatures", {"INPUT": layer, "OUTPUT": tmp_path})
                    return [tmp_path]
            return []
        else:
            raw_str = self._aoi_files_widget.filePath()
            if not raw_str:
                return []
            if hasattr(QgsFileWidget, "splitFilePaths"):
                return QgsFileWidget.splitFilePaths(raw_str)
            if "|" in raw_str:
                return [p.strip() for p in raw_str.split("|") if p.strip()]
            elif ";" in raw_str:
                return [p.strip() for p in raw_str.split(";") if p.strip()]
            return [raw_str.strip()]

    @property
    def mfd_path(self):
        return self._mfd_path_hidden

    @property
    def t32_path(self):
        if self.rb_local.isChecked():
            local_dir = self.selected_local_folder_path.strip()
            return os.path.join(local_dir, "tiles32.shp") if local_dir else ""
        return self._t32_path_hidden

    @property
    def t08_path(self):
        if self.rb_local.isChecked():
            local_dir = self.selected_local_folder_path.strip()
            return os.path.join(local_dir, "tiles08.shp") if local_dir else ""
        return self._t08_path_hidden

    @property
    def t32_field(self):
        return self._t32_field_hidden

    @property
    def t08_field(self):
        return self._t08_field_hidden

    @property
    def primary_zoom(self):
        return self._primary_zoom_value

    @property
    def secondary_zoom(self):
        return self._secondary_zoom_value

    @property
    def zoom_levels(self):
        zooms = []
        if self.cb_osm11.isChecked():
            zooms.append(self.primary_zoom)
        if self.cb_osm9.isChecked():
            zooms.append(self.secondary_zoom)
        return sorted(list(set(zooms)), reverse=True)

    @property
    def selected_mfd_products(self):
        return [prod for prod, cb in self._mfd_boxes.items() if cb.isChecked()]


class FishnetXtract:
    def __init__(self, iface):
        self.iface = iface
        self.action = None
        self.dialog = None

    def initGui(self):
        icon_path = os.path.join(os.path.dirname(__file__), "FishnetXtract.PNG")
        icon = QIcon(icon_path) if os.path.exists(icon_path) else QIcon()
        self.action = QAction(icon, "FishnetXtract", self.iface.mainWindow())
        self.action.triggered.connect(self.run)
        self.iface.addToolBarIcon(self.action)
        self.iface.addPluginToVectorMenu("&FishnetXtract", self.action)

    def unload(self):
        self.iface.removePluginVectorMenu("&FishnetXtract", self.action)
        self.iface.removeToolBarIcon(self.action)
        if self.dialog:
            self.dialog.close()

    def run(self):
        # Always instantiate a fresh dialog window so it opens looking clean and new every time
        self.dialog = FishnetXtractDialog(self.iface, self.iface.mainWindow())
        self.dialog.show()
        self.dialog.raise_()
        self.dialog.activateWindow()


def classFactory(iface):
    return FishnetXtract(iface)
