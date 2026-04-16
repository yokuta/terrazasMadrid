/**
 * Visor de Sombras · Terrazas
 * app.js — main application logic
 *
 * Sections:
 *   1. Imports & Constants
 *   2. State
 *   3. DOM References
 *   4. Utilities
 *   5. Map Setup
 *   6. Sheet (bottom panel) drag behavior
 *   7. Legend
 *   8. Status pill (toast)
 *   9. User location
 *  10. Catalog loading (rótulos + addresses + terraces)
 *  11. Type filter
 *  12. Green filter
 *  13. Terrace layer rendering
 *  14. Shadow ring UI
 *  15. Terrace info card
 *  16. DuckDB engine
 *  17. Shadow queries
 *  18. Autocomplete search
 *  19. Controls (date, hour slider)
 *  20. Boot
 */

import * as duckdb from 'https://cdn.jsdelivr.net/npm/@duckdb/duckdb-wasm@1.33.1-dev20.0/+esm';
import wkx from 'https://esm.sh/wkx';
import { Buffer } from 'https://esm.sh/buffer';

/* ============================================================
   1. CONSTANTS
   ============================================================ */
const BUCKET_BASE_URL     = 'https://pub-048f4919d8bc472898a82c1bca238348.r2.dev/weekly_parquet';
const FILE_YEAR_IN_BUCKET = 2025;
const FILE_BASENAME       = 'terrace_shadows';
const FILE_SUFFIX         = '.parquet';

const ROTULOS_JSON_URL    = './datos/rotulos_terrazas_index.json';
const ADDRESS_GEOJSON_URL = './datos/numeracionCallesMadrid_light.geojson';
const TERRACES_GEOJSON_URL = './datos/terrazas.geojson';

const MIN_DATE = '2026-01-01';
const MAX_DATE = '2026-12-31';

const SOURCE_EPSG = 'EPSG:25830';
const TARGET_EPSG = 'EPSG:4326';

const RING_CIRCUMFERENCE = 2 * Math.PI * 28; // matches SVG r="28"

const MADRID_BOUNDS = L.latLngBounds([40.312, -3.888], [40.643, -3.517]);
const MAP_MIN_ZOOM  = 10;
const MAP_MAX_ZOOM  = 19;
const FIT_BOUNDS_MAX_ZOOM = 19;

/**
 * Type filter options: maps canonical key → display metadata + match strings.
 * match[] values are substrings of normalized tipo_actividad from GeoJSON.
 */
const TYPE_OPTION_META = {
  '':                     { label: 'Todos',        icon: '🗂️', match: [] },
  'bar':                  { label: 'Bar',           icon: '🍺', match: ['bar'] },
  'restaurante':          { label: 'Restaurante',   icon: '🍽️', match: ['restaurante'] },
  'cafeteria':            { label: 'Cafetería',     icon: '☕', match: ['cafeteria'] },
  'cerveceria / taberna': { label: 'Cervecería',    icon: '🍻', match: ['cerveceria', 'taberna'] },
  'comida rapida':        { label: 'Fast food',     icon: '🌮', match: ['comida rapida', 'fast food'] },
  'heladeria / dulces':   { label: 'Heladería',     icon: '🍦', match: ['heladeria', 'dulces'] },
};

/* ============================================================
   2. APPLICATION STATE
   ============================================================ */
let db = null, conn = null;

let currentLayer       = null;   // Leaflet layer for shadow polygons
let currentDayFeatures = [];

let rotulosCatalog  = [];        // terrace name catalog for search
let addressCatalog  = [];        // street address catalog for search
let currentSuggestions = [];
let selectedSuggIdx    = -1;

let terracesGeojson       = null; // full GeoJSON of all terrace points
let terracesLayer         = null; // Leaflet layer for terrace dots
let selectedTerraceId     = null;
let selectedRotulo        = null;
let selectedTerraceFeature = null;

let shadowByTerraceId = new Map(); // terraceId → shadow_pct from latest query
let greenFilterActive  = false;
let activityTypeFilter = '';

let autoLoadTimeout = null;
const registeredWeekAliases = new Set(); // tracks which parquet files are registered in DuckDB

let userLocationMarker = null;
let userLocationHalo   = null;

/* ============================================================
   3. DOM REFERENCES
   ============================================================ */
const searchInput    = document.getElementById('rotuloSearchInput');
const searchClear    = document.getElementById('search-clear');
const acList         = document.getElementById('autocompleteList');
const dateInput      = document.getElementById('dateInput');
const hourSlider     = document.getElementById('hourSlider');
const hourBadge      = document.getElementById('hourBadge');
const statusPill     = document.getElementById('status-pill');
const sheet          = document.getElementById('sheet');
const placeName      = document.getElementById('place-name');
const shadowPctVal   = document.getElementById('shadow-pct-value');
const shadowTimeNote = document.getElementById('shadow-time-note');
const ringFill       = document.getElementById('ring-fill');
const ringLabelText  = document.getElementById('ring-label-text');
const noResult       = document.getElementById('no-result');
const desktopLabel   = document.getElementById('desktop-label');
const sheetClose     = document.getElementById('sheet-close');
const handleArea     = document.getElementById('sheet-handle-area');
const terraceInfoSection = document.getElementById('terrace-info-section');
const terraceInfoCard    = document.getElementById('terrace-info-card');
const shadowLegend   = document.getElementById('shadow-legend');
const searchWrap     = document.getElementById('search-wrap');

// Mobile filter elements
const greenFilterToggle        = document.getElementById('green-filter-toggle');
const typeFilterBtn            = document.getElementById('type-filter-btn');
const typeBtnLabelText         = document.getElementById('type-btn-label-text');
const mobileTypeDropdownPortal = document.getElementById('mobile-type-dropdown-portal');

// Create and inject mobile dropdown element
const typeFilterDropdown = document.createElement('div');
typeFilterDropdown.id = 'type-filter-dropdown';
typeFilterDropdown.setAttribute('role', 'listbox');
typeFilterDropdown.setAttribute('aria-label', 'Tipo de local');
mobileTypeDropdownPortal.appendChild(typeFilterDropdown);

// FAB elements
const fabLocate = document.getElementById('fab-locate');

// Desktop filter elements
const desktopGreenFilter  = document.getElementById('desktop-green-filter');
const desktopFabDivider   = document.getElementById('desktop-fab-divider');
const desktopTypeWrap     = document.getElementById('desktop-type-wrap');
const desktopTypeBtn      = document.getElementById('desktop-type-btn');
const desktopTypeDropdown = document.getElementById('desktop-type-dropdown');

/* ============================================================
   4. UTILITIES
   ============================================================ */
/** Returns true when the viewport is mobile-width (<720px) */
function isMobileLayout() { return window.innerWidth < 720; }

/** Strips accents, lowercases, collapses whitespace */
function normalizeText(text) {
  return String(text ?? '')
    .normalize('NFD')
    .replace(/[\u0300-\u036f]/g, '')
    .toLowerCase()
    .trim()
    .replace(/\s+/g, ' ');
}

/** Normalizes tipo_actividad — returns '' for unusable values */
function normalizeActivityType(value) {
  const txt = normalizeText(value);
  if (!txt || txt === 'sin clasificar' || txt === 'no hosteleria') return '';
  return txt;
}

function escapeHtml(str) {
  return String(str ?? '')
    .replaceAll('&', '&amp;').replaceAll('<', '&lt;').replaceAll('>', '&gt;')
    .replaceAll('"', '&quot;').replaceAll("'", '&#039;');
}

function safeText(v) {
  if (v === null || v === undefined || v === '') return '—';
  return String(v).trim() || '—';
}

function toIntOrDash(v) {
  const n = Number(v);
  return Number.isFinite(n) ? n : '—';
}

function isFiniteNumber(v) { return Number.isFinite(Number(v)); }

function toNumberOrNull(v) {
  if (v === null || v === undefined) return null;
  const n = Number(v);
  return Number.isFinite(n) ? n : null;
}

function pad2(n) { return String(n).padStart(2, '0'); }

/** Returns true if feature matches the selected activity type filter */
function matchesActivityType(feature, selectedType) {
  if (!selectedType) return true;
  const activity = normalizeActivityType(feature?.properties?.tipo_actividad);
  const meta = TYPE_OPTION_META[selectedType];
  if (!meta?.match?.length) return true;
  return meta.match.some(m => activity.includes(m));
}

/* ── Date helpers ── */

function toYMD(value) {
  if (!value) return null;
  if (typeof value === 'string') {
    const m = value.match(/^(\d{4}-\d{2}-\d{2})/);
    if (m) return m[1];
  }
  const d = new Date(value);
  if (Number.isNaN(d.getTime())) return null;
  return `${d.getFullYear()}-${pad2(d.getMonth()+1)}-${pad2(d.getDate())}`;
}

function getHourFromDatetime(value) {
  if (!value) return null;
  if (typeof value === 'string') {
    const m = value.match(/T(\d{2}):/); if (m) return Number(m[1]);
    const m2 = value.match(/ (\d{2}):/); if (m2) return Number(m2[1]);
  }
  const d = new Date(value);
  return Number.isNaN(d.getTime()) ? null : d.getHours();
}

/** Returns ISO week number and year for a YYYY-MM-DD string */
function getIsoWeekInfo(dateString) {
  const date = new Date(dateString + 'T00:00:00');
  if (Number.isNaN(date.getTime())) throw new Error(`Fecha inválida: ${dateString}`);
  const tmp = new Date(Date.UTC(date.getFullYear(), date.getMonth(), date.getDate()));
  const dayNum = tmp.getUTCDay() || 7;
  tmp.setUTCDate(tmp.getUTCDate() + 4 - dayNum);
  const isoYear = tmp.getUTCFullYear();
  const yearStart = new Date(Date.UTC(isoYear, 0, 1));
  const isoWeek = Math.ceil((((tmp - yearStart) / 86400000) + 1) / 7);
  return { isoYear, isoWeek };
}

/** Returns the date string for a given ISO year/week/weekday (1=Mon … 7=Sun) */
function getIsoWeekDate(isoYear, isoWeek, isoWeekday) {
  const simple = new Date(Date.UTC(isoYear, 0, 4 + (isoWeek - 1) * 7));
  const dow = simple.getUTCDay() || 7;
  simple.setUTCDate(simple.getUTCDate() - dow + isoWeekday);
  return `${simple.getUTCFullYear()}-${pad2(simple.getUTCMonth()+1)}-${pad2(simple.getUTCDate())}`;
}

/** Maps selectedDate → Wednesday of the same ISO week in FILE_YEAR_IN_BUCKET */
function getRepresentativeWednesdayDateForSelectedWeek(selectedDate) {
  const { isoWeek } = getIsoWeekInfo(selectedDate);
  return getIsoWeekDate(FILE_YEAR_IN_BUCKET, isoWeek, 3);
}

function buildWeekFileName(dateString) {
  const { isoWeek } = getIsoWeekInfo(dateString);
  return `${FILE_BASENAME}_${FILE_YEAR_IN_BUCKET}_W${pad2(isoWeek)}${FILE_SUFFIX}`;
}

function buildWeekUrl(dateString)   { return `${BUCKET_BASE_URL}/${buildWeekFileName(dateString)}`; }

function buildWeekAlias(dateString) {
  const { isoWeek } = getIsoWeekInfo(dateString);
  return `week_${FILE_YEAR_IN_BUCKET}_W${pad2(isoWeek)}.parquet`;
}

function clampHour(hour) { return Math.max(6, Math.min(21, Number(hour))); }

function getInitialDateAndHour() {
  const now = new Date();
  let ymd = `${now.getFullYear()}-${pad2(now.getMonth()+1)}-${pad2(now.getDate())}`;
  if (ymd < MIN_DATE) ymd = MIN_DATE;
  if (ymd > MAX_DATE) ymd = MAX_DATE;
  return { ymd, hour: clampHour(now.getHours()) };
}

/* ── Coordinate projection (EPSG:25830 → WGS84) ── */

proj4.defs(SOURCE_EPSG, '+proj=utm +zone=30 +ellps=GRS80 +units=m +no_defs +type=crs');
proj4.defs(TARGET_EPSG, '+proj=longlat +datum=WGS84 +no_defs +type=crs');

function transformCoords25830To4326(coords) {
  if (!Array.isArray(coords)) return coords;
  if (coords.length >= 2 && !Array.isArray(coords[0])) {
    const x = Number(coords[0]), y = Number(coords[1]);
    if (!isFiniteNumber(x) || !isFiniteNumber(y)) throw new Error('Coordenadas no finitas');
    const [lon, lat] = proj4(SOURCE_EPSG, TARGET_EPSG, [x, y]);
    if (!isFiniteNumber(lon) || !isFiniteNumber(lat)) throw new Error('Reproyección inválida');
    return [lon, lat];
  }
  return coords.map(transformCoords25830To4326);
}

function reprojectGeometry(geometry) {
  if (!geometry?.type) return null;
  if (geometry.type === 'GeometryCollection') {
    return { ...geometry, geometries: (geometry.geometries || []).map(reprojectGeometry).filter(Boolean) };
  }
  if (!geometry.coordinates) return null;
  return { ...geometry, coordinates: transformCoords25830To4326(geometry.coordinates) };
}

/* ── WKB geometry decoding ── */

function toUint8Array(value) {
  if (!value) return null;
  if (value instanceof Uint8Array) return value;
  if (value instanceof ArrayBuffer) return new Uint8Array(value);
  if (Array.isArray(value)) return new Uint8Array(value);
  if (ArrayBuffer.isView(value)) return new Uint8Array(value.buffer, value.byteOffset, value.byteLength);
  if (typeof value === 'object') {
    const vals = Object.values(value);
    if (vals.length && vals.every(v => Number.isFinite(Number(v))))
      return new Uint8Array(vals.map(v => Number(v)));
  }
  return null;
}

function isLikelyGeoJSONGeometry(value) {
  return value && typeof value === 'object' && typeof value.type === 'string' &&
    (Array.isArray(value.coordinates) || Array.isArray(value.geometries));
}

function decodeWkbGeometry(value) {
  if (!value) throw new Error('geometry vacía');
  if (typeof value === 'string') return wkx.Geometry.parse(value).toGeoJSON();
  const bytes = toUint8Array(value);
  if (!bytes) throw new Error('No se pudo convertir geometry');
  return wkx.Geometry.parse(Buffer.from(bytes)).toGeoJSON();
}

function getGeometryFromRow(row, rowIndex) {
  const raw = row.geometry;
  if (!raw) throw new Error(`Fila ${rowIndex}: geometry vacía`);
  if (isLikelyGeoJSONGeometry(raw)) return raw;
  return decodeWkbGeometry(raw);
}

function normalizeDuckRow(row) {
  if (!row) return row;
  if (typeof row.toJSON === 'function') return row.toJSON();
  const obj = {};
  for (const key of Object.keys(row)) {
    const value = row[key];
    obj[key] = (value && typeof value.toJSON === 'function') ? value.toJSON() : value;
  }
  return obj;
}

async function arrowTableToRows(table) {
  if (!table) return [];
  return (table.toArray ? table.toArray() : []).map(normalizeDuckRow);
}

/** Converts a DuckDB result row into a GeoJSON Feature (with reprojection) */
function rowToFeature(row, rowIndex = null) {
  const sourceGeometry = getGeometryFromRow(row, rowIndex);
  const geom4326 = reprojectGeometry(sourceGeometry);
  if (!geom4326) throw new Error(`Fila ${rowIndex}: no se pudo reproyectar`);
  return {
    type: 'Feature',
    geometry: geom4326,
    properties: {
      terraza_id:      Number(row.terraza_id),
      rotulo:          row.rotulo ?? '',
      datetime:        row.datetime,
      date:            toYMD(row.date ?? row.datetime),
      hour:            getHourFromDatetime(row.datetime),
      shadow_area_m2:  row.shadow_area_m2,
      shadow_pct:      row.shadow_pct,
      terrace_area_m2: row.terrace_area_m2,
      building_id:     row.building_id,
    },
  };
}

/* ============================================================
   5. MAP SETUP
   ============================================================ */
const map = L.map('map', {
  center: [40.4168, -3.7038],
  zoom: isMobileLayout() ? 12 : 11,
  minZoom: MAP_MIN_ZOOM,
  maxZoom: MAP_MAX_ZOOM,
  maxBounds: MADRID_BOUNDS.pad(0.15),
  maxBoundsViscosity: 0.8,
  preferCanvas: true,
  zoomControl: false,
});

L.tileLayer('https://{s}.basemaps.cartocdn.com/rastertiles/voyager/{z}/{x}/{y}{r}.png', {
  subdomains: 'abcd',
  minZoom: MAP_MIN_ZOOM,
  maxZoom: MAP_MAX_ZOOM,
  attribution: '© OpenStreetMap © CARTO'
}).addTo(map);

map.fitBounds(MADRID_BOUNDS, {
  padding: isMobileLayout() ? [16, 16] : [20, 20],
  maxZoom: isMobileLayout() ? 12 : 11
});

/* ── IP-based approximate map centering on load ── */
async function centerMapByApproxLocation() {
  const madridCenter = [40.4168, -3.7038];
  const ZOOM_IP = 13;
  const ZOOM_FALLBACK = 15;

  try {
    const res = await fetch('https://ipapi.co/json/');
    if (!res.ok) throw new Error('IP location failed');
    const data = await res.json();
    const lat = Number(data.latitude);
    const lon = Number(data.longitude);

    if (!Number.isFinite(lat) || !Number.isFinite(lon)) {
      map.setView(madridCenter, ZOOM_FALLBACK, { animate: false });
      return;
    }

    // Only zoom in if user is within Madrid bounds
    if (!MADRID_BOUNDS.pad(0.8).contains(L.latLng(lat, lon))) {
      map.setView(madridCenter, ZOOM_FALLBACK, { animate: false });
      return;
    }

    map.setView([lat, lon], ZOOM_IP, { animate: false });
  } catch (err) {
    console.warn('IP centering fallback:', err);
    map.setView(madridCenter, ZOOM_FALLBACK, { animate: false });
  }
}

/* ============================================================
   6. SHEET DRAG (mobile bottom sheet)
   ============================================================ */
let sheetState     = 'peek';
let dragStartY     = 0;
let dragStartState = 'peek';
let isDragging     = false;
let dragDelta      = 0;

const peekH = () => parseInt(getComputedStyle(document.documentElement).getPropertyValue('--sheet-peek')) || 116;
const midH  = () => window.innerHeight * 0.34;
const fullH = () => window.innerHeight * 0.72;

function getSheetHeightForState(state) {
  if (state === 'peek') return peekH();
  if (state === 'mid')  return midH();
  return fullH();
}

function getDraggingSheetHeight() {
  const startHeight = getSheetHeightForState(dragStartState);
  return Math.max(peekH(), Math.min(fullH(), startHeight + dragDelta));
}

function setSheetState(state, animate = true) {
  sheetState = state;
  if (!animate) sheet.style.transition = 'none';
  sheet.dataset.state = state;
  if (!animate) setTimeout(() => { sheet.style.transition = ''; }, 50);

  const h = getSheetHeightForState(state);
  statusPill.style.bottom = (h + 12) + 'px';
  updateLegendPosition();
  updateLegendVisibility();
}

function onDragStart(clientY) {
  isDragging = true;
  dragStartY = clientY;
  dragStartState = sheetState;
  dragDelta = 0;
  sheet.style.transition = 'none';
  updateLegendPosition();
  updateLegendVisibility();
}

function onDragMove(clientY) {
  if (!isDragging) return;
  dragDelta = dragStartY - clientY;
  updateLegendPosition();
}

function onDragEnd() {
  if (!isDragging) return;
  isDragging = false;
  sheet.style.transition = '';

  const threshold = 60;
  if (dragStartState === 'peek') {
    setSheetState(dragDelta > threshold ? 'mid' : 'peek');
  } else if (dragStartState === 'mid') {
    if (dragDelta > threshold)       setSheetState('full');
    else if (dragDelta < -threshold) setSheetState('peek');
    else                             setSheetState('mid');
  } else {
    setSheetState(dragDelta < -threshold ? 'mid' : 'full');
  }

  updateLegendPosition();
  updateLegendVisibility();
}

// Touch drag
handleArea.addEventListener('touchstart', e => { onDragStart(e.touches[0].clientY); }, { passive: true });
handleArea.addEventListener('touchmove',  e => { onDragMove(e.touches[0].clientY); },  { passive: true });
handleArea.addEventListener('touchend',   () => onDragEnd());

// Mouse drag
handleArea.addEventListener('mousedown', e => onDragStart(e.clientY));
document.addEventListener('mousemove',  e => { if (isDragging) onDragMove(e.clientY); });
document.addEventListener('mouseup',    () => { if (isDragging) onDragEnd(); });

sheetClose.addEventListener('click', () => {
  setSheetState('peek');
  terraceInfoSection.classList.add('hidden');
});

/* ============================================================
   7. LEGEND
   ============================================================ */
function updateLegendPosition() {
  if (!shadowLegend) return;

  if (!isMobileLayout()) {
    shadowLegend.style.bottom = '';
    return;
  }

  const margin = 14;
  const height = isDragging ? getDraggingSheetHeight() : getSheetHeightForState(sheetState);
  shadowLegend.style.bottom = `${Math.round(height + margin)}px`;
}

/** Legend is only visible on mobile when sheet is at peek state and not dragging */
function updateLegendVisibility() {
  if (!shadowLegend) return;
  const shouldShow = isMobileLayout() && sheetState === 'peek' && !isDragging;
  shadowLegend.classList.toggle('hidden', !shouldShow);
}

/* ============================================================
   8. STATUS PILL (toast notification)
   ============================================================ */
let statusTimeout = null;

function showStatus(msg, isError = false, loading = false) {
  statusPill.innerHTML = loading ? `<span class="spinner"></span>${msg}` : msg;
  statusPill.className = 'visible' + (isError ? ' error' : '');
  clearTimeout(statusTimeout);
  if (!loading) {
    statusTimeout = setTimeout(() => { statusPill.className = ''; }, 2800);
  }
}

function hideStatus() {
  clearTimeout(statusTimeout);
  statusPill.className = '';
}

/* ============================================================
   9. USER LOCATION
   ============================================================ */
function showUserLocationMarker(lat, lng) {
  if (userLocationHalo)   { map.removeLayer(userLocationHalo);   userLocationHalo = null; }
  if (userLocationMarker) { map.removeLayer(userLocationMarker); userLocationMarker = null; }

  // Pulsing halo ring
  userLocationHalo = L.circleMarker([lat, lng], {
    radius: 20,
    color: '#00bcd4',
    weight: 1.5,
    fillColor: '#00bcd4',
    fillOpacity: 0.12,
    className: 'user-loc-halo',
  }).addTo(map);

  // Solid center dot
  userLocationMarker = L.circleMarker([lat, lng], {
    radius: 7,
    color: '#ffffff',
    weight: 2.5,
    fillColor: '#00bcd4',
    fillOpacity: 1,
    className: 'user-loc-dot',
  }).addTo(map);
}

function handleLocate() {
  if (!navigator.geolocation) { showStatus('Geolocalización no disponible', true); return; }

  fabLocate.classList.add('locating');
  showStatus('Obteniendo ubicación…', false, true);

  navigator.geolocation.getCurrentPosition(
    ({ coords: { latitude: lat, longitude: lng } }) => {
      fabLocate.classList.remove('locating');
      hideStatus();
      showUserLocationMarker(lat, lng);

      const targetZoom = 17;
      const currentZoom = map.getZoom();

      // Reset zoom slightly before flying to avoid Leaflet animation glitch
      if (currentZoom >= targetZoom - 0.25) {
        map.setView([lat, lng], Math.max(14, currentZoom - 1), { animate: false });
      }

      map.flyTo([lat, lng], targetZoom, { animate: true, duration: 1.2, easeLinearity: 0.2 });
    },
    (err) => {
      fabLocate.classList.remove('locating');
      const msgs = { 1: 'Permiso denegado', 2: 'Posición no disponible', 3: 'Tiempo agotado' };
      showStatus(msgs[err.code] || 'Error de geolocalización', true);
    },
    { enableHighAccuracy: true, timeout: 10000, maximumAge: 30000 }
  );
}

fabLocate?.addEventListener('click', handleLocate);

/* ============================================================
   10. CATALOG LOADING
   ============================================================ */

/** Loads the JSON index of terrace names used for autocomplete */
async function loadRotulosCatalog() {
  try {
    const res = await fetch(ROTULOS_JSON_URL, { cache: 'no-store' });
    if (!res.ok) throw new Error(`Cannot read ${ROTULOS_JSON_URL}`);
    const data = await res.json();
    if (!Array.isArray(data)) throw new Error('Rótulos JSON is not an array');

    rotulosCatalog = data
      .map(item => ({
        ...item,
        type: 'terrace',
        terraza_id: Number(item.terraza_id),
        _search_blob: normalizeText([
          item.label_busqueda, item.rotulo_formateado, item.rotulo_original,
          item.direccion_resumen, item.nombre_via, item.numero_via
        ].filter(Boolean).join(' '))
      }))
      .filter(item => Number.isFinite(item.terraza_id));
  } catch (err) {
    console.error(err);
    showStatus('No se pudo cargar el catálogo de rótulos', true);
  }
}

/** Loads the Madrid street address GeoJSON for address search */
async function loadAddressCatalog() {
  try {
    const res = await fetch(ADDRESS_GEOJSON_URL, { cache: 'no-store' });
    if (!res.ok) throw new Error(`Cannot read ${ADDRESS_GEOJSON_URL}`);
    const data = await res.json();
    if (!data || data.type !== 'FeatureCollection' || !Array.isArray(data.features)) {
      throw new Error('Invalid address GeoJSON');
    }

    addressCatalog = data.features.map((feature, idx) => {
      const props  = feature?.properties || {};
      const coords = feature?.geometry?.coordinates;

      if (!Array.isArray(coords) || coords.length < 2 ||
          !Number.isFinite(Number(coords[0])) || !Number.isFinite(Number(coords[1]))) {
        return null;
      }

      const display = String(props.d || '').trim();
      const search  = normalizeText(props.b || props.d || '');
      if (!display || !search) return null;

      return {
        type: 'address',
        id: `addr_${idx}`,
        display_label: display,
        search_label: search,
        lon: Number(coords[0]),
        lat: Number(coords[1]),
        _search_blob: search
      };
    }).filter(Boolean);

  } catch (err) {
    console.error(err);
    showStatus('No se pudo cargar el callejero', true);
  }
}

/** Loads the terrace points GeoJSON layer */
async function loadTerracesGeojson() {
  try {
    const res = await fetch(TERRACES_GEOJSON_URL, { cache: 'no-store' });
    if (!res.ok) throw new Error(`Cannot read ${TERRACES_GEOJSON_URL}`);
    const data = await res.json();
    if (!data || data.type !== 'FeatureCollection' || !Array.isArray(data.features)) {
      throw new Error('Invalid terrace GeoJSON');
    }
    terracesGeojson = data;
    buildTypeDropdownOptions();
    renderTerracesLayer();
  } catch (err) {
    console.error(err);
    showStatus('No se pudo cargar la capa de terrazas', true);
  }
}

/* ============================================================
   11. TYPE FILTER
   ============================================================ */

/** Builds HTML for a single type option item */
function buildTypeOptionHTML(value, isSelected) {
  const meta = TYPE_OPTION_META[value] || { label: formatActivityLabel(value), icon: '📍' };
  return `
    <div class="type-option${isSelected ? ' selected' : ''}" role="option" aria-selected="${isSelected}" data-value="${escapeHtml(value)}">
      <svg class="type-option-check" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.5" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true">
        <polyline points="20 6 9 17 4 12"/>
      </svg>
      <span class="type-option-icon" aria-hidden="true">${meta.icon}</span>
      <span>${escapeHtml(meta.label)}</span>
    </div>
  `;
}

/** Populates both mobile and desktop type dropdowns based on available activity types */
function buildTypeDropdownOptions() {
  if (!terracesGeojson?.features?.length) return;

  // Collect which activity types actually exist in the data
  const existingValues = new Set(
    terracesGeojson.features
      .map(f => normalizeActivityType(f?.properties?.tipo_actividad))
      .filter(v => v && v !== 'hosteleria otros')
  );

  // Keep only options whose match values appear in the data
  const preferredOrder = ['', 'bar', 'restaurante', 'cafeteria', 'cerveceria / taberna', 'comida rapida', 'heladeria / dulces'];
  const visibleOptions = preferredOrder.filter(value => {
    if (value === '') return true;
    const meta = TYPE_OPTION_META[value];
    if (!meta?.match) return false;
    return Array.from(existingValues).some(activity => meta.match.some(m => activity.includes(m)));
  });

  const html = visibleOptions.map(v => buildTypeOptionHTML(v, v === activityTypeFilter)).join('');

  function attachListeners(dropdown, source) {
    if (!dropdown) return;
    dropdown.innerHTML = html;
    dropdown.querySelectorAll('.type-option').forEach(el => {
      el.addEventListener('click', () => selectTypeOption(el.dataset.value, source));
    });
  }

  attachListeners(typeFilterDropdown, 'mobile');
  attachListeners(desktopTypeDropdown, 'desktop');
}

function formatActivityLabel(value) {
  const map = {
    'bar': 'Bar', 'restaurante': 'Restaurante', 'cafeteria': 'Cafetería',
    'cerveceria / taberna': 'Cervecería', 'comida rapida': 'Fast food',
    'heladeria / dulces': 'Heladería'
  };
  return map[value] || (value.charAt(0).toUpperCase() + value.slice(1));
}

function selectTypeOption(value) {
  activityTypeFilter = value || '';
  const meta = TYPE_OPTION_META[activityTypeFilter] || { label: 'Todos', icon: '🗂️' };

  // Update mobile UI
  if (typeBtnLabelText) typeBtnLabelText.textContent = meta.label || 'Todos';
  if (typeFilterBtn) typeFilterBtn.classList.toggle('has-value', !!activityTypeFilter);

  // Update desktop icon + tooltip
  if (desktopTypeBtn) {
    desktopTypeBtn.innerHTML = `${meta.icon}<span class="fab-tooltip">Tipo: ${meta.label}</span>`;
    desktopTypeBtn.classList.toggle('has-value', !!activityTypeFilter);
  }

  // Sync selected state in both dropdowns
  [typeFilterDropdown, desktopTypeDropdown].forEach(dropdown => {
    if (!dropdown) return;
    dropdown.querySelectorAll('.type-option').forEach(el => {
      const isSelected = el.dataset.value === activityTypeFilter;
      el.classList.toggle('selected', isSelected);
      el.setAttribute('aria-selected', String(isSelected));
    });
  });

  closeTypeDropdown('mobile');
  closeTypeDropdown('desktop');
  renderTerracesLayer();
}

/** Calculates dropdown position relative to #search-wrap (mobile only) */
function positionMobileTypeDropdown() {
  if (window.innerWidth >= 720 || !typeFilterBtn || !typeFilterDropdown || !searchWrap) return;
  const btnRect  = typeFilterBtn.getBoundingClientRect();
  const wrapRect = searchWrap.getBoundingClientRect();
  typeFilterDropdown.style.top  = `${btnRect.bottom - wrapRect.top + 8}px`;
  typeFilterDropdown.style.left = `${btnRect.left - wrapRect.left}px`;
}

function openTypeDropdown(target = 'mobile') {
  if (target === 'desktop') {
    closeTypeDropdown('mobile');
    desktopTypeDropdown?.classList.add('open');
    desktopTypeBtn?.setAttribute('aria-expanded', 'true');
  } else {
    if (window.innerWidth >= 720) return;
    closeTypeDropdown('desktop');
    positionMobileTypeDropdown();
    typeFilterDropdown?.classList.add('open');
    typeFilterBtn?.setAttribute('aria-expanded', 'true');
  }
}

function closeTypeDropdown(target = 'mobile') {
  if (target === 'desktop') {
    desktopTypeDropdown?.classList.remove('open');
    desktopTypeBtn?.setAttribute('aria-expanded', 'false');
  } else {
    typeFilterDropdown?.classList.remove('open');
    typeFilterBtn?.setAttribute('aria-expanded', 'false');
  }
}

typeFilterBtn?.addEventListener('click', e => {
  e.stopPropagation();
  typeFilterDropdown?.classList.contains('open') ? closeTypeDropdown('mobile') : openTypeDropdown('mobile');
});

desktopTypeBtn?.addEventListener('click', e => {
  e.stopPropagation();
  desktopTypeDropdown?.classList.contains('open') ? closeTypeDropdown('desktop') : openTypeDropdown('desktop');
});

// Close dropdowns when clicking outside
document.addEventListener('click', e => {
  if (!e.target.closest('.type-filter-wrap') && !e.target.closest('.desktop-type-wrap')) {
    closeTypeDropdown('mobile');
    closeTypeDropdown('desktop');
  }
  if (!e.target.closest('#search-wrap')) closeAC();
});

document.addEventListener('keydown', e => {
  if (e.key === 'Escape') { closeTypeDropdown('mobile'); closeTypeDropdown('desktop'); }
});

/* ============================================================
   12. GREEN FILTER
   ============================================================ */
function toggleGreenFilter() {
  greenFilterActive = !greenFilterActive;
  greenFilterToggle?.classList.toggle('is-active', greenFilterActive);
  greenFilterToggle?.setAttribute('aria-pressed', String(greenFilterActive));
  desktopGreenFilter?.classList.toggle('is-active', greenFilterActive);
  desktopGreenFilter?.setAttribute('aria-pressed', String(greenFilterActive));
  renderTerracesLayer();
}

greenFilterToggle?.addEventListener('click', toggleGreenFilter);
desktopGreenFilter?.addEventListener('click', toggleGreenFilter);

/* ============================================================
   13. TERRACE LAYER RENDERING
   ============================================================ */

/** Gets shadow_pct (0–100) for a terrace, or null if not yet loaded */
function getShadowPctForTerrace(terraceId) {
  const raw = shadowByTerraceId.get(Number(terraceId));
  if (raw === null || raw === undefined) return null;
  const n = Number(raw);
  if (!Number.isFinite(n)) return null;
  return n <= 1 ? n * 100 : n; // handle both 0–1 and 0–100 ranges
}

/**
 * Maps shadow_pct to a sun exposure bucket (0=shade … 3=full sun)
 * for color coding on the map.
 */
function getSunBucketFromShadowPct(pct) {
  if (pct === null) return 0;
  if (pct >= 75) return 0; // mostly shade
  if (pct >= 50) return 1;
  if (pct >= 25) return 2;
  return 3;                 // full sun
}

function getMarkerFillColor(feature) {
  const terraceId = Number(feature?.properties?.id_terraza);
  const pct = getShadowPctForTerrace(terraceId);
  const bucket = getSunBucketFromShadowPct(pct);

  const colors = ['#2f6fb3', '#6fa8dc', '#f4b942', '#d8572a'];
  const baseColor = colors[bucket] ?? '#2f6fb3';

  const isSelected = selectedTerraceId !== null && terraceId === Number(selectedTerraceId);
  return isSelected ? '#0f3d68' : baseColor;
}

/** Re-renders all terrace markers, applying active filters and shadow colors */
function renderTerracesLayer() {
  if (!terracesGeojson) return;

  if (terracesLayer) { map.removeLayer(terracesLayer); terracesLayer = null; }

  const filteredFeatures = terracesGeojson.features.filter(feature => {
    const passesGreen = !greenFilterActive || Number(feature?.properties?.tiene_zona_ajardinada) === 1;
    const passesType  = matchesActivityType(feature, activityTypeFilter);
    return passesGreen && passesType;
  });

  terracesLayer = L.geoJSON(
    { ...terracesGeojson, features: filteredFeatures },
    {
      pointToLayer: (feature, latlng) => {
        const terraceId = Number(feature?.properties?.id_terraza);
        const isSelected = selectedTerraceId !== null && terraceId === Number(selectedTerraceId);
        return L.circleMarker(latlng, {
          radius: isSelected ? 7 : 5,
          color: '#ffffff',
          weight: 2,
          fillColor: getMarkerFillColor(feature),
          fillOpacity: isSelected ? 1 : 0.92
        });
      },
      onEachFeature: (feature, layer) => {
        layer.on('click', () => selectTerraceFeature(feature));
      }
    }
  ).addTo(map);
}

function findTerraceFeatureById(terraceId) {
  if (!terracesGeojson?.features?.length) return null;
  return terracesGeojson.features.find(f => Number(f?.properties?.id_terraza) === Number(terraceId)) || null;
}

/* ── Terrace selection ── */

function selectTerraceFeature(feature) {
  if (!feature?.properties) return;
  const terraceId = Number(feature.properties.id_terraza);
  if (!Number.isFinite(terraceId)) return;

  selectedTerraceFeature = feature;
  selectedTerraceId = terraceId;
  selectedRotulo = safeText(feature.properties.rotulo);

  searchInput.value = selectedRotulo;
  searchClear.classList.add('visible');
  closeAC();
  searchInput.blur();

  placeName.textContent = selectedRotulo;
  placeName.classList.remove('empty');

  renderTerraceInfo(feature);
  renderTerracesLayer();

  // Fly to the terrace if it has point geometry
  if (feature.geometry?.type === 'Point' && Array.isArray(feature.geometry.coordinates)) {
    const [lon, lat] = feature.geometry.coordinates;
    if (Number.isFinite(lon) && Number.isFinite(lat)) {
      map.flyTo([lat, lon], Math.max(map.getZoom(), 17), { duration: 0.5 });
    }
  }

  setSheetState('mid');
  scheduleLoad();
}

function selectAddressResult(item) {
  if (!item || !Number.isFinite(item.lat) || !Number.isFinite(item.lon)) return;

  // Clear any existing terrace selection
  selectedTerraceId      = null;
  selectedRotulo         = null;
  selectedTerraceFeature = null;

  clearLayer();
  resetSummary();
  terraceInfoSection.classList.add('hidden');
  noResult.style.display = 'none';

  placeName.textContent = item.display_label;
  placeName.classList.remove('empty');

  searchInput.value = item.display_label;
  searchClear.classList.add('visible');
  closeAC();
  searchInput.blur();

  renderTerracesLayer();
  map.flyTo([item.lat, item.lon], Math.max(map.getZoom(), 17), { duration: 0.55 });

  if (isMobileLayout()) setSheetState('peek');
}

/* ============================================================
   14. SHADOW RING UI
   ============================================================ */
function updateRing(pct) {
  if (pct === null) {
    ringFill.style.strokeDashoffset = RING_CIRCUMFERENCE;
    ringLabelText.innerHTML = '—<br><span>sombra</span>';
    shadowPctVal.textContent = '—';
    shadowTimeNote.textContent = 'Selecciona lugar, fecha y hora';
    return;
  }
  const capped = Math.min(pct, 100);
  ringFill.style.strokeDashoffset = RING_CIRCUMFERENCE * (1 - capped / 100);
  ringLabelText.innerHTML = `${capped.toFixed(0)}%<br><span>sombra</span>`;
  shadowPctVal.textContent = `${capped.toFixed(1)} %`;
  shadowTimeNote.textContent = `${pad2(hourSlider.value)}:00 · ${dateInput.value}`;
}

function clearLayer() {
  if (currentLayer) { map.removeLayer(currentLayer); currentLayer = null; }
}

function resetSummary() {
  updateRing(null);
  noResult.style.display = 'none';
}

/* ============================================================
   15. TERRACE INFO CARD
   ============================================================ */
function renderTerraceInfo(feature) {
  if (!feature?.properties) {
    terraceInfoSection.classList.add('hidden');
    terraceInfoCard.innerHTML = '';
    return;
  }

  const p = feature.properties;
  const totalEstufas = (Number(p.estufas_gas_es) || 0) + (Number(p.estufas_electricas_es) || 0);
  const subtitle = [safeText(p.desc_nombre), safeText(p.num_terraza), safeText(p.desc_barrio_local)]
    .filter(v => v !== '—').join(' · ');

  const schedule = (ini, fin) => (ini && fin) ? `${ini} – ${fin}` : '—';

  terraceInfoCard.innerHTML = `
    <div class="terrace-info-title">${escapeHtml(safeText(p.rotulo))}</div>
    <div class="terrace-info-subtitle">${escapeHtml(subtitle || 'Terraza seleccionada')}</div>
    <div class="terrace-info-grid">
      <div class="info-pill"><div class="info-pill-label">Mesas</div><div class="info-pill-value">${escapeHtml(toIntOrDash(p.mesas_es))}</div></div>
      <div class="info-pill"><div class="info-pill-label">Sillas</div><div class="info-pill-value">${escapeHtml(toIntOrDash(p.sillas_es))}</div></div>
      <div class="info-pill"><div class="info-pill-label">Sombrillas</div><div class="info-pill-value">${escapeHtml(toIntOrDash(p.sombrillas_es))}</div></div>
      <div class="info-pill"><div class="info-pill-label">Estufas</div><div class="info-pill-value">${escapeHtml(toIntOrDash(totalEstufas))}</div></div>
    </div>
    <div class="terrace-info-list">
      <div class="terrace-info-item">
        <div class="info-pill-label">Horario L-J</div>
        <div class="info-pill-value">${escapeHtml(schedule(p.hora_ini_LJ_es, p.hora_fin_LJ_es))}</div>
      </div>
      <div class="terrace-info-item">
        <div class="info-pill-label">Horario V-S</div>
        <div class="info-pill-value">${escapeHtml(schedule(p.hora_ini_VS_es, p.hora_fin_VS_es))}</div>
      </div>
    </div>
  `;

  terraceInfoSection.classList.remove('hidden');
}

/* ============================================================
   16. DUCKDB ENGINE
   ============================================================ */
async function initDuckDB() {
  try {
    showStatus('Cargando datos…', false, true);
    const JSDELIVR_BUNDLES = duckdb.getJsDelivrBundles();
    const bundle = await duckdb.selectBundle(JSDELIVR_BUNDLES);
    if (!bundle) throw new Error('No DuckDB bundle found');

    const workerUrl = URL.createObjectURL(
      new Blob([`importScripts("${bundle.mainWorker}");`], { type: 'text/javascript' })
    );

    const worker = new Worker(workerUrl);
    db = new duckdb.AsyncDuckDB(new duckdb.ConsoleLogger(), worker);
    await db.instantiate(bundle.mainModule, bundle.pthreadWorker);
    URL.revokeObjectURL(workerUrl);

    conn = await db.connect();
    await conn.query(`SET enable_progress_bar = false;`);
    await conn.query(`SET threads = 1;`);
    hideStatus();
  } catch (err) {
    showStatus('Error inicializando el motor de datos', true);
    console.error(err);
  }
}

/** Registers a weekly parquet file with DuckDB (only once per alias) */
async function ensureWeekRegistered(dateString) {
  if (!db) throw new Error('DuckDB not initialized');
  const alias = buildWeekAlias(dateString);
  const url   = buildWeekUrl(dateString);
  if (registeredWeekAliases.has(alias)) return { alias, url };
  await db.registerFileURL(alias, url, duckdb.DuckDBDataProtocol.HTTP, true);
  registeredWeekAliases.add(alias);
  return { alias, url };
}

/* ============================================================
   17. SHADOW QUERIES
   ============================================================ */

/** Fetches shadow_pct for all terraces at the selected date/hour */
async function refreshTerraceShadowColors() {
  if (!db || !conn || !terracesGeojson) return;
  const selectedDate = dateInput.value;
  const selectedHour = Number(hourSlider.value);
  try {
    const { alias } = await ensureWeekRegistered(selectedDate);
    const representativeDate = getRepresentativeWednesdayDateForSelectedWeek(selectedDate);
    const sql = `
      SELECT terraza_id, shadow_pct
      FROM read_parquet('${alias}')
      WHERE substr(coalesce(cast(date as varchar), cast(datetime as varchar)), 1, 10) = '${representativeDate}'
        AND EXTRACT(HOUR FROM datetime) = ${selectedHour}
    `;
    const rows = await arrowTableToRows(await conn.query(sql));
    shadowByTerraceId.clear();
    for (const row of rows) {
      const tid = Number(row.terraza_id);
      if (Number.isFinite(tid)) shadowByTerraceId.set(tid, row.shadow_pct);
    }
    renderTerracesLayer();
  } catch (err) {
    console.error('Error refreshing shadow colors:', err);
  }
}

function getFitPadding() {
  if (isMobileLayout()) return { paddingTopLeft: [24, 110], paddingBottomRight: [24, 320] };
  return { paddingTopLeft: [400, 40], paddingBottomRight: [40, 40] };
}

/** Loads shadow geometry for the selected terrace at the current date/hour */
async function loadSelection() {
  if (!db || !conn) { showStatus('DuckDB-Wasm aún no está cargado', true); return; }
  if (!selectedTerraceId) return;

  const selectedDate = dateInput.value;
  const selectedHour = Number(hourSlider.value);

  if (!selectedDate) { showStatus('Selecciona una fecha', true); return; }
  if (selectedDate < MIN_DATE || selectedDate > MAX_DATE) {
    showStatus(`La fecha debe estar entre ${MIN_DATE} y ${MAX_DATE}`, true);
    return;
  }

  try {
    showStatus('Consultando datos…', false, true);
    noResult.style.display = 'none';

    const { alias } = await ensureWeekRegistered(selectedDate);
    const representativeDate = getRepresentativeWednesdayDateForSelectedWeek(selectedDate);
    const sql = `
      SELECT terraza_id, rotulo, datetime, date, shadow_area_m2, shadow_pct,
             terrace_area_m2, building_id, geometry
      FROM read_parquet('${alias}')
      WHERE terraza_id = ${Number(selectedTerraceId)}
        AND substr(coalesce(cast(date as varchar), cast(datetime as varchar)), 1, 10) = '${representativeDate}'
        AND EXTRACT(HOUR FROM datetime) = ${selectedHour}
      ORDER BY datetime
    `;

    const rows = await arrowTableToRows(await conn.query(sql));

    currentDayFeatures = rows
      .map((row, i) => { try { return rowToFeature(row, i); } catch (e) { console.error(e); return null; } })
      .filter(Boolean);

    clearLayer();

    if (!currentDayFeatures.length) {
      resetSummary();
      noResult.style.display = 'block';
      hideStatus();
      return;
    }

    // Draw shadow polygon
    currentLayer = L.geoJSON(currentDayFeatures, {
      style: () => ({
        color: '#24374d',
        weight: 2.4,
        fillColor: '#40566f',
        fillOpacity: 0.42,
        dashArray: '6 4',
        lineJoin: 'round'
      })
    }).addTo(map);

    try {
      const bounds = currentLayer.getBounds();
      if (bounds.isValid()) map.fitBounds(bounds, { ...getFitPadding(), maxZoom: FIT_BOUNDS_MAX_ZOOM });
    } catch (e) { console.error(e); }

    const raw = currentDayFeatures[0].properties.shadow_pct;
    const pct = raw !== null && raw !== undefined ? (raw <= 1 ? raw * 100 : raw) : null;
    updateRing(pct);
    hideStatus();

  } catch (err) {
    clearLayer();
    currentDayFeatures = [];
    resetSummary();
    showStatus('Error consultando los datos', true);
    console.error(err);
  }
}

/** Debounces shadow refresh + layer load after any control change */
function scheduleLoad() {
  clearTimeout(autoLoadTimeout);
  autoLoadTimeout = setTimeout(async () => {
    await refreshTerraceShadowColors();
    await loadSelection();
  }, 120);
}

/* ============================================================
   18. AUTOCOMPLETE SEARCH
   ============================================================ */

/** Returns the human-readable label for a catalog item */
function getItemDisplayLabel(item) {
  if (item?.type === 'address') return item.display_label || 'Dirección';
  return item.label_busqueda || item.rotulo_formateado || item.rotulo_original || `Terraza ${item.terraza_id}`;
}

function closeAC() {
  acList.innerHTML = '';
  acList.classList.remove('open');
  currentSuggestions = [];
  selectedSuggIdx = -1;
}

function renderAC(items) {
  currentSuggestions = items;
  selectedSuggIdx = -1;

  if (!items.length) { closeAC(); return; }

  acList.innerHTML = items.map((item, index) => {
    const isAddress = item.type === 'address';
    const title    = escapeHtml(getItemDisplayLabel(item));
    const subtitle = isAddress
      ? 'Dirección'
      : escapeHtml(item.direccion_resumen || item.nombre_via || 'Terraza');

    // Same pin SVG for both types
    const pinSVG = `<svg width="16" height="16" viewBox="0 0 24 24" fill="white" stroke="none"><path d="M12 2C8.13 2 5 5.13 5 9c0 5.25 7 13 7 13s7-7.75 7-13c0-3.87-3.13-7-7-7zm0 9.5c-1.38 0-2.5-1.12-2.5-2.5S10.62 6.5 12 6.5s2.5 1.12 2.5 2.5S13.38 11.5 12 11.5z"/></svg>`;

    return `
      <div class="ac-item" role="option" data-idx="${index}">
        <div class="ac-pin">${pinSVG}</div>
        <div class="ac-text">
          <div class="ac-title">${title}</div>
          <div class="ac-sub">${subtitle}</div>
        </div>
      </div>
    `;
  }).join('');

  acList.classList.add('open');

  acList.querySelectorAll('.ac-item').forEach(el => {
    el.addEventListener('mousedown', e => { e.preventDefault(); selectSuggestion(Number(el.dataset.idx)); });
    el.addEventListener('touchend',  e => { e.preventDefault(); selectSuggestion(Number(el.dataset.idx)); });
  });
}

function highlightAC() {
  acList.querySelectorAll('.ac-item').forEach((el, i) => {
    el.classList.toggle('active', i === selectedSuggIdx);
  });
}

/**
 * Searches both address and terrace catalogs.
 * Results order: address-starts, address-contains, terrace-starts, terrace-contains.
 */
function searchCatalog(query) {
  const q = normalizeText(query);
  if (!q) return [];

  const addressStarts   = [], addressContains   = [];
  const terraceStarts   = [], terraceContains   = [];

  for (const item of addressCatalog) {
    if (!item._search_blob.includes(q)) continue;
    (normalizeText(item.display_label).startsWith(q) ? addressStarts : addressContains).push(item);
  }

  for (const item of rotulosCatalog) {
    if (!item._search_blob.includes(q)) continue;
    (normalizeText(getItemDisplayLabel(item)).startsWith(q) ? terraceStarts : terraceContains).push(item);
  }

  return [...addressStarts, ...addressContains, ...terraceStarts, ...terraceContains].slice(0, 12);
}

function selectSuggestion(index) {
  const item = currentSuggestions[index];
  if (!item) return;

  if (item.type === 'address') { selectAddressResult(item); return; }

  const feature = findTerraceFeatureById(item.terraza_id);
  if (feature) { selectTerraceFeature(feature); return; }

  // Fallback: select by ID when feature not yet loaded
  selectedTerraceId = item.terraza_id;
  selectedRotulo    = getItemDisplayLabel(item);

  searchInput.value = selectedRotulo;
  searchClear.classList.add('visible');
  closeAC();
  searchInput.blur();

  placeName.textContent = selectedRotulo;
  placeName.classList.remove('empty');
  setSheetState('mid');
  scheduleLoad();
}

/* ── Search input listeners ── */

searchInput.addEventListener('input', () => {
  const query = searchInput.value.trim();
  searchClear.classList.toggle('visible', query.length > 0);
  renderAC(searchCatalog(query));
});

searchInput.addEventListener('focus', () => {
  const query = searchInput.value.trim();
  if (query) renderAC(searchCatalog(query));
});

searchInput.addEventListener('keydown', e => {
  if (!acList.classList.contains('open')) {
    if (e.key === 'Enter') {
      const suggestions = searchCatalog(searchInput.value.trim());
      if (suggestions.length === 1) { e.preventDefault(); currentSuggestions = suggestions; selectSuggestion(0); }
    }
    return;
  }
  if (e.key === 'ArrowDown')  { e.preventDefault(); selectedSuggIdx = Math.min(selectedSuggIdx + 1, currentSuggestions.length - 1); highlightAC(); }
  else if (e.key === 'ArrowUp')   { e.preventDefault(); selectedSuggIdx = Math.max(selectedSuggIdx - 1, 0); highlightAC(); }
  else if (e.key === 'Enter')     { e.preventDefault(); selectSuggestion(selectedSuggIdx >= 0 ? selectedSuggIdx : (currentSuggestions.length === 1 ? 0 : -1)); }
  else if (e.key === 'Escape')    { closeAC(); }
});

searchInput.addEventListener('blur', () => setTimeout(() => closeAC(), 150));

searchClear.addEventListener('click', () => {
  searchInput.value = '';
  searchClear.classList.remove('visible');
  closeAC();

  selectedTerraceId      = null;
  selectedRotulo         = null;
  selectedTerraceFeature = null;

  placeName.textContent = 'Selecciona una terraza';
  placeName.classList.add('empty');
  terraceInfoSection.classList.add('hidden');

  clearLayer();
  resetSummary();
  renderTerracesLayer();
  searchInput.focus();
});

/* ============================================================
   19. CONTROLS (date + hour slider)
   ============================================================ */
function updateHour(hour) { hourBadge.textContent = `${pad2(hour)}:00`; }

dateInput.addEventListener('change', () => scheduleLoad());
dateInput.addEventListener('keydown', e => { if (e.key === 'Enter') loadSelection(); });

hourSlider.addEventListener('input', () => {
  const hour = clampHour(hourSlider.value);
  hourSlider.value = hour;
  updateHour(hour);
  scheduleLoad();
});

/* ============================================================
   20. RESPONSIVE CHECKS
   ============================================================ */
function checkDesktop() {
  const isDesktop = window.innerWidth >= 720;

  if (desktopLabel)       desktopLabel.style.display      = isDesktop ? 'block' : 'none';
  if (desktopFabDivider)  desktopFabDivider.style.display  = isDesktop ? 'block' : 'none';
  if (desktopGreenFilter) desktopGreenFilter.style.display = isDesktop ? 'flex'  : 'none';
  if (desktopTypeWrap)    desktopTypeWrap.style.display    = isDesktop ? 'block' : 'none';

  if (isDesktop) closeTypeDropdown('mobile');

  updateLegendPosition();
  updateLegendVisibility();
}

window.addEventListener('resize', () => {
  checkDesktop();
  if (typeFilterDropdown.classList.contains('open') && window.innerWidth < 720) {
    positionMobileTypeDropdown();
  }
});

document.getElementById('mobile-filters-bar')?.addEventListener('scroll', () => {
  if (typeFilterDropdown.classList.contains('open') && window.innerWidth < 720) {
    positionMobileTypeDropdown();
  }
});

/* ============================================================
   BOOT — Initialize everything in dependency order
   ============================================================ */
(async () => {
  showStatus('Cargando datos…', false, true);

  try {
    const { ymd, hour } = getInitialDateAndHour();
    dateInput.value  = ymd;
    hourSlider.value = hour;
    updateHour(hour);

    checkDesktop();
    resetSummary();
    setSheetState('peek', false);

    await centerMapByApproxLocation();
    await loadRotulosCatalog();
    await loadAddressCatalog();
    await loadTerracesGeojson();
    await initDuckDB();
    await refreshTerraceShadowColors();

    renderTerracesLayer();
    updateLegendPosition();
    updateLegendVisibility();
  } catch (err) {
    console.error('Boot error:', err);
  } finally {
    hideStatus();
  }
})();