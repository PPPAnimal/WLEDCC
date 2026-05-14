""" SA.py — WLEDCC Spectrum Analyzer
    By Bill Sullivan (SullySSignS)

    Exports SpectrumController — a self-contained SA engine that can be
    embedded in any Flet app (including WLEDCC) or run standalone via the
    thin SpectrumApp wrapper at the bottom of this file.

    Settings are saved to SA-config.json in AppData\\Roaming\\WLEDCC,
    the same folder used by WLEDCC.  Both apps share the same config file,
    so SA preferences are always in sync.

    Requirements: flet, numpy, soundcard  (win32gui NOT required)
"""

import flet as ft
try:
    import flet.canvas as cv
except Exception:
    cv = None

import threading
import time
import os
import sys
import json
import math
import random
import glob
import colorsys
import subprocess
import ctypes
import base64
import io

try:
    from PIL import Image as _PILImage, ImageDraw as _PILDraw, ImageFilter as _PILFilter, ImageFont as _PILFont
    _PIL_OK = True
except Exception:
    _PILImage  = None
    _PILDraw   = None
    _PILFilter = None
    _PILFont   = None
    _PIL_OK    = False

# Minimal 1×1 black PNG encoded as base64 — used as ft.Image placeholder so
# Flet's "must have src or src_base64" validation never fires at construction.
def _make_1x1_png_b64():
    import struct, zlib as _zl
    def _chunk(name, data):
        crc = struct.pack('>I', _zl.crc32(name + data) & 0xffffffff)
        return struct.pack('>I', len(data)) + name + data + crc
    png = (b'\x89PNG\r\n\x1a\n'
        + _chunk(b'IHDR', struct.pack('>IIBBBBB', 1, 1, 8, 2, 0, 0, 0))
        + _chunk(b'IDAT', _zl.compress(b'\x00\x00\x00\x00'))
        + _chunk(b'IEND', b''))
    return base64.b64encode(png).decode()
try:
    _HALLU_BLANK_B64 = _make_1x1_png_b64()
except Exception:
    _HALLU_BLANK_B64 = "iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAAAAAA6fptVAAAACklEQVQI12NgAAAAAgAB4iG8MwAAAABJRU5ErkJggg=="
del _make_1x1_png_b64

# Transparent 300×62 PNG used as the initial neon-VU canvas placeholder.
try:
    _buf = io.BytesIO()
    _PILImage.new("RGBA", (300, 62), (0, 0, 0, 0)).save(_buf, format="PNG")
    _NVU_BLANK_B64 = base64.b64encode(_buf.getvalue()).decode()
    del _buf
except Exception:
    _NVU_BLANK_B64 = _HALLU_BLANK_B64

# ── PIL-based canvas for Modern/Neon VU modes ─────────────────────────────────
# In Flet 0.84, cv.Canvas shapes are full @control objects (each with a unique
# ControlId).  Replacing canvas.shapes with a fresh list every frame forces the
# ObjectPatch differ to emit N removes + N adds — crushing FPS for complex
# scenes (100+ shapes/frame × 24 fps = ~5000 wire-ops/sec).
# _PilCanvas renders the same shape objects to a single PNG image and pushes one
# data-URI ft.Image update per frame, restoring smooth playback.  All existing
# renderer functions work unchanged — they still build cv.Rect/Circle/Path
# objects and assign them to self._neon_vu_canvas.shapes.

def _pil_color(c) -> tuple:
    """Parse Flet 0.84 color value to RGBA PIL tuple.

    Handles '#rrggbb', '#aarrggbb', 'color,opacity' (Flet 0.84 with_opacity),
    and Flutter named colors: 'white', 'white60', 'black', 'transparent', etc.
    """
    if c is None:
        return (255, 255, 255, 255)
    s = str(c).strip()

    # Flet 0.84 with_opacity() returns "color,opacity" e.g. "#00EEFF,0.45"
    if ',' in s:
        color_part, _, opacity_part = s.rpartition(',')
        base = _pil_color(color_part.strip())
        try:
            opacity = max(0.0, min(1.0, float(opacity_part.strip())))
        except ValueError:
            opacity = 1.0
        return (base[0], base[1], base[2], int(base[3] * opacity))

    # Flutter / Flet named colors
    sl = s.lower()
    if sl == 'transparent':                       return (0,   0,   0,   0)
    if sl in ('white', 'ffffff'):                 return (255, 255, 255, 255)
    if sl in ('black', '000000'):                 return (0,   0,   0,   255)
    if sl.startswith('white') and sl[5:].isdigit():
        return (255, 255, 255, round(int(sl[5:]) / 100 * 255))
    if sl.startswith('black') and sl[5:].isdigit():
        return (0, 0, 0, round(int(sl[5:]) / 100 * 255))

    s = s.lstrip('#')
    try:
        if len(s) == 6:
            r, g, b = int(s[0:2], 16), int(s[2:4], 16), int(s[4:6], 16)
            return (r, g, b, 255)
        if len(s) == 8:    # Flutter ARGB (#aarrggbb)
            a, r, g, b = int(s[0:2], 16), int(s[2:4], 16), int(s[4:6], 16), int(s[6:8], 16)
            return (r, g, b, a)
    except Exception:
        pass
    return (200, 200, 200, 180)


# Font cache: (size_px, bold, italic) → PIL ImageFont or None
_PIL_FONT_CACHE: dict = {}

def _pil_get_font(size_px: int, bold: bool = False, italic: bool = False):
    """Return a PIL ImageFont for *size_px*, loading from Windows Fonts on first call."""
    key = (size_px, bold, italic)
    if key in _PIL_FONT_CACHE:
        return _PIL_FONT_CACHE[key]
    font = None
    if _PILFont is not None:
        try:
            _wf = os.path.join(os.environ.get('WINDIR', 'C:\\Windows'), 'Fonts')
            _candidates = []
            if bold and italic:  _candidates = ['arialbi.ttf', 'seguisbi.ttf']
            elif bold:           _candidates = ['arialbd.ttf', 'segoeuib.ttf', 'calibrib.ttf']
            elif italic:         _candidates = ['ariali.ttf',  'seguisli.ttf']
            _candidates += ['arial.ttf', 'segoeui.ttf', 'calibri.ttf', 'verdana.ttf']
            for _fn in _candidates:
                try:
                    font = _PILFont.truetype(os.path.join(_wf, _fn), size=max(6, size_px))
                    break
                except Exception:
                    pass
            if font is None:
                try:   font = _PILFont.load_default(size=max(6, size_px))
                except Exception: pass
        except Exception:
            pass
    _PIL_FONT_CACHE[key] = font
    return font


def _pil_draw_path(draw, elements, color, is_fill, sw, scale=1, ox=0, oy=0):
    """Execute Flet Path elements onto *draw*; coords scaled by *scale* and offset by (ox, oy)."""
    sub_paths, closed_flags, current = [], [], []
    for elem in elements:
        t = getattr(elem, '_type', None) or type(elem).__name__
        if t == 'MoveTo':
            if current:
                sub_paths.append(current); closed_flags.append(False)
            current = [(elem.x * scale - ox, elem.y * scale - oy)]
        elif t == 'LineTo':
            current.append((elem.x * scale - ox, elem.y * scale - oy))
        elif t == 'Close':
            if current:
                sub_paths.append(current); closed_flags.append(True)
                current = []
    if current:
        sub_paths.append(current); closed_flags.append(False)
    for pts, closed in zip(sub_paths, closed_flags):
        if len(pts) < 2:
            continue
        if closed and is_fill and len(pts) >= 3:
            draw.polygon(pts, fill=color)
        elif closed:
            draw.polygon(pts, outline=color)
        else:
            draw.line(pts, fill=color, width=sw)


def _pil_shape_bbox(shape, scale):
    """Return (x0, y0, x1, y1) bounding box for *shape* at *scale*× pixel coordinates.

    Returns None when the bounds cannot be computed (caller should use full canvas).
    The returned box is un-clamped; caller clips it to canvas size before use.
    """
    cls   = type(shape).__name__
    paint = getattr(shape, 'paint', None)
    sw    = max(1.0, (getattr(paint, 'stroke_width', 1) or 1) * scale)
    pad   = int(sw / 2) + 2   # stroke radius + 1px margin

    if cls == 'Rect':
        x0 = int(shape.x * scale) - pad
        y0 = int(shape.y * scale) - pad
        x1 = int((shape.x + shape.width)  * scale) + pad + 1
        y1 = int((shape.y + shape.height) * scale) + pad + 1
        return (x0, y0, x1, y1)
    if cls == 'Circle':
        cx, cy = shape.x * scale, shape.y * scale
        r = shape.radius * scale
        return (int(cx - r) - pad, int(cy - r) - pad, int(cx + r) + pad + 1, int(cy + r) + pad + 1)
    if cls == 'Oval':
        x0 = int(shape.x * scale) - pad
        y0 = int(shape.y * scale) - pad
        x1 = int((shape.x + shape.width)  * scale) + pad + 1
        y1 = int((shape.y + shape.height) * scale) + pad + 1
        return (x0, y0, x1, y1)
    if cls == 'Line':
        xs = sorted([shape.x1 * scale, shape.x2 * scale])
        ys = sorted([shape.y1 * scale, shape.y2 * scale])
        return (int(xs[0]) - pad, int(ys[0]) - pad, int(xs[1]) + pad + 1, int(ys[1]) + pad + 1)
    if cls == 'Path':
        xs, ys = [], []
        for elem in shape.elements:
            t = type(elem).__name__
            if t in ('MoveTo', 'LineTo'):
                xs.append(elem.x * scale); ys.append(elem.y * scale)
        if xs:
            return (int(min(xs)) - pad, int(min(ys)) - pad,
                    int(max(xs)) + pad + 1, int(max(ys)) + pad + 1)
    if cls == 'Text':
        style  = getattr(shape, 'style', None)
        sz     = float(getattr(style, 'size', 9) or 9) * scale
        txt    = str(getattr(shape, 'value', '') or '')
        est_w  = int(len(txt) * sz * 0.68) + 4
        est_h  = int(sz * 1.25) + 4
        aln    = getattr(shape, 'alignment', None)
        ax     = float(getattr(aln, 'x', 0.0) if aln else 0.0)
        ay     = float(getattr(aln, 'y', 0.0) if aln else 0.0)
        cx     = int(shape.x * scale)
        cy     = int(shape.y * scale)
        x0     = cx - int(est_w * (ax + 1) / 2) - pad
        y0     = cy - int(est_h * (ay + 1) / 2) - pad
        return (x0, y0, x0 + est_w + pad * 2, y0 + est_h + pad * 2)
    return None


def _pil_draw_shape(draw, shape, scale, ox=0, oy=0):
    """Draw one Flet canvas Shape onto *draw*.

    All coordinates are multiplied by *scale* then shifted by (ox, oy) so that
    the caller can draw into a tight bounding-box layer and composite it onto the
    main canvas at (ox, oy).
    """
    paint   = getattr(shape, 'paint', None)
    c       = _pil_color(getattr(paint, 'color', None) if paint else None)
    sw      = max(1, round((getattr(paint, 'stroke_width', 1) or 1) * scale))
    is_fill = (getattr(paint, 'style', None) == ft.PaintingStyle.FILL)
    cls     = type(shape).__name__

    def _sx(v): return v * scale - ox
    def _sy(v): return v * scale - oy

    if cls == 'Rect':
        x = _sx(shape.x);  y = _sy(shape.y)
        w = shape.width * scale;  h = shape.height * scale
        br = getattr(shape, 'border_radius', None)
        r  = 0
        try:
            r = int(round((getattr(br, 'top_left', 0) or 0) * scale))
        except Exception:
            pass
        bbox = [x, y, x + w - 1, y + h - 1]
        try:
            if r > 0:
                if is_fill: draw.rounded_rectangle(bbox, radius=r, fill=c)
                else:       draw.rounded_rectangle(bbox, radius=r, outline=c, width=sw)
            else:
                if is_fill: draw.rectangle(bbox, fill=c)
                else:       draw.rectangle(bbox, outline=c, width=sw)
        except Exception:
            if is_fill: draw.rectangle(bbox, fill=c)
            else:       draw.rectangle(bbox, outline=c, width=sw)

    elif cls == 'Circle':
        cx, cy = _sx(shape.x), _sy(shape.y)
        rad = shape.radius * scale
        bbox = [cx - rad, cy - rad, cx + rad, cy + rad]
        if is_fill: draw.ellipse(bbox, fill=c)
        else:       draw.ellipse(bbox, outline=c, width=sw)

    elif cls == 'Oval':
        x = _sx(shape.x);  y = _sy(shape.y)
        w = shape.width * scale;  h = shape.height * scale
        if is_fill: draw.ellipse([x, y, x + w, y + h], fill=c)
        else:       draw.ellipse([x, y, x + w, y + h], outline=c, width=sw)

    elif cls == 'Line':
        draw.line([(_sx(shape.x1), _sy(shape.y1)), (_sx(shape.x2), _sy(shape.y2))],
                fill=c, width=sw)

    elif cls == 'Path':
        _pil_draw_path(draw, shape.elements, c, is_fill, sw, scale, ox=ox, oy=oy)

    elif cls == 'Text':
        txt = str(getattr(shape, 'value', '') or '')
        if not txt:
            return
        style  = getattr(shape, 'style', None)
        sz_pt  = float(getattr(style, 'size', 9) or 9)
        wt     = str(getattr(style, 'weight', '') or '')
        bold   = wt.lower() in ('bold', 'w700', 'w800', 'w900') or (wt.isdigit() and int(wt) >= 700)
        italic = bool(getattr(style, 'italic', False))
        tc     = _pil_color(getattr(style, 'color', None) if style else None)
        font   = _pil_get_font(max(6, round(sz_pt * scale)), bold, italic)
        aln    = getattr(shape, 'alignment', None)
        ax     = float(getattr(aln, 'x', 0.0) if aln else 0.0)
        ay     = float(getattr(aln, 'y', 0.0) if aln else 0.0)
        h_anc  = 'l' if ax < -0.3 else ('r' if ax > 0.3 else 'm')
        v_anc  = 'a' if ay < -0.3 else ('d' if ay > 0.3 else 'm')
        xy     = (_sx(shape.x), _sy(shape.y))
        try:
            draw.text(xy, txt, fill=tc, font=font, anchor=h_anc + v_anc)
        except Exception:
            try: draw.text(xy, txt, fill=tc, font=font)
            except Exception: pass


# LANCZOS resampling filter — handles both old and new Pillow API.
try:
    _rs = getattr(_PILImage, "Resampling", None)
    _LANCZOS = getattr(_rs or _PILImage, "LANCZOS", None) or getattr(_PILImage, "ANTIALIAS", None)
except Exception:
    _LANCZOS = None


class _PilGradPolyline:
    """Gradient-coloured polyline for _PilCanvas.

    Draws the entire polyline in one PIL call (no per-segment joins = no blob
    artefacts at shared endpoints) then colourises each pixel column using a
    numpy X-axis gradient.  Cost per glow layer: one mask draw + two numpy
    broadcasts + one alpha_composite — independent of point count.
    """

    def __init__(self, points, color_fn, glow_layers, canvas_w):
        """
        points:      list of (x, y) unscaled canvas-coord tuples
        color_fn:    callable(frac: float) -> (R, G, B) int tuple at X-fraction 0..1
        glow_layers: list of (stroke_width_unscaled, alpha_0_to_1) ordered
                    outer-glow first (wide+faint → narrow+bright)
        canvas_w:    unscaled canvas width for X-fraction mapping
        """
        self.points      = points
        self.color_fn    = color_fn
        self.glow_layers = glow_layers
        self.canvas_w    = float(canvas_w)

    def render(self, canvas, scale, CW, CH):
        """Composite this gradient polyline onto *canvas* (RGBA PIL Image at *scale*×)."""
        if not _PIL_OK or len(self.points) < 2:
            return
        try:
            import numpy as np
            S      = scale
            max_sw = max((sw for sw, _ in self.glow_layers), default=1.0)
            pad    = int(max_sw * S / 2) + 2
            xs     = [p[0] * S for p in self.points]
            ys     = [p[1] * S for p in self.points]
            x0     = max(0, int(min(xs)) - pad)
            y0     = max(0, int(min(ys)) - pad)
            x1     = min(CW, int(max(xs)) + pad + 1)
            y1     = min(CH, int(max(ys)) + pad + 1)
            if x1 <= x0 or y1 <= y0:
                return
            bw, bh = x1 - x0, y1 - y0

            # Precompute RGB colour for every pixel column in the bbox
            rgb_map = np.zeros((bw, 3), dtype=np.uint8)
            for xi in range(bw):
                frac = (x0 + xi) / max(1.0, CW - 1)
                r, g, b = self.color_fn(frac)
                rgb_map[xi] = (r, g, b)

            # Points offset into bbox-local coords at render scale
            pts_local = [(p[0] * S - x0, p[1] * S - y0) for p in self.points]

            for sw, alpha in self.glow_layers:
                if alpha <= 0.0:
                    continue
                sw_px  = max(1, round(sw * S))
                a_mult = min(1.0, float(alpha))

                # Whole polyline onto a greyscale alpha mask — one draw call, no join blobs
                mask_img  = _PILImage.new("L", (bw, bh), 0)
                mask_draw = _PILDraw.Draw(mask_img)
                try:
                    mask_draw.line(pts_local, fill=255, width=sw_px, joint="curve")
                except TypeError:
                    mask_draw.line(pts_local, fill=255, width=sw_px)

                mask_arr = np.array(mask_img, dtype=np.float32)  # shape (bh, bw)

                # Build RGBA: broadcast column colours, alpha from mask × layer opacity
                rgba_arr           = np.zeros((bh, bw, 4), dtype=np.uint8)
                rgba_arr[:, :, :3] = rgb_map[np.newaxis, :, :]   # (bw,3) → (bh,bw,3)
                rgba_arr[:, :, 3]  = np.clip(mask_arr * a_mult, 0, 255).astype(np.uint8)

                layer = _PILImage.fromarray(rgba_arr, "RGBA")
                canvas.alpha_composite(layer, dest=(x0, y0))
        except Exception:
            pass


class _PilCanvas:
    """Render Flet canvas shapes to a PNG data URI via PIL.

    Each shape is drawn into a tight bounding-box RGBA layer, then composited
    onto the main canvas via alpha_composite (true SRC_OVER Porter-Duff).  This
    gives correct semi-transparent blending without the cost of full-size
    (600×124) layers — a 10-px orb uses a ~60×60 layer instead.

    Pipeline: allocate 2× canvas → per-shape tight-bbox composite → luminance-
    masked neon bloom (numpy) → LANCZOS resize to native size → PNG data URI.
    """

    SCALE = 2       # supersample factor — render at 2×, display at 1×
    BLOOM = True    # additive Gaussian glow for neon look

    def __init__(self, width: int, height: int, image_ctrl):
        self.shapes    = []
        self._w        = int(width)
        self._h        = int(height)
        self._img_ctrl = image_ctrl

    def update(self):
        if not _PIL_OK:
            return
        try:
            S  = self.SCALE
            CW = self._w * S   # canvas width at 2×
            CH = self._h * S   # canvas height at 2×
            canvas = _PILImage.new("RGBA", (CW, CH), (0, 0, 0, 0))

            for shape in self.shapes:
                try:
                    if isinstance(shape, _PilGradPolyline):
                        shape.render(canvas, S, CW, CH)
                        continue
                    raw_bbox = _pil_shape_bbox(shape, S)
                    # Clamp to canvas bounds
                    if raw_bbox is not None:
                        x0 = max(0, raw_bbox[0]); y0 = max(0, raw_bbox[1])
                        x1 = min(CW, raw_bbox[2]); y1 = min(CH, raw_bbox[3])
                    else:
                        x0, y0, x1, y1 = 0, 0, CW, CH
                    if x1 <= x0 or y1 <= y0:
                        continue
                    lw, lh = x1 - x0, y1 - y0
                    layer = _PILImage.new("RGBA", (lw, lh), (0, 0, 0, 0))
                    draw  = _PILDraw.Draw(layer, mode="RGBA")
                    _pil_draw_shape(draw, shape, S, ox=x0, oy=y0)
                    canvas.alpha_composite(layer, dest=(x0, y0))
                except Exception:
                    pass

            # Neon bloom: only bloom pre-multiply-bright pixels to avoid amplifying
            # faint full-canvas overlays (beat-flash tints, background hazes).
            if self.BLOOM and _PILFilter is not None:
                try:
                    import numpy as np
                    a_arr   = np.array(canvas, dtype=np.float32)
                    alpha_f = a_arr[..., 3:4] / 255.0
                    pm_rgb  = a_arr[..., :3] * alpha_f
                    lum     = (0.299 * pm_rgb[..., 0] +
                            0.587 * pm_rgb[..., 1] +
                            0.114 * pm_rgb[..., 2])
                    mask    = np.clip(lum / 80.0, 0.0, 1.0)[..., np.newaxis]
                    bloom_src = _PILImage.fromarray(
                        np.clip(a_arr * mask, 0, 255).astype(np.uint8), "RGBA")
                    glow    = bloom_src.filter(_PILFilter.GaussianBlur(radius=S * 1.2))
                    g_arr   = np.array(glow, dtype=np.float32)
                    bloomed = np.clip(a_arr + g_arr * 0.40, 0, 255).astype(np.uint8)
                    canvas  = _PILImage.fromarray(bloomed, "RGBA")
                except Exception:
                    pass

            out = canvas.resize((self._w, self._h), _LANCZOS)
            buf = io.BytesIO()
            out.save(buf, format="PNG", compress_level=1)
            self._img_ctrl.src = buf.getvalue()   # Flet 0.84 accepts raw bytes
            self._img_ctrl.update()
        except Exception:
            pass


# ── Window size constants ─────────────────────────────────────────────────────
_SA_COMPACT_W = 410   # width when only the SA display is shown
_SA_COMPACT_H = 140   # height when only the SA display is shown
_SA_MENU_W    = 410   # width when a settings panel is open
_SA_MENU_H    = 780   # height for main settings panel  (SA + ~620px panel)
_SA_IDLE_H    = 760   # height for idle-effects panel   (SA + ~600px panel)
_SA_NATIVE_W  = 300   # spectrum box native width  (scale reference)
_SA_NATIVE_H  = 62    # spectrum box native height (scale reference)
_SA_MAX_FPS   = 60    # sliding-window audio loop supports up to 60 fps

# ── Paths ────────────────────────────────────────────────────────────────────
_VERSION_DIR = os.path.dirname(sys.executable if getattr(sys, "frozen", False) else os.path.abspath(__file__))
_DATA_DIR    = os.path.join(os.environ.get("APPDATA", _VERSION_DIR), "WLEDCC")
os.makedirs(_DATA_DIR, exist_ok=True)
SA_CONFIG_FILE = os.path.join(_DATA_DIR, "SA-config.json")

# ── Background image defaults per NVU mode ───────────────────────────────────
_NVU_BG_DEFAULTS = {
    "drift":   "BG Nebula Space.jpg",
    "retro":   "BG Brushed Metal.jpg",
    "custom":  "Gauge Yellow.jpg",
    "hud":     "BLANK",
    "rock":    "stage kiss.jpg",
    "bs":      "stage metallica.jpg",
    "cascade": "stage acdc2.jpg",
}
_NVU_CONTAIN_DEFAULTS = {"neon_cascade": True, "beat_saber": True}

# Color modes available for random cycling, per visualizer mode
_CM_RANDOM_POOL = {
    "beat_saber":   ("loop", "gradient"),
    "neon_cascade": ("loop", "gradient"),
    "rock_stage":   ("loop", "gradient", "loop_smoke", "gradient_smoke"),
}

# ── Mode hierarchy — single source of truth for the random-playlist tree ──────
#   Flat modes: {"key", "label"}
#   Multi-level modes add "submodes" → list of {"key","label","base_layers"}
#   base_layers: list of {"key","label"}
_HALLU_BASE_LAYERS = [
    {"key": "waveform",  "label": "Waveform"},
    {"key": "circle",    "label": "Circular Waveform"},
    {"key": "particles", "label": "Particles"},
    {"key": "bars",      "label": "Spectrum Bars"},
]
_MODE_HIERARCHY = [
    {
        "key": "classic_group",
        "label": "Classic",
        "submodes": [
            {"key": "classic",      "label": "Spectrum"},
            {"key": "vu",           "label": "VU (L/R)"},
            {"key": "cyber_city",   "label": "Cyber City"},
            {"key": "hud_reactor",  "label": "HUD Reactor"},
        ],
    },
    {
        "key": "vu_meters",
        "label": "VU Meters",
        "submodes": [
            {"key": "neon_drift",  "label": "Neon Drift"},
            {"key": "retro_tech",  "label": "Retro-Tech"},
            {"key": "custom_vu",   "label": "Custom VU"},
        ],
    },
    {
        "key": "modern",
        "label": "Modern",
        "submodes": [
            {"key": "beat_saber",   "label": "Beat Saber"},
            {"key": "neon_cascade", "label": "Neon Cascade"},
            {"key": "rock_stage",   "label": "Rock Stage"},
        ],
    },
    {
        "key": "hallucination",
        "label": "Hallucination",
        "submodes": [
            {"key": "mirror",   "label": "Recursive Mirror",       "base_layers": _HALLU_BASE_LAYERS},
            {"key": "chroma",   "label": "Chromatic Aberration",   "base_layers": _HALLU_BASE_LAYERS},
            {"key": "perlin",   "label": "Perlin Flow Fields",     "base_layers": _HALLU_BASE_LAYERS},
            {"key": "morph",    "label": "Geometry Morphing",      "base_layers": _HALLU_BASE_LAYERS},
        ],
    },
]


class SpectrumController:
    """Self-contained spectrum analyzer engine.

    Parameters
    ----------
    page          : ft.Page  — the Flet page to render into.
    version_dir   : str      — directory containing background .jpg assets.
    legacy_config : dict     — SA settings dict from a parent app's cache
                            (used as fallback when SA-config.json is absent).
    on_save       : callable — optional hook called after save_config() so the
                            parent app (WLEDCC) can trigger its own cache save.
    log_fn        : callable — optional log(msg, color) function; falls back to
                            updating the built-in status text + print().
    menu_expand_fn  : callable(w, h) — called when a settings panel opens
                                    (standalone SA uses this to resize the window).
    menu_collapse_fn: callable()     — called when a settings panel closes.
    """

    @staticmethod
    def _random_tree_default():
        """All-enabled random-playlist tree, built from _MODE_HIERARCHY."""
        tree = {}
        for mode in _MODE_HIERARCHY:
            if "submodes" not in mode:
                tree[mode["key"]] = True
            else:
                sub = {"enabled": True}
                for sm in mode["submodes"]:
                    if "base_layers" not in sm:
                        sub[sm["key"]] = True          # container group leaf
                    else:
                        sub[sm["key"]] = {"enabled": True}
                        for bl in sm["base_layers"]:
                            sub[sm["key"]][bl["key"]] = True
                tree[mode["key"]] = sub
        return tree

    @staticmethod
    def _load_random_tree(raw):
        """Merge a raw JSON dict into the live _MODE_HIERARCHY shape.

        Stale keys (modes/submodes removed from the hierarchy) are silently
        dropped.  Missing keys default to True (enabled).
        """
        tree = {}
        for mode in _MODE_HIERARCHY:
            mk = mode["key"]
            if "submodes" not in mode:
                v = raw.get(mk, True)
                tree[mk] = bool(v) if isinstance(v, bool) else True
            else:
                raw_sub = raw.get(mk, {})
                if not isinstance(raw_sub, dict):
                    raw_sub = {}
                sub = {"enabled": bool(raw_sub.get("enabled", True))}
                for sm in mode["submodes"]:
                    sk = sm["key"]
                    if "base_layers" not in sm:
                        v = raw_sub.get(sk, True)
                        sub[sk] = bool(v) if isinstance(v, bool) else True
                    else:
                        raw_sm = raw_sub.get(sk, {})
                        if not isinstance(raw_sm, dict):
                            raw_sm = {}
                        sm_dict = {"enabled": bool(raw_sm.get("enabled", True))}
                        for bl in sm["base_layers"]:
                            bk = bl["key"]
                            sm_dict[bk] = bool(raw_sm.get(bk, True))
                        sub[sk] = sm_dict
                tree[mk] = sub
        return tree

    def __init__(self, page: ft.Page, version_dir: str,
                legacy_config=None, on_save=None, log_fn=None,
                menu_expand_fn=None, menu_collapse_fn=None,
                debug_mode_fn=None):
        self.page    = page
        self.running = True
        self._own_hwnd          = None   # set once by _start_pos_tracker
        self._own_rect          = None   # ctypes.wintypes.RECT, physical px, refreshed every 200 ms
        self._own_dpi           = 96
        self._pos_tracker_stop  = False
        self._aspect_lock       = True   # mirrored from SpectrumApp; persisted in every save_config
        self._event_loop        = None   # captured in start(); used by _schedule_render
        self._version_dir       = version_dir
        self._on_save           = on_save
        self._log_fn            = log_fn
        self._menu_expand_fn    = menu_expand_fn
        self._menu_collapse_fn  = menu_collapse_fn
        # Callable that returns bool: True when debug mode is active.
        # Used to show/hide the status text overlay in embedded mode.
        self._debug_mode_fn     = debug_mode_fn
        
        # ── Debug mode state (for standalone mode when no debug_mode_fn provided) ──
        self._debug_mode = bool(self._debug_mode_fn()) if self._debug_mode_fn else True
        
        # ── Spectrum analyzer state ───────────────────────────────────────
        self._spec_bands            = 32
        self._spec_analysis_bands   = 32
        self._spec_levels           = 16
        self._spec_bars             = [0.0] * 32
        self._spec_peaks            = [0.0] * 32
        self._spec_peak_hold        = [0]   * 32
        self._spec_band_avg         = [0.0] * 32
        self._spec_segments         = []
        self._spec_gain             = 1.0
        self._spec_target_fps       = _SA_MAX_FPS
        self._spec_actual_fps       = 0.0
        self._spec_fps_label        = None
        self._spec_fps_track_ts     = 0.0
        self._spec_fps_frame_count  = 0
        self._spec_sensitivity      = 0.85
        self._spec_reactivity       = 1.0
        self._spec_bar_decay        = 2.0
        self._spec_peak_decay       = 1.0
        self._spec_mode             = "classic"
        self._spec_mode_random_enabled        = True
        self._spec_mode_random_on_song        = True
        self._spec_mode_random_current        = "classic"
        self._spec_mode_random_cycle_seconds  = 60.0
        self._menu_rebuild_requested          = False
        self._spec_random_tree                = self._random_tree_default()
        self._spec_random_current_leaf        = None   # (mode, submode, base_layer) tuple
        self._spec_mode_random_played         = set()  # set of (mode, submode, base_layer) tuples
        self._spec_mode_random_next_ts        = time.monotonic() + 60.0
        self._spec_mode_song_silence_seconds  = 2.0
        self._spec_mode_song_switch_armed     = True
        self._spec_mode_song_debounce         = 0
        self._spec_nvu_drift_bg     = _NVU_BG_DEFAULTS["drift"]
        self._spec_nvu_retro_bg     = _NVU_BG_DEFAULTS["retro"]
        self._spec_nvu_custom_bg    = _NVU_BG_DEFAULTS["custom"]
        self._spec_nvu_hud_bg       = _NVU_BG_DEFAULTS["hud"]
        self._spec_nvu_rock_bg      = _NVU_BG_DEFAULTS["rock"]
        self._spec_nvu_bs_bg        = _NVU_BG_DEFAULTS["bs"]
        self._spec_nvu_cascade_bg   = _NVU_BG_DEFAULTS["cascade"]
        self._spec_nvu_bg_contain   = dict(_NVU_CONTAIN_DEFAULTS)
        self._spec_nvu_bg_force_reload = False
        self._spec_bs_color_mode    = "random"  # active color mode (used by renderer)
        self._spec_color_mode_per_mode = {"beat_saber": "random", "neon_cascade": "random", "rock_stage": "random", "hallucination": "random"}
        self._spec_display_hue      = 0.0          # 0-1 HSV hue of current render
        self._spec_capture_channels = 2
        self._spec_sample_rate      = 48000
        self._spec_sampling_enabled = True
        self._spec_vu_gain          = 0.18
        self._spec_vu_left          = 0.0
        self._spec_vu_right         = 0.0
        self._spec_vu_peak_left     = 0.0
        self._spec_vu_peak_right    = 0.0
        self._spec_vu_peak_hold_left  = 0
        self._spec_vu_peak_hold_right = 0
        # Central per-frame audio snapshot — written by _compute_audio_frame(), read by all modes
        self._sa_raw_bass       = 0.0   # bar[0] clamped 0-1
        self._sa_mono_vu        = 0.0   # (L+R)/2 VU, 0-1
        self._sa_bass           = 0.0   # band-extracted bass, 0-1
        self._sa_mid            = 0.0
        self._sa_treble         = 0.0
        self._sa_beat           = False
        self._sa_peak           = 0.0
        self._sa_smth_bass      = 0.0   # shared smoother for canvas modes
        self._sa_smth_vu        = 0.0
        self._sa_prev_smth_bass = 0.0
        self._sa_beat_detected  = False  # unified rising-edge beat signal
        self._sa_beat_bass_avg  = 0.0   # adaptive running average for beat threshold
        self._sa_beat_prev      = False  # previous frame beat state
        self._sa_beat_sens      = 1.0   # loaded from active mode's per-mode config
        self._spec_idle_enabled     = True
        self._spec_idle_timeout     = 5.0
        self._spec_idle_effect      = "random"
        self._spec_idle_cycle_effects = ["pulse", "text", "pacman", "tetris",
                                        "invaders", "snake", "starwars"]
        self._spec_idle_speed       = 1.0
        self._spec_idle_random_current        = "pulse"
        self._spec_idle_random_cycle_seconds  = 10.0
        self._spec_idle_random_next_ts        = time.monotonic() + 10.0
        self._spec_idle_threshold   = 0.02
        self._spec_idle_active      = False
        self._spec_idle_cycle_done  = True
        self._spec_last_audio_ts    = time.monotonic()
        self._spec_idle_text        = " SPECTRUM ANALYZER "
        self._spec_idle_scroll      = 0
        self._spec_idle_phase       = 0.0
        self._spec_eq_freqs         = [60, 170, 310, 600, 1000, 3000, 6000, 12000, 14000, 15000]
        self._spec_eq_gains         = [1.0] * 10
        self._spec_log_once         = False
        self._spec_no_audio_warned  = False
        self._spec_audio_sources    = []
        self._spec_source_order     = []
        self._spec_selected_source  = None
        self._spec_profiles         = {}
        self._spec_source_changed   = False
        self._config_dirty               = False
        self._sa_session_backup_written  = False
        self._menu_open             = False
        self._settings_save_btn     = None
        self._settings_dirty_label  = None
        self._current_sf            = 1.0
        self._cm_rand_current       = {}   # mode_name -> active non-random cm
        self._cm_rand_beats         = {}   # mode_name -> beats since last change
        self._cm_rand_target        = {}   # mode_name -> beat count until next change
        self._cm_rand_next_ts       = {}   # mode_name -> monotonic time of next forced change
        self._spec_mode_configs     = {}   # config_path -> per-path settings snapshot
        self._spec_mode_transitioning = False
        self._spec_disabled         = False
        self._spec_render_mode      = "grid"
        self._spec_box_grid_size    = (300, 62)
        self._spec_box_graphics_size = (300, 62)
        self._spec_grid_content     = None
        self._spec_graphics_host    = None
        self._spec_graphics_layer   = None
        self._spec_graphics_ready   = False
        self._spec_graphics_stars   = []
        self._spec_graphics_lines   = []
        self._spec_graphics_view_size = (0, 0)
        self._spec_display_cleared  = False
        self._spec_np_patch_applied = False
        self._render_pending        = False   # guard: at most one queued render task

        # ── Hallucination state ───────────────────────────────────────────
        self._spec_hallu_submode               = "mirror"
        self._spec_hallu_params_per_submode    = {
            "mirror":   {"zoom": 0.85,   "rotDeg": 10.0,   "opacity": 1.0,    "beat_sens": 2.0,  "dim_thresh": 0.25},
            "chroma":   {"maxSplit": 14, "trail": 0.18},
            "perlin":   {"noiseScale": 0.012, "evolveRate": 0.30},
            "morph":    {"layers": 3, "jitter": 1.0, "beat_sens": 1.0},
        }
        self._spec_hallu_base_kind             = "waveform"
        self._spec_hallu_random_cycle_choices  = ["mirror","chroma","perlin","morph"]
        self._spec_hallu_random_cycle_seconds  = 60.0
        self._spec_hallu_random_current        = "mirror"
        self._spec_hallu_random_next_ts        = time.monotonic() + 60.0
        self._spec_hallu_song_switch_armed     = True
        self._menu_last_tab                    = 0
        self._spec_hallu_prev_frame            = None
        self._spec_hallu_aux                   = {}
        self._spec_hallu_bass_avg              = 0.0
        self._spec_hallu_auto_rot              = True
        self._spec_hallu_auto_spread           = True
        self._spec_hallu_auto_blur             = True

        self._spec_hallu_excited             = False
        self._spec_hallu_excited_ts          = 0.0
        self._spec_hallu_excited_prev       = False
        self._spec_hallu_rot_smooth        = 0.0
        self._hallu_img                        = None
        self._hallu_host                       = None

        # ── Neon VU Meter state ───────────────────────────────────────────
        self._neon_vu_left_smooth   = 0.0
        self._neon_vu_right_smooth  = 0.0
        self._neon_vu_theme         = "neon_drift"
        self._neon_vu_canvas        = None
        self._neon_vu_bg_image      = None
        self._neon_vu_host          = None

        # ── Load config then build controls ──────────────────────────────
        self.load_config(legacy_config)
        self._build_controls()

    # ── Public API ───────────────────────────────────────────────────────────

    @property
    def widget(self):
        """The SA Row (buttons + spectrum box) — embed this in any layout."""
        return self._sa_row

    @property
    def menu_host(self):
        """Column that holds the inline settings panel (hidden when idle)."""
        return self._menu_host

    @property
    def btn_overlay(self):
        """Hover button overlay — place in the outer unscaled Stack so buttons
        stay at native icon size when the SA display is zoomed."""
        return self._spec_btn_overlay

    @property
    def status_text(self):
        """ft.Text widget showing status messages (optional — add to layout)."""
        return self._status_text

    def start(self):
        """Start the background audio analyzer thread."""
        try:
            import asyncio
            self._event_loop = asyncio.get_running_loop()
        except Exception:
            self._event_loop = None
        threading.Thread(target=self._audio_analyzer_loop, daemon=True,
                        name="SA_AudioLoop").start()

    def stop(self):
        """Signal the audio analyzer thread to exit."""
        self.running = False

    def is_audio_detected(self):
        """Return True if live audio was seen within the last 2 s."""
        try:
            _age = time.monotonic() - float(self._spec_last_audio_ts)
            return (not bool(self._spec_idle_active)) and (_age <= 2.0)
        except Exception:
            return False

    # ── Config ───────────────────────────────────────────────────────────────

    def load_config(self, legacy_config=None, preserve_mode=False):
        """Load SA settings from SA-config.json.

        If the file is absent or empty and *legacy_config* is supplied (a dict
        from WLEDCC's cache), those values are used as a one-time migration
        fallback so existing preferences are not lost on first run.

        If *preserve_mode* is True the currently active display mode is kept
        and only its per-mode settings are reloaded (used by the Reload button).
        """
        _active_mode = self._spec_mode
        def _clamp(v, lo, hi, default):
            try:   return max(lo, min(hi, float(v)))
            except: return default

        try:
            with open(SA_CONFIG_FILE, "r", encoding="utf-8") as f:
                c = json.load(f)
        except Exception:
            c = {}
        self._config_dirty = False

        # One-time migration: use parent app's cached values when our own file
        # doesn't exist yet.
        if not c and legacy_config and isinstance(legacy_config, dict):
            c = dict(legacy_config)

        self._spec_selected_source = c.get("spec_audio_source", None)
        _src_order = c.get("spec_source_order", [])
        self._spec_source_order = [str(n) for n in _src_order if isinstance(n, str)]

        self._spec_profiles = {}
        _raw_profiles = c.get("spec_profiles", {})
        if isinstance(_raw_profiles, dict):
            for _k, _v in _raw_profiles.items():
                if not isinstance(_k, str) or not isinstance(_v, dict):
                    continue
                try:
                    self._spec_profiles[_k] = {
                        "sensitivity": _clamp(_v.get("sensitivity", 0.85), 0.1, 1.5, 0.85),
                        "reactivity":  _clamp(_v.get("reactivity",  1.0),  0.25, 3.0, 1.0),
                        "bar_decay":   _clamp(_v.get("bar_decay",   2.0),  0.1, 5.0, 2.0),
                        "peak_decay":  _clamp(_v.get("peak_decay",  1.0),  0.1, 5.0, 1.0),
                        "eq_gains":    [max(0.25, min(3.0, float(x)))
                                        for x in _v.get("eq_gains", [1.0] * 10)],
                    }
                except Exception:
                    continue

        self._spec_sensitivity  = _clamp(c.get("spec_sensitivity",  0.85), 0.1, 1.5, 0.85)
        self._spec_reactivity   = _clamp(c.get("spec_reactivity",   1.0),  0.25, 3.0, 1.0)
        self._spec_bar_decay    = _clamp(c.get("spec_bar_decay",    2.0),  0.1, 5.0, 2.0)
        self._spec_peak_decay   = _clamp(c.get("spec_peak_decay",   1.0),  0.1, 5.0, 1.0)
        self._spec_target_fps   = int(_clamp(c.get("spec_target_fps", _SA_MAX_FPS), 8, _SA_MAX_FPS, _SA_MAX_FPS))
        self._set_spec_analysis_bands(c.get("spec_analysis_bands", self._spec_bands),
                                    restart_audio=False, reset_now=True)
        _sr = int(_clamp(c.get("spec_sample_rate", 48000), 8000, 96000, 48000))
        self._spec_sample_rate  = _sr if _sr in (16000, 22050, 32000, 44100, 48000) else 48000
        self._spec_sampling_enabled = bool(c.get("spec_sampling_enabled", True))
        self._spec_mode_song_silence_seconds = _clamp(c.get("spec_mode_song_timeout", 2.0), 1.0, 15.0, 2.0)

        # Load global random-cycle flags (with migration from old "random"/"random_song" mode values)
        self._spec_mode_random_enabled = bool(c.get("spec_mode_random_enabled", True))
        self._spec_mode_random_on_song  = bool(c.get("spec_mode_random_on_song", True))
        try: self._spec_mode_random_cycle_seconds = max(5.0, min(3600.0,
                float(c.get("spec_mode_random_cycle_secs", 60.0))))
        except: pass

        if not preserve_mode:
            _mode = str(c.get("spec_mode", "classic")).lower()
            if _mode == "neon_vu":
                _mode = str(c.get("spec_neon_vu_theme", "neon_drift")).lower()
            # Migration: old "random"/"random_song" modes → flags
            if _mode == "random":
                self._spec_mode_random_enabled = True
                _mode = "classic"
            elif _mode == "random_song":
                self._spec_mode_random_on_song = True
                _mode = "classic"
            self._spec_mode = _mode if _mode in (
                "classic", "vu", "cyber_city", "beat_saber", "neon_drift", "retro_tech",
                "custom_vu", "hud_reactor", "neon_cascade", "rock_stage", "hallucination") else "classic"

        self._spec_nvu_drift_bg  = c.get("spec_nvu_drift_bg",  _NVU_BG_DEFAULTS["drift"])
        self._spec_nvu_retro_bg  = c.get("spec_nvu_retro_bg",  _NVU_BG_DEFAULTS["retro"])
        self._spec_nvu_custom_bg = c.get("spec_nvu_custom_bg", _NVU_BG_DEFAULTS["custom"])
        self._spec_nvu_hud_bg    = c.get("spec_nvu_hud_bg",    _NVU_BG_DEFAULTS["hud"])
        self._spec_nvu_rock_bg   = c.get("spec_nvu_rock_bg",   _NVU_BG_DEFAULTS["rock"])
        self._spec_nvu_bs_bg     = c.get("spec_nvu_bs_bg",     _NVU_BG_DEFAULTS["bs"])
        self._spec_nvu_cascade_bg= c.get("spec_nvu_cascade_bg",_NVU_BG_DEFAULTS["cascade"])
        _bc = c.get("spec_nvu_bg_contain", _NVU_CONTAIN_DEFAULTS)
        self._spec_nvu_bg_contain = dict(_bc) if isinstance(_bc, dict) else dict(_NVU_CONTAIN_DEFAULTS)
        _bg_rename = {
            "nebula space.jpg":  "BG Nebula Space.jpg",
            "brushed metal.jpg": "BG Brushed Metal.jpg",
            "planets space.jpg": "BG Planets Space.jpg",
            "retro blue.jpg":    "Gauge Blue.jpg",
            "retro yellow.jpg":  "Gauge Yellow.jpg",
        }
        self._spec_nvu_drift_bg  = _bg_rename.get(self._spec_nvu_drift_bg.lower(),  self._spec_nvu_drift_bg)
        self._spec_nvu_retro_bg  = _bg_rename.get(self._spec_nvu_retro_bg.lower(),  self._spec_nvu_retro_bg)
        self._spec_nvu_custom_bg = _bg_rename.get(self._spec_nvu_custom_bg.lower(), self._spec_nvu_custom_bg)
        self._spec_nvu_hud_bg    = _bg_rename.get(self._spec_nvu_hud_bg.lower(),    self._spec_nvu_hud_bg)
        self._spec_nvu_rock_bg   = _bg_rename.get(self._spec_nvu_rock_bg.lower(),   self._spec_nvu_rock_bg)
        _valid_cm = ("loop", "gradient", "loop_smoke", "gradient_smoke", "random")
        _cm_map = c.get("spec_color_mode_per_mode", {})
        if isinstance(_cm_map, dict) and _cm_map:
            for _mk in ("beat_saber", "neon_cascade", "rock_stage"):
                _v = str(_cm_map.get(_mk, "random")).lower()
                self._spec_color_mode_per_mode[_mk] = _v if _v in _valid_cm else "random"
            _v = str(_cm_map.get("hallucination", "random")).lower()
            self._spec_color_mode_per_mode["hallucination"] = _v if _v in ("loop", "gradient", "random") else "random"
        else:
            # migrate legacy single value
            _cm = str(c.get("spec_bs_color_mode", "random")).lower()
            _cm = _cm if _cm in _valid_cm else "random"
            for _mk in ("beat_saber", "neon_cascade", "rock_stage"):
                self._spec_color_mode_per_mode[_mk] = _cm
        self._spec_bs_color_mode = self._spec_color_mode_per_mode.get(
            self._spec_mode, self._spec_color_mode_per_mode.get("beat_saber", "random"))

        _nvu = str(c.get("spec_neon_vu_theme", "neon_drift")).lower()
        self._neon_vu_theme = _nvu if _nvu in ("neon_drift", "retro_tech", "custom_vu", "hud_reactor", "beat_saber", "neon_cascade", "rock_stage") else "neon_drift"

        # ── Random playlist tree ──────────────────────────────────────────────
        _raw_tree = c.get("spec_random_tree")
        self._spec_random_tree = self._load_random_tree(
            _raw_tree if isinstance(_raw_tree, dict) else {}
        )

        # ── Hallucination dropdown state (needed to compute config path) ─────
        _valid_sub = ("mirror","chroma","perlin","morph")
        _hs = str(c.get("spec_hallu_submode", "mirror")).lower()
        self._spec_hallu_submode = "mirror" if _hs == "random" else (_hs if _hs in _valid_sub else "mirror")
        _hbk = str(c.get("spec_hallu_base_kind", "waveform")).lower()
        _valid_base = {bl["key"] for bl in _HALLU_BASE_LAYERS}
        self._spec_hallu_base_kind = _hbk if _hbk in _valid_base else "waveform"

        self._spec_idle_enabled = bool(c.get("spec_idle_enabled", True))
        self._spec_idle_timeout = _clamp(c.get("spec_idle_timeout", 5.0), 2.0, 30.0, 5.0)
        _idle_fx = str(c.get("spec_idle_effect", "random")).lower()
        self._spec_idle_effect  = _idle_fx if _idle_fx in (
            "random", "pulse", "text", "pacman", "tetris", "invaders", "snake", "starwars") else "random"
        self._spec_idle_speed   = _clamp(c.get("spec_idle_speed", 2.0), 0.25, 3.0, 2.0)

        _idle_cycle = c.get("spec_idle_cycle_effects", self._spec_idle_cycle_effects)
        if isinstance(_idle_cycle, list):
            _allowed = ["pulse", "text", "pacman", "tetris", "invaders", "snake", "starwars"]
            self._spec_idle_cycle_effects = [x for x in _idle_cycle if x in _allowed] or list(_allowed)

        _eq = c.get("spec_eq_gains", self._spec_eq_gains)
        if isinstance(_eq, list) and len(_eq) == len(self._spec_eq_freqs):
            try:
                self._spec_eq_gains = [max(0.25, min(3.0, float(v))) for v in _eq]
            except Exception:
                self._spec_eq_gains = [1.0] * len(self._spec_eq_freqs)

        if "__default__" not in self._spec_profiles:
            self._save_spec_profile(None)
        self._load_spec_profile(self._spec_selected_source)

        # Load per-path config store (with one-time migration from older save formats)
        _idle_keys = {"idle_timeout", "idle_effect", "idle_speed", "idle_cycle_effects"}
        self._spec_mode_configs = {}
        if "spec_mode_configs" in c:
            for _k, _v in c["spec_mode_configs"].items():
                if isinstance(_k, str) and isinstance(_v, dict):
                    self._spec_mode_configs[_k] = {ik: iv for ik, iv in _v.items()
                                                    if ik not in _idle_keys}
        else:
            # Migration: old spec_per_mode flat entries → new path keys
            for _mk, _mv in c.get("spec_per_mode", {}).items():
                if isinstance(_mk, str) and isinstance(_mv, dict):
                    self._spec_mode_configs[_mk] = {ik: iv for ik, iv in _mv.items()
                                                    if ik not in _idle_keys}
            # Migration: old flat hallu keys → extras on the active hallu path
            _hp = c.get("spec_hallu_params_per_submode", {})
            _hallu_path = f"hallucination/{self._spec_hallu_submode}/{self._spec_hallu_base_kind}"
            _h_base = dict(self._spec_mode_configs.get(_hallu_path, {}))
            _sub_params = dict(_hp.get(self._spec_hallu_submode, {})) if isinstance(_hp, dict) else {}
            _cm_map = c.get("spec_color_mode_per_mode", {})
            _cm_h = str(_cm_map.get("hallucination", "random") if isinstance(_cm_map, dict) else "random").lower()
            _valid_cm_h = ("loop", "gradient", "random")
            _h_base["extras"] = {
                "color_mode":           _cm_h if _cm_h in _valid_cm_h else "random",
                "auto_rot":      bool(c.get("spec_hallu_auto_rot",       True)),
                "auto_spread":   bool(c.get("spec_hallu_auto_spread",  True)),
                "auto_blur":     bool(c.get("spec_hallu_auto_blur",    True)),

                "params":        _sub_params,
            }
            self._spec_mode_configs[_hallu_path] = _h_base
        self._apply_per_mode_settings(_active_mode if preserve_mode else self._spec_mode, restart_audio=False)

        if not preserve_mode and (self._spec_mode_random_enabled or self._spec_mode_random_on_song):
            self._advance_random_mode()
            self._spec_mode_random_next_ts = time.monotonic() + max(1.0, self._spec_mode_random_cycle_seconds)
            self._spec_mode_song_switch_armed = True

        if os.path.basename(sys.argv[0]).lower().startswith("sa"):
            self._start_pos_tracker()

    def save_config(self, win_pos=None):
        """Persist SA settings to SA-config.json.

        *win_pos* is an optional dict (e.g. ``{"win_x": 100, "win_y": 200}``)
        supplied by the standalone SpectrumApp so window position is preserved
        alongside SA settings in the same file.
        """
        self._capture_per_mode_settings(self._spec_mode)
        try:
            c = {
                "spec_audio_source":       self._spec_selected_source,
                "spec_source_order":       list(self._spec_source_order),
                "spec_profiles":           json.loads(json.dumps(self._spec_profiles)),
                "spec_sensitivity":        float(self._spec_sensitivity),
                "spec_reactivity":         float(self._spec_reactivity),
                "spec_bar_decay":          float(self._spec_bar_decay),
                "spec_peak_decay":         float(self._spec_peak_decay),
                "spec_target_fps":         int(self._spec_target_fps),
                "spec_analysis_bands":     int(self._spec_analysis_bands),
                "spec_sample_rate":        int(self._spec_sample_rate),
                "spec_sampling_enabled":   bool(self._spec_sampling_enabled),
                "spec_mode":                    str(self._spec_mode),
                "spec_mode_random_enabled":     bool(self._spec_mode_random_enabled),
                "spec_mode_random_on_song":     bool(self._spec_mode_random_on_song),
                "spec_mode_random_cycle_secs":  float(self._spec_mode_random_cycle_seconds),
                "spec_neon_vu_theme":      str(self._neon_vu_theme),
                "spec_mode_song_timeout":  float(self._spec_mode_song_silence_seconds),
                "spec_random_tree":        self._load_random_tree(self._spec_random_tree),
                "spec_nvu_drift_bg":       self._spec_nvu_drift_bg,
                "spec_nvu_retro_bg":       self._spec_nvu_retro_bg,
                "spec_nvu_custom_bg":      self._spec_nvu_custom_bg,
                "spec_nvu_hud_bg":         self._spec_nvu_hud_bg,
                "spec_nvu_rock_bg":        self._spec_nvu_rock_bg,
                "spec_nvu_bs_bg":          self._spec_nvu_bs_bg,
                "spec_nvu_cascade_bg":     self._spec_nvu_cascade_bg,
                "spec_nvu_bg_contain":     dict(self._spec_nvu_bg_contain),
                "spec_bs_color_mode":      str(self._spec_bs_color_mode),
                "spec_color_mode_per_mode": dict(self._spec_color_mode_per_mode),
                "spec_idle_enabled":       bool(self._spec_idle_enabled),
                "spec_idle_timeout":       float(self._spec_idle_timeout),
                "spec_idle_effect":        str(self._spec_idle_effect),
                "spec_idle_speed":         float(self._spec_idle_speed),
                "spec_idle_cycle_effects": list(self._spec_idle_cycle_effects),
                "spec_eq_gains":           [float(v) for v in self._spec_eq_gains],
                "spec_hallu_submode":              str(self._spec_hallu_submode),
                "spec_hallu_base_kind":            str(self._spec_hallu_base_kind),
                "spec_mode_configs":               json.loads(json.dumps(self._spec_mode_configs)),
                "aspect_lock":                     bool(self._aspect_lock),
            }
            if win_pos:
                c.update(win_pos)
            if not self._sa_session_backup_written:
                _ts  = time.strftime("%Y%m%d_%H%M%S")
                _bak = os.path.join(_DATA_DIR, f"SA-config_backup_{_ts}.json")
                try:
                    with open(_bak, "w", encoding="utf-8") as _bf:
                        json.dump(c, _bf, indent=2)
                    self._sa_session_backup_written = True
                    _existing = sorted(glob.glob(os.path.join(_DATA_DIR, "SA-config_backup_*.json")))
                    while len(_existing) > 5:
                        try: os.remove(_existing.pop(0))
                        except: pass
                except Exception:
                    pass
            with open(SA_CONFIG_FILE, "w", encoding="utf-8") as f:
                json.dump(c, f, indent=2)
            self._config_dirty = False
            self._update_save_buttons()
        except Exception as ex:
            self._status(f"Config save error: {ex}")
        # Notify parent app so it can persist its own cache
        if self._on_save:
            try:   self._on_save()
            except Exception: pass

    def _on_settings_tab_change(self, idx: int):
        """Called when the user switches settings tabs.

        Saves the new tab index and, if switching to SA Settings (tab 0),
        rebuilds that tab so it reflects the currently active mode — which
        may have changed while the user was on a different tab.
        """
        _prev = self._menu_last_tab
        self._menu_last_tab = idx
        if idx == 0 and _prev != 0:
            try:
                self._show_combined_settings(initial_tab=0)
            except Exception:
                pass

    def _update_save_buttons(self):
        """Refresh dirty indicator and save-button style in the open settings panel."""
        try:
            if self._settings_dirty_label is not None:
                self._settings_dirty_label.value = "Unsaved" if self._config_dirty else ""
                self._settings_dirty_label.update()
            if self._settings_save_btn is not None:
                self._settings_save_btn.style = ft.ButtonStyle(
                    bgcolor="#c0392b" if self._config_dirty else "#1a1a2e",
                    color="white",
                )
                self._settings_save_btn.update()
        except Exception:
            pass

    # ── Shared render helpers ─────────────────────────────────────────────────

    def _bar(self, i):
        _bars = self._spec_bars
        _ana = max(1, len(_bars))
        return max(0.0, min(1.0, float(_bars[min(_ana-1, max(0, i))])))

    @staticmethod
    def _sm(c, r, a, rel):
        return r*a + c*(1-a) if r > c else r*rel + c*(1-rel)

    @staticmethod
    def _lerp_h(a, b, t):
        d = (b - a) % 1.0
        if d > 0.5: d -= 1.0
        return (a + d * t) % 1.0

    @staticmethod
    def _ease(t):
        return t * t * (3.0 - 2.0 * t)

    @staticmethod
    def _rgb(h, s=1.0, v=1.0):
        r, g, b = colorsys.hsv_to_rgb(h % 1.0, s, v)
        return "#{:02x}{:02x}{:02x}".format(int(r*255), int(g*255), int(b*255))

    def _wo(self, a, c):
        return ft.Colors.with_opacity(min(1.0, max(0.0, float(a) * self._current_sf)), c)

    def _set_px(self, _x, _y, _color):
        _bands = max(1, self._spec_bands)
        _levels = max(1, self._spec_levels)
        if 0 <= _x < _bands and 0 <= _y < _levels:
            self._spec_segments[_x][_y].bgcolor = _color

    def _draw_mask(self, _mask, _x0, _y0, _color):
        for _ry, _row in enumerate(_mask):
            for _rx, _bit in enumerate(_row):
                if _bit == "1":
                    self._set_px(_x0 + _rx, _y0 + _ry, _color)

    def _tick_random_cm(self, mode_name, new_beat):
        """Return the effective (non-random) color mode for this frame.
        Advances random cycling on beats and elapsed time when 'random' is active."""
        _cm = self._spec_bs_color_mode
        if _cm != "random":
            return _cm
        _pool = _CM_RANDOM_POOL.get(mode_name, ("loop", "gradient"))
        _now  = time.monotonic()
        _cur  = self._cm_rand_current.get(mode_name)
        if _cur is None:
            _cur = random.choice(_pool)
            self._cm_rand_current[mode_name]  = _cur
            self._cm_rand_beats[mode_name]    = 0
            self._cm_rand_target[mode_name]   = random.randint(8, 24)
            self._cm_rand_next_ts[mode_name]  = _now + random.uniform(15.0, 40.0)
            return _cur
        _change = False
        if new_beat:
            _bc = self._cm_rand_beats.get(mode_name, 0) + 1
            self._cm_rand_beats[mode_name] = _bc
            if _bc >= self._cm_rand_target.get(mode_name, 16):
                _change = True
        if _now >= self._cm_rand_next_ts.get(mode_name, 0.0):
            _change = True
        if _change:
            _others = [m for m in _pool if m != _cur]
            _cur = random.choice(_others) if _others else random.choice(_pool)
            self._cm_rand_current[mode_name]  = _cur
            self._cm_rand_beats[mode_name]    = 0
            self._cm_rand_target[mode_name]   = random.randint(8, 24)
            self._cm_rand_next_ts[mode_name]  = _now + random.uniform(15.0, 40.0)
        return _cur

    def _config_path_for(self, mode):
        """Return the slash-separated config key for the given mode using current sub-selections."""
        if mode == "hallucination":
            return f"hallucination/{self._spec_hallu_submode}/{self._spec_hallu_base_kind}"
        return mode

    def _capture_per_mode_settings(self, mode):
        """Snapshot all SA settings page state into _spec_mode_configs for the given mode."""
        if not mode or mode in ("random", "random_song"):
            return
        _path = self._config_path_for(mode)
        _entry = {
            "sensitivity":        float(self._spec_sensitivity),
            "reactivity":         float(self._spec_reactivity),
            "bar_decay":          float(self._spec_bar_decay),
            "peak_decay":         float(self._spec_peak_decay),
            "target_fps":         int(self._spec_target_fps),
            "analysis_bands":     int(self._spec_analysis_bands),
            "eq_gains":           [float(v) for v in self._spec_eq_gains],
        }
        if mode == "hallucination":
            _sub = self._spec_hallu_submode
            _entry["extras"] = {
                "color_mode":  str(self._spec_color_mode_per_mode.get("hallucination", "loop")),
                "auto_rot":      bool(self._spec_hallu_auto_rot),
                "auto_spread":   bool(self._spec_hallu_auto_spread),
                "auto_blur":     bool(self._spec_hallu_auto_blur),

                "params":        dict(self._spec_hallu_params_per_submode.get(_sub, {})),
            }
        elif mode in self._spec_color_mode_per_mode:
            _entry["extras"] = {
                "color_mode": str(self._spec_color_mode_per_mode.get(mode, "gradient")),
                "beat_sens":  float(self._sa_beat_sens),
            }
        self._spec_mode_configs[_path] = _entry

    def _apply_per_mode_settings(self, mode, restart_audio=True):
        """Load _spec_mode_configs for the given mode into active settings, or use defaults."""
        if not mode or mode in ("random", "random_song"):
            return
        _path = self._config_path_for(mode)
        _s = self._spec_mode_configs.get(_path) or {}
        def _c(v, lo, hi, d):
            try:   return max(lo, min(hi, float(v)))
            except: return d
        self._spec_sensitivity  = _c(_s.get("sensitivity",  0.85), 0.1, 1.5, 0.85)
        self._spec_reactivity   = _c(_s.get("reactivity",   1.0),  0.25, 3.0, 1.0)
        self._spec_bar_decay    = _c(_s.get("bar_decay",    2.0),  0.1, 5.0, 2.0)
        self._spec_peak_decay   = _c(_s.get("peak_decay",   1.0),  0.1, 5.0, 1.0)
        self._spec_target_fps   = int(_c(_s.get("target_fps", _SA_MAX_FPS), 8, _SA_MAX_FPS, _SA_MAX_FPS))
        self._set_spec_analysis_bands(_s.get("analysis_bands", self._spec_bands),
                                    restart_audio=restart_audio,
                                    reset_now=not restart_audio)
        _eq = _s.get("eq_gains", [])
        if isinstance(_eq, list) and len(_eq) == len(self._spec_eq_freqs):
            try:   self._spec_eq_gains = [max(0.25, min(3.0, float(v))) for v in _eq]
            except: self._spec_eq_gains = [1.0] * len(self._spec_eq_freqs)
        else:
            self._spec_eq_gains = [1.0] * len(self._spec_eq_freqs)
        # Apply mode-specific extras
        _x = _s.get("extras") if isinstance(_s.get("extras"), dict) else {}
        if not _x:
            if mode in self._spec_color_mode_per_mode:
                self._sa_beat_sens = 1.0
            elif mode == "hallucination":
                _sub = self._spec_hallu_submode
                _default_bs = 2.0 if _sub == "mirror" else 1.0
                self._sa_beat_sens = float(
                    self._spec_hallu_params_per_submode.get(_sub, {}).get("beat_sens", _default_bs))
            return
        if mode == "hallucination":
            _sub = self._spec_hallu_submode
            _cm = str(_x.get("color_mode", "random")).lower()
            self._spec_color_mode_per_mode["hallucination"] = _cm if _cm in ("loop", "gradient", "random") else "random"
            self._spec_hallu_auto_rot       = bool(_x.get("auto_rot",       True))
            self._spec_hallu_auto_spread    = bool(_x.get("auto_spread",    True))
            self._spec_hallu_auto_blur      = bool(_x.get("auto_blur",      True))

            _defaults = {
                "mirror":   {"zoom": 0.85,   "rotDeg": 10.0,   "opacity": 1.0,    "beat_sens": 2.0,  "dim_thresh": 0.25},
                "chroma":   {"maxSplit": 14, "trail": 0.18},
                "perlin":   {"noiseScale": 0.012, "evolveRate": 0.30},
                "morph":    {"layers": 3, "jitter": 1.0, "beat_sens": 1.0},
            }
            _params = _x.get("params", {})
            if isinstance(_params, dict) and _params:
                self._spec_hallu_params_per_submode[_sub] = {
                    **_defaults.get(_sub, {}), **_params
                }
            _merged = self._spec_hallu_params_per_submode.get(_sub, _defaults.get(_sub, {}))
            _default_bs = 2.0 if _sub == "mirror" else 1.0
            self._sa_beat_sens = float(_merged.get("beat_sens", _default_bs))
        elif mode in self._spec_color_mode_per_mode:
            _valid_cm = ("loop", "gradient", "loop_smoke", "gradient_smoke", "random")
            _cm = str(_x.get("color_mode", "gradient")).lower()
            self._spec_color_mode_per_mode[mode] = _cm if _cm in _valid_cm else "gradient"
            self._spec_bs_color_mode = self._spec_color_mode_per_mode.get(
                mode, self._spec_color_mode_per_mode.get("beat_saber", "gradient"))
            self._sa_beat_sens = float(_x.get("beat_sens", 1.0))

    # ── Controls builder ──────────────────────────────────────────────────────

    def _build_controls(self):
        """Build all Flet SA controls.  Does NOT touch the page or window —
        the caller is responsible for adding ``self.widget`` and
        ``self.menu_host`` to whatever layout it owns.
        """
        # ── Spectrum palette ──────────────────────────────────────────────
        _spec_palette = [
            "#00a800", "#00b500", "#00c300", "#00d000", "#00dd00", "#22e000",
            "#4de200", "#7ae400", "#a8e600", "#d6dd00", "#f0c400", "#f59f00",
            "#f97800", "#fb4f00", "#fd2d00", "#ff0000",
        ]
        self._spec_palette   = _spec_palette
        self._spec_segments  = []
        _band_controls       = []
        for _ in range(self._spec_bands):
            _levels = []
            for _lvl in range(self._spec_levels):
                _c = ft.Container(width=7, height=2, border_radius=1, bgcolor="#101010")
                _levels.append(_c)
            self._spec_segments.append(_levels)
            _band_controls.append(
                ft.Column(_levels, spacing=1, tight=True,
                        horizontal_alignment=ft.CrossAxisAlignment.CENTER)
            )

        self._spec_grid_content  = ft.Row(_band_controls, spacing=2,
                                        vertical_alignment=ft.CrossAxisAlignment.END)
        self._spec_graphics_layer = ft.Stack([], expand=True)
        self._spec_graphics_host  = ft.Container(
            expand=True, bgcolor="#05050c",
            content=self._spec_graphics_layer,
            padding=ft.Padding.only(left=8, right=8, top=6, bottom=6),
        )

        # ── Neon VU canvas ────────────────────────────────────────────────
        # Use _PilCanvas instead of cv.Canvas: renders shapes to a single PNG
        # data-URI per frame, avoiding Flet 0.84's per-shape @control diff cost.
        _nvu_bg_src = (self._spec_nvu_drift_bg if self._neon_vu_theme == "neon_drift"
                    else self._spec_nvu_retro_bg)
        _nvu_img = ft.Image(
            src="data:image/png;base64," + _NVU_BLANK_B64,
            fit=ft.BoxFit.FILL,
            gapless_playback=True,   # keep old frame visible until new one is ready (no blank flash)
            filter_quality=ft.FilterQuality.HIGH,
            width=300, height=62,
        )
        self._neon_vu_canvas = _PilCanvas(300, 62, _nvu_img)

        _bg_file_exists = (_nvu_bg_src != "BLANK") and os.path.isfile(
            os.path.join(self._version_dir, _nvu_bg_src))
        self._neon_vu_bg_image = ft.Image(
            src=_nvu_bg_src if _bg_file_exists else "",
            visible=_bg_file_exists,
            fit=ft.BoxFit.CONTAIN if self._spec_nvu_bg_contain.get(self._neon_vu_theme, False) else ft.BoxFit.COVER,
            width=300, height=62, opacity=0.80,
        )
        self._neon_vu_host = ft.Container(
            width=300, height=62,
            bgcolor="#07071a",
            clip_behavior=ft.ClipBehavior.HARD_EDGE,
            content=ft.Stack(
                controls=[self._neon_vu_bg_image, _nvu_img],
                width=300, height=62,
                clip_behavior=ft.ClipBehavior.HARD_EDGE,
            ),
        )

        # ── Hallucination image host ──────────────────────────────────────
        self._hallu_img = ft.Image(
            src="data:image/png;base64," + _HALLU_BLANK_B64, fit=ft.BoxFit.FILL,
            gapless_playback=True,
            width=300, height=62,
        )
        self._hallu_host = ft.Container(
            width=300, height=62,
            bgcolor="#000000",
            clip_behavior=ft.ClipBehavior.HARD_EDGE,
            content=self._hallu_img,
        )

        # ── Spectrum box ──────────────────────────────────────────────────
        self._spectrum_box = ft.Container(
            bgcolor="#060606",
            border=ft.Border.all(1, "#2b2b2b"),
            border_radius=4,
            padding=ft.Padding.only(left=6, right=6, top=0, bottom=0),
            width=self._spec_box_grid_size[0],
            height=self._spec_box_grid_size[1],
            content=self._spec_grid_content,
            tooltip=ft.Tooltip(message="Click to open settings", prefer_below=False, wait_duration=700),
            ink=True,
            on_click=self._open_spectrum_source_selector,
        )

        # ── Buttons ───────────────────────────────────────────────────────
        _btn_style = ft.ButtonStyle(
            bgcolor="transparent",
            shape=ft.RoundedRectangleBorder(radius=5),
            padding=ft.Padding.all(1),
        )
        self._spec_sampling_btn = ft.IconButton(
            icon=ft.Icons.MIC, icon_size=12,
            tooltip="Sampling ON",
            style=_btn_style,
            on_click=self._toggle_spec_sampling,
        )
        self._spec_idle_quick_btn = ft.IconButton(
            icon=ft.Icons.AUTO_AWESOME, icon_size=12,
            tooltip="Idle effects ON",
            style=_btn_style,
            on_click=self._toggle_spec_idle_quick,
        )
        self._spec_combined_settings_btn = ft.IconButton(
            icon=ft.Icons.SETTINGS, icon_size=12,
            icon_color="#ff9800",
            tooltip="SA Settings",
            style=_btn_style,
            on_click=self._open_combined_settings,
        )
        self._spec_detach_btn = ft.IconButton(
            icon=ft.Icons.OPEN_IN_NEW, icon_size=12,
            icon_color="#ff9800",
            tooltip="Detach — open SA in its own window",
            style=_btn_style,
            on_click=self._launch_sa_detached,
        )
        self._spec_prev_mode_btn = ft.IconButton(
            icon=ft.Icons.SKIP_PREVIOUS, icon_size=12,
            icon_color="#aaaaaa",
            tooltip="Previous mode",
            style=_btn_style,
            on_click=lambda _: self._cycle_spec_mode(-1),
        )
        self._spec_next_mode_btn = ft.IconButton(
            icon=ft.Icons.SKIP_NEXT, icon_size=12,
            icon_color="#aaaaaa",
            tooltip="Next mode",
            style=_btn_style,
            on_click=lambda _: self._cycle_spec_mode(1),
        )
        self._sync_spec_quick_buttons()

        # ── Button overlay (inside the display face, visible on hover) ────
        self._spec_btn_overlay = ft.Container(
            content=ft.Row([
                ft.Row([self._spec_sampling_btn, self._spec_idle_quick_btn], spacing=0),
                ft.Row([self._spec_prev_mode_btn, self._spec_next_mode_btn], spacing=0),
                ft.Row([self._spec_combined_settings_btn, self._spec_detach_btn], spacing=0),
            ], alignment=ft.MainAxisAlignment.SPACE_BETWEEN),
            opacity=0,
            bgcolor="transparent",
            left=0, top=0, right=0,
            height=24,
        )

        # ── Display stack: current content only ──────────────────────────
        # btn_overlay lives in the outer unscaled Stack (SpectrumApp) so
        # the buttons stay at native size when the SA display is zoomed.
        self._spec_display_stack = ft.Stack([
            self._spec_grid_content,
        ])

        # Rebuild spectrum box with the stack as permanent content
        self._spectrum_box.content = self._spec_display_stack

        # ── Status text (shown in standalone; hidden/unused in WLEDCC) ────
        self._status_text = ft.Text("", size=10, color="grey600")

        # ── Embeddable SA row and inline menu host ────────────────────────
        self._sa_row = ft.Row([
            self._spectrum_box,
        ], spacing=2, vertical_alignment=ft.CrossAxisAlignment.END)

        self._menu_host = ft.Column([], visible=False, tight=True)

    # ── Logging / status ─────────────────────────────────────────────────────

    def _status(self, msg, color="grey500", debug_only=False):
        if self._log_fn:
            try:
                is_debug = self._debug_mode_fn() if self._debug_mode_fn else self._debug_mode
                if not debug_only or is_debug:
                    self._log_fn(f"[SA] {msg}", color)
            except Exception: pass
        else:
            print(f"[SA] {msg}")
        async def _do_status():
            try:
                # In embedded mode (debug_mode_fn provided), hide when debug is off
                if self._debug_mode_fn is not None and not self._debug_mode_fn():
                    self._status_text.visible = False
                    self._status_text.update()
                    return
                self._status_text.visible = True
                self._status_text.value = msg
                self._status_text.color = color
                self._status_text.update()
            except Exception:
                pass
        try:
            self.page.run_task(_do_status)
        except Exception:
            pass

    def sync_status_visibility(self):
        """Called from parent (WLEDCC) when debug mode changes."""
        try:
            show = self._debug_mode_fn() if self._debug_mode_fn else self._debug_mode
            if not show and not self._status_text.visible:
                return  # already hidden, skip update
            self._status_text.visible = show
            self._status_text.update()
        except Exception:
            pass

    # ── Menu window-resize helpers ────────────────────────────────────────────

    def _expand_for_menu(self, w=_SA_MENU_W, h=_SA_MENU_H):
        """Notify the parent that a settings panel has opened.
        In standalone mode the window is resized; in WLEDCC it's a no-op
        (the inline panel just pushes the layout down)."""
        if self._menu_open:
            try:   self._menu_host.update()
            except Exception: self.page.update()
            return
        self._menu_open = True
        if self._menu_expand_fn:
            try:   self._menu_expand_fn(w, h)
            except Exception: pass
        else:
            try:   self.page.update()
            except Exception: pass

    def _restore_compact(self):
        """Notify the parent that a settings panel has closed."""
        if self._menu_collapse_fn:
            try:   self._menu_collapse_fn()
            except Exception: pass
        else:
            try:   self.page.update()
            except Exception: pass

    def _close_menu_panel(self):
        """Hide the inline settings panel and restore the compact window."""
        self._menu_open = False
        try:
            self._menu_host.controls = []
            self._menu_host.visible  = False
            self._menu_host.update()
        except Exception:
            pass
        self._restore_compact()

    def _on_sa_hover(self, e):
        try:
            self._spec_btn_overlay.opacity = 1.0 if e.data else 0.0
            self._spec_btn_overlay.update()
        except Exception:
            pass

    # ── Colour helpers ────────────────────────────────────────────────────────

    def _dim_hex(self, hex_color, brightness):
        h = hex_color.lstrip("#")
        if len(h) != 6: return hex_color
        r = int(int(h[0:2], 16) * brightness)
        g = int(int(h[2:4], 16) * brightness)
        b = int(int(h[4:6], 16) * brightness)
        return "#{:02x}{:02x}{:02x}".format(r, g, b)

    def _hue_to_hex(self, h):
        r, g, b = colorsys.hsv_to_rgb(h / 360.0, 0.85, 0.75)
        return "#{:02x}{:02x}{:02x}".format(int(r * 255), int(g * 255), int(b * 255))

    # ── Spectrum helpers ──────────────────────────────────────────────────────

    def _collect_random_leaves(self):
        """Walk _MODE_HIERARCHY + _spec_random_tree → flat list of enabled (mode, submode, base_layer) tuples."""
        leaves = []
        tree = self._spec_random_tree
        for mode in _MODE_HIERARCHY:
            mk = mode["key"]
            if "submodes" not in mode:
                if tree.get(mk, True):
                    leaves.append((mk, None, None))
            else:
                mode_val = tree.get(mk, {})
                if not isinstance(mode_val, dict) or not mode_val.get("enabled", True):
                    continue
                for sm in mode["submodes"]:
                    sk = sm["key"]
                    if "base_layers" not in sm:
                        if mode_val.get(sk, True):
                            leaves.append((sk, None, None))
                    else:
                        sm_val = mode_val.get(sk, {})
                        if not isinstance(sm_val, dict) or not sm_val.get("enabled", True):
                            continue
                        for bl in sm["base_layers"]:
                            bk = bl["key"]
                            if sm_val.get(bk, True):
                                leaves.append((mk, sk, bk))
        return leaves

    def _advance_random_mode(self):
        """Unified random advance: picks one enabled leaf from the tree, shuffle-without-repeat."""
        _leaves = self._collect_random_leaves()
        if not _leaves:
            return
        _unplayed = [x for x in _leaves if x not in self._spec_mode_random_played]
        if not _unplayed:
            self._spec_mode_random_played = set()
            _unplayed = list(_leaves)
        _candidates = [x for x in _unplayed if x != self._spec_random_current_leaf]
        if not _candidates:
            _candidates = _unplayed
        _pick = random.choice(_candidates)
        self._spec_mode_random_played.add(_pick)
        self._spec_random_current_leaf = _pick
        _m, _sub, _base = _pick
        if _m in ("neon_drift", "retro_tech", "custom_vu", "hud_reactor",
                "beat_saber", "neon_cascade", "rock_stage"):
            self._neon_vu_theme = _m
        if _m in self._spec_color_mode_per_mode:
            self._spec_bs_color_mode = self._spec_color_mode_per_mode[_m]
        if _m == "hallucination" and _sub is not None:
            self._capture_per_mode_settings("hallucination")
            self._spec_hallu_submode    = _sub
            self._spec_hallu_base_kind  = _base
            self._spec_hallu_aux        = {}
            self._spec_hallu_prev_frame = None
        self._spec_mode = _m
        self._spec_mode_random_current = _m
        self._apply_per_mode_settings(_m)
        if self._menu_open and self._menu_last_tab == 0:
            self._menu_rebuild_requested = True

    def _cycle_spec_mode(self, direction):
        """Step prev (-1) or next (+1) through enabled (mode, submode, base_layer) leaves in _MODE_HIERARCHY order."""
        # Use only enabled leaves (respects the random/idle page checkboxes)
        _all = self._collect_random_leaves()
        if not _all:
            return
        # Identify current leaf
        if self._spec_mode == "hallucination":
            _cur = ("hallucination", self._spec_hallu_submode, self._spec_hallu_base_kind)
        else:
            _cur = (self._spec_mode, None, None)
        if _cur in _all:
            _idx = _all.index(_cur)
            _m, _sub, _base = _all[(_idx + direction) % len(_all)]
        else:
            # Current mode disabled — jump to first (next) or last (prev) enabled mode
            _m, _sub, _base = _all[0 if direction > 0 else -1]
        self._spec_mode_transitioning = True
        try:
            self._capture_per_mode_settings(self._spec_mode)
            if _m in ("neon_drift", "retro_tech", "custom_vu", "hud_reactor",
                    "beat_saber", "neon_cascade", "rock_stage"):
                self._neon_vu_theme = _m
            if _m in self._spec_color_mode_per_mode:
                self._spec_bs_color_mode = self._spec_color_mode_per_mode[_m]
            if _m == "hallucination" and _sub is not None:
                self._spec_hallu_submode    = _sub
                self._spec_hallu_base_kind  = _base
                self._spec_hallu_aux        = {}
                self._spec_hallu_prev_frame = None
            self._spec_mode = _m
            if self._spec_mode_random_enabled or self._spec_mode_random_on_song:
                self._spec_mode_random_current = _m
            self._apply_per_mode_settings(_m)
            self._config_dirty = True
            if self._menu_open and self._menu_last_tab == 0:
                self._menu_rebuild_requested = True
        finally:
            self._spec_mode_transitioning = False

    def _get_spec_render_interval(self):
        _fps = max(8, min(_SA_MAX_FPS, int(round(float(self._spec_target_fps or _SA_MAX_FPS)))))
        return 1.0 / float(_fps)

    def _sync_render(self):
        """Runs on the event loop thread — safe for Flet UI updates."""
        try:
            _t0 = time.monotonic()
            self._render_spectrum()
            _render_ms = (time.monotonic() - _t0) * 1000.0

            _now = time.monotonic()
            if self._spec_fps_track_ts > 0:
                self._spec_fps_frame_count += 1
                _elapsed = _now - self._spec_fps_track_ts
                if _elapsed >= 1.0:
                    self._spec_actual_fps      = self._spec_fps_frame_count / _elapsed
                    self._spec_fps_frame_count = 0
                    self._spec_fps_track_ts    = _now
                    _lbl = self._spec_fps_label
                    if _lbl is not None:
                        try:
                            _lbl.value = (f"{int(self._spec_target_fps)} FPS"
                                          f"  actual: {self._spec_actual_fps:.0f}"
                                          f"  render: {_render_ms:.0f}ms")
                            _lbl.update()
                        except Exception:
                            pass
            else:
                self._spec_fps_track_ts    = _now
                self._spec_fps_frame_count = 0
        except Exception:
            pass
        finally:
            self._render_pending = False

    def _sync_clear_display(self):
        """Runs on the event loop thread — safe for Flet UI updates."""
        try:
            self._clear_spectrum_display()
        except Exception:
            pass

    def _schedule_render(self):
        """Post one render frame to the event loop from any background thread.

        Uses loop.call_soon_threadsafe() — writes to the selector self-pipe so
        the event loop wakes immediately, same as run_task but without creating
        a coroutine object. Avoids the 'coroutine never awaited' RuntimeWarning
        that page.run_task() can produce when the session tears down mid-frame.
        """
        if self._render_pending or not self.running:
            return
        _loop = self._event_loop
        if _loop is None or not _loop.is_running():
            return
        self._render_pending = True
        try:
            _loop.call_soon_threadsafe(self._sync_render)
        except Exception:
            self._render_pending = False

    def _reset_spec_analysis_state(self):
        _count = max(6, min(int(self._spec_bands),
                            int(self._spec_analysis_bands or self._spec_bands)))
        self._spec_bars      = [0.0] * _count
        self._spec_peaks     = [0.0] * _count
        self._spec_peak_hold = [0]   * _count
        self._spec_band_avg  = [0.0] * _count

    def _set_spec_analysis_bands(self, bands, restart_audio=True, reset_now=False):
        try:   _new = max(6, min(int(self._spec_bands), int(round(float(bands)))))
        except: _new = int(self._spec_bands)
        _old = int(self._spec_analysis_bands or self._spec_bands)
        self._spec_analysis_bands = _new
        if reset_now:
            self._reset_spec_analysis_state()
        if restart_audio and _new != _old:
            self._spec_source_changed = True
            if self._spec_disabled:
                self._spec_disabled = False
                threading.Thread(target=self._audio_analyzer_loop,
                                daemon=True, name="SA_AudioLoop").start()
        return _new != _old

    def _clear_spectrum_display(self):
        try:
            self._set_spectrum_render_mode("grid")
            for _segs in self._spec_segments:
                for _seg in _segs:
                    _seg.bgcolor = "#101010"
            self._spectrum_box.update()
        except Exception:
            pass

    def _set_spectrum_render_mode(self, mode, silent=False):
        _target = mode if mode in ("graphics", "neon_vu", "hallucination") else "grid"
        if self._spec_render_mode == _target:
            return
        if _target == "neon_vu":
            self._spectrum_box.padding = ft.Padding.all(0)
            self._spectrum_box.width   = 300
            self._spectrum_box.height  = 62
            self._spec_display_stack.controls[0] = self._neon_vu_host
        elif _target == "graphics":
            self._spectrum_box.padding = ft.Padding.all(0)
            self._spectrum_box.width   = self._spec_box_graphics_size[0]
            self._spectrum_box.height  = self._spec_box_graphics_size[1]
            self._spec_display_stack.controls[0] = self._spec_graphics_host
            self._spec_graphics_ready  = False
            self._spec_graphics_view_size = (0, 0)
        elif _target == "hallucination":
            self._spectrum_box.padding = ft.Padding.all(0)
            self._spectrum_box.width   = 300
            self._spectrum_box.height  = 62
            self._spec_display_stack.controls[0] = self._hallu_host
        else:
            self._spectrum_box.padding = ft.Padding.symmetric(horizontal=6, vertical=4)
            self._spectrum_box.width   = self._spec_box_grid_size[0]
            self._spectrum_box.height  = self._spec_box_grid_size[1]
            self._spec_display_stack.controls[0] = self._spec_grid_content
        self._spec_render_mode = _target
        if not silent:
            try: self._spectrum_box.update()
            except: pass

    def _sync_spec_quick_buttons(self):
        try:
            _on  = "#ff9800"
            _off = "grey500"
            self._spec_combined_settings_btn.icon_color = _on
            if self._spec_sampling_enabled:
                self._spec_sampling_btn.icon_color = _on
                self._spec_sampling_btn.tooltip    = "Sampling ON"
            else:
                self._spec_sampling_btn.icon_color = _off
                self._spec_sampling_btn.tooltip    = "Sampling OFF"
            if self._spec_idle_enabled:
                self._spec_idle_quick_btn.icon_color = _on
                self._spec_idle_quick_btn.tooltip    = "Idle effects ON"
            else:
                self._spec_idle_quick_btn.icon_color = _off
                self._spec_idle_quick_btn.tooltip    = "Idle effects OFF"
            self._spec_sampling_btn.update()
            self._spec_idle_quick_btn.update()
            self._spec_combined_settings_btn.update()
        except Exception:
            pass

    def _toggle_spec_sampling(self, _=None):
        self._spec_sampling_enabled = not self._spec_sampling_enabled
        self._spec_source_changed   = True
        if self._spec_disabled:
            self._spec_disabled = False
            threading.Thread(target=self._audio_analyzer_loop,
                            daemon=True, name="SA_AudioLoop").start()
        self._sync_spec_quick_buttons()
        self._config_dirty = True
        self._update_save_buttons()

    def _toggle_spec_idle_quick(self, _=None):
        self._spec_idle_enabled = not self._spec_idle_enabled
        self._spec_idle_active  = False
        self._sync_spec_quick_buttons()
        self._config_dirty = True
        self._update_save_buttons()

    # ── Audio profile helpers ─────────────────────────────────────────────────

    def _spec_profile_key(self, source_name=None):
        _name = self._spec_selected_source if source_name is None else source_name
        return "__default__" if not _name else str(_name)

    def _save_spec_profile(self, source_name=None):
        _key = self._spec_profile_key(source_name)
        self._spec_profiles[_key] = {
            "sensitivity": float(self._spec_sensitivity),
            "reactivity":  float(self._spec_reactivity),
            "bar_decay":   float(self._spec_bar_decay),
            "peak_decay":  float(self._spec_peak_decay),
            "eq_gains":    [float(v) for v in self._spec_eq_gains],
        }

    def _load_spec_profile(self, source_name=None):
        _key = self._spec_profile_key(source_name)
        _p   = self._spec_profiles.get(_key, {}) if isinstance(self._spec_profiles, dict) else {}
        def _c(v, lo, hi, d):
            try:   return max(lo, min(hi, float(v)))
            except: return d
        self._spec_sensitivity = _c(_p.get("sensitivity", 0.85), 0.1, 1.5, 0.85)
        self._spec_reactivity  = _c(_p.get("reactivity",  1.0),  0.25, 3.0, 1.0)
        self._spec_bar_decay   = _c(_p.get("bar_decay",   2.0),  0.1, 5.0, 2.0)
        self._spec_peak_decay  = _c(_p.get("peak_decay",  1.0),  0.1, 5.0, 1.0)
        _eq = _p.get("eq_gains", None)
        if isinstance(_eq, list) and len(_eq) == len(self._spec_eq_freqs):
            try:   self._spec_eq_gains = [max(0.25, min(3.0, float(v))) for v in _eq]
            except: self._spec_eq_gains = [1.0] * len(self._spec_eq_freqs)
        else:
            self._spec_eq_gains = [1.0] * len(self._spec_eq_freqs)

    def _pick_default_spectrum_source(self, _sc):
        try:   _speaker = _sc.default_speaker()
        except: _speaker = None
        try:   _all_mics = list(_sc.all_microphones(include_loopback=True))
        except: _all_mics = []
        if _speaker is not None:
            try:
                _loop = _sc.get_microphone(id=_speaker.id, include_loopback=True)
                if _loop: return _loop, "output-loopback"
            except: pass
        _speaker_name = (_speaker.name.lower() if _speaker and getattr(_speaker, "name", None) else "")
        for _m in _all_mics:
            _n = str(getattr(_m, "name", "")).lower()
            if "loopback" in _n or "stereo mix" in _n:
                if _speaker_name and _speaker_name in _n:
                    return _m, "output-loopback"
        for _m in _all_mics:
            _n = str(getattr(_m, "name", "")).lower()
            if "loopback" in _n or "stereo mix" in _n:
                return _m, "output-loopback"
        try:
            _mic = _sc.default_microphone()
            if _mic: return _mic, "input-microphone"
        except: pass
        return None, None

    def _refresh_spectrum_sources(self):
        try:
            import importlib
            _sc = importlib.import_module("soundcard")
            _all_mics = list(_sc.all_microphones(include_loopback=True))
            _raw = [(m.name, idx) for idx, m in enumerate(_all_mics)]
            _rank = {n: i for i, n in enumerate(self._spec_source_order)}
            self._spec_audio_sources = sorted(_raw, key=lambda it: (_rank.get(it[0], 10**9), it[1]))
            _new_order = []
            for _name, _ in self._spec_audio_sources:
                if _name not in _new_order:
                    _new_order.append(_name)
            self._spec_source_order = _new_order
            return True
        except Exception:
            self._spec_audio_sources = []
            return False

    # ── Detach / launch standalone SA ────────────────────────────────────────

    def _start_pos_tracker(self):
        """Background thread: find our HWND once, then poll GetWindowRect every 200 ms.

        Stores physical-pixel rect + DPI in self._own_rect / self._own_dpi so that
        _launch_sa_detached always has a current window position without depending on
        Flet's stale page.window.left/top (which only reflects the last programmatic set).
        """
        import threading

        def _track():
            import time as _time
            _pid   = os.getpid()
            _title = self.page.title or ""

            # ── Phase 1: locate our HWND ──────────────────────────────────
            for _ in range(40):   # retry up to 4 s while window is opening
                if self._pos_tracker_stop:
                    return
                _hits = []
                _EWP  = ctypes.WINFUNCTYPE(ctypes.c_bool, ctypes.c_size_t, ctypes.c_size_t)

                def _cb(hwnd, _):
                    if not ctypes.windll.user32.IsWindowVisible(hwnd):
                        return True
                    _pw = ctypes.c_ulong()
                    ctypes.windll.user32.GetWindowThreadProcessId(hwnd, ctypes.byref(_pw))
                    if _pw.value != _pid:
                        return True
                    _buf = ctypes.create_unicode_buffer(512)
                    ctypes.windll.user32.GetWindowTextW(hwnd, _buf, 512)
                    if _title and _buf.value != _title:
                        return True
                    _rc = ctypes.wintypes.RECT()
                    if ctypes.windll.user32.GetWindowRect(hwnd, ctypes.byref(_rc)):
                        if _rc.right - _rc.left > 100:
                            _hits.append(hwnd)
                    return True

                ctypes.windll.user32.EnumWindows(_EWP(_cb), 0)
                if _hits:
                    self._own_hwnd = _hits[0]
                    break
                _time.sleep(0.1)

            # ── Phase 2: keep rect current ────────────────────────────────
            while not self._pos_tracker_stop:
                if self._own_hwnd:
                    try:
                        _rc = ctypes.wintypes.RECT()
                        if ctypes.windll.user32.GetWindowRect(self._own_hwnd, ctypes.byref(_rc)):
                            if _rc.right - _rc.left > 50:
                                self._own_rect = _rc
                                try:
                                    self._own_dpi = ctypes.windll.user32.GetDpiForWindow(self._own_hwnd) or 96
                                except Exception:
                                    pass
                    except Exception:
                        pass
                _time.sleep(0.2)

        threading.Thread(target=_track, daemon=True).start()

    def _launch_sa_detached(self, _=None):
        """Launch SA.exe (or SA.py fallback) as a detached independent process."""
        _here = os.path.dirname(
            sys.executable if getattr(sys, "frozen", False)
            else os.path.abspath(__file__)
        )
        _exe = os.path.join(_here, "SA.exe")
        _py  = os.path.join(_here, "SA.py")
        try:
            _is_standalone = os.path.basename(sys.argv[0]).lower().startswith('sa')
            if _is_standalone:
                # Use the rect cached by _start_pos_tracker (updated every 200 ms)
                # so we always have the live OS position even after the user drags
                # the window (Flet's page.window.left/top are stale in that case).
                _wx = _wy = None
                _ww = int(self.page.window.width  or _SA_COMPACT_W)
                # Use Flet's page.window.height — it's updated immediately on
                # programmatic set (menu open/close) and on user resize.
                # Do NOT use _own_rect height: the tracker polls every 200 ms and
                # can carry a stale menu-expanded height that breaks the fit check.
                _wh = int(self.page.window.height or _SA_COMPACT_H)
                _rc = self._own_rect
                if _rc is not None:
                    try:
                        _sc = (self._own_dpi or 96) / 96
                        _wa = ctypes.wintypes.RECT()
                        ctypes.windll.user32.SystemParametersInfoW(48, 0, ctypes.byref(_wa), 0)
                        _wat = round(_wa.top    / _sc)
                        _wab = round(_wa.bottom / _sc)
                        _wal = round(_wa.left   / _sc)
                        _war = round(_wa.right  / _sc)
                        # Prefer below; fall back to above; last resort: top of work area
                        _wy_below = round(_rc.bottom / _sc)
                        _wy_above = round(_rc.top    / _sc) - _wh
                        if _wy_below + _wh <= _wab:
                            _wy = _wy_below
                        elif _wy_above >= _wat:
                            _wy = _wy_above
                        else:
                            _wy = _wat
                        _wx = max(_wal, min(round(_rc.left / _sc), _war - _ww))
                    except Exception:
                        _wx = _wy = None
                if _wx is None:
                    _wx = int(self.page.window.left   or 0)
                    _wy = int(self.page.window.top    or 0) + _wh
                _spawn_args = ["--spawn-x", str(_wx), "--spawn-y", str(_wy),
                            "--spawn-w", str(_ww), "--spawn-h", str(_wh)]
                if self._debug_mode:
                    _debug = self._debug_mode_fn() if self._debug_mode_fn else self._debug_mode
                    if _debug:
                        _spawn_args.append("--debug-mode")
            else:
                try:
                    _hwnd = ctypes.windll.user32.FindWindowW(None, self.page.title)
                    _pt   = ctypes.wintypes.POINT(0, 0)
                    ctypes.windll.user32.ClientToScreen(_hwnd, ctypes.byref(_pt))
                    _wx, _wy = _pt.x, _pt.y + _SA_COMPACT_H + 4
                except Exception:
                    _wx, _wy = 0, 0
                _spawn_args = ["--spawn-x", str(_wx), "--spawn-y", str(_wy),
                            "--spawn-w", str(_SA_COMPACT_W), "--spawn-h", str(_SA_COMPACT_H)]
                _debug = self._debug_mode_fn() if self._debug_mode_fn else self._debug_mode
                if _debug:
                    _spawn_args.append("--debug-mode")
            # Pass the next mode after the currently playing one so the new
            # instance starts there instead of on the last-saved mode.
            _mode_args = []
            try:
                _all = self._collect_random_leaves()
                if _all:
                    if self._spec_mode == "hallucination":
                        _cur = ("hallucination", self._spec_hallu_submode, self._spec_hallu_base_kind)
                    else:
                        _cur = (self._spec_mode, None, None)
                    _idx = _all.index(_cur) if _cur in _all else -1
                    _nm, _nsub, _nbase = _all[(_idx + 1) % len(_all)]
                    _mode_args = ["--start-mode", _nm]
                    if _nm == "hallucination" and _nsub:
                        _mode_args += ["--hallu-sub", _nsub, "--hallu-base", str(_nbase or "waveform")]
            except Exception:
                pass
            if os.path.isfile(_exe):
                subprocess.Popen([_exe] + _spawn_args + _mode_args, cwd=_here)
                self._status("Launched SA.exe", "cyan")
            elif os.path.isfile(_py):
                subprocess.Popen([sys.executable, _py] + _spawn_args + _mode_args, cwd=_here)
                self._status("Launched SA.py", "cyan")
            else:
                self._status("SA.exe / SA.py not found", "orange400")
        except Exception as ex:
            self._status(f"Launch failed: {ex}", "red400")

    # ── Settings dialogs ──────────────────────────────────────────────────────

    def _open_spectrum_source_selector(self, _=None):
        try:   self._show_combined_settings(initial_tab=0)
        except Exception as ex: self._status(f"Settings error: {ex}", "orange400")

    def _open_spectrum_idle_settings(self, _=None):
        try:   self._show_combined_settings(initial_tab=1)
        except Exception as ex: self._status(f"Idle settings error: {ex}", "orange400")

    def _open_combined_settings(self, _=None):
        try:   self._show_combined_settings(initial_tab=0)
        except Exception as ex: self._status(f"Settings error: {ex}", "orange400")

    def _show_combined_settings(self, initial_tab=0):
        self._status("Spectrum settings opened")
        self._refresh_spectrum_sources()

        _sens_slider = _react_slider = None
        _bar_decay_slider = _peak_decay_slider = None

        def _clear_panel_refs():
            self._settings_save_btn    = None
            self._settings_dirty_label = None

        def _do_close(_=None):
            _clear_panel_refs()
            self._close_menu_panel()

        def _do_reload(_=None):
            _tab = _tabs.selected_index
            _keep_mode = self._spec_mode  # guard against concurrent render-loop mode changes
            _clear_panel_refs()
            self.load_config(preserve_mode=True)
            self._spec_mode = _keep_mode  # ensure mode is never reverted by undo
            self._show_combined_settings(initial_tab=_tab)

        def _do_save(_=None):
            self._save_spec_profile()
            self.save_config()
            self._status("Settings saved", "green400")

        def _do_save_and_exit(_=None):
            self._save_spec_profile()
            self.save_config()
            _clear_panel_refs()
            self._status("Settings saved", "green400")
            self._close_menu_panel()

        source_list = None

        def on_source_selected(source_name):
            nonlocal _active_eq_preset
            self._save_spec_profile()
            self._spec_selected_source = source_name if source_name != "Default" else None
            if self._spec_selected_source:
                self._spec_source_order = (
                    [self._spec_selected_source] +
                    [n for n in self._spec_source_order if n != self._spec_selected_source]
                )
            self._load_spec_profile(self._spec_selected_source)
            self._spec_source_changed = True
            if self._spec_disabled:
                self._spec_disabled = False
                threading.Thread(target=self._audio_analyzer_loop,
                                daemon=True, name="SA_AudioLoop").start()
            self._refresh_spectrum_sources()
            if source_list is not None:
                source_list.controls = _build_source_buttons()
                source_list.update()
            if _sens_slider is not None:
                _sens_slider.value = max(_sens_slider.min, min(_sens_slider.max, float(self._spec_sensitivity)))
                _sens_slider.update()
                _sens_pct.value    = f"{int(self._spec_sensitivity * 100)}%"
                _sens_pct.update()
            if _react_slider is not None:
                _react_slider.value = max(_react_slider.min, min(_react_slider.max, float(self._spec_reactivity)))
                _react_slider.update()
                _react_pct.value   = f"{self._spec_reactivity:.2f}x"
                _react_pct.update()
            if _bar_decay_slider is not None:
                _bar_decay_slider.value = max(_bar_decay_slider.min, min(_bar_decay_slider.max, float(self._spec_bar_decay)))
                _bar_decay_slider.update()
                _bar_decay_pct.value = f"{self._spec_bar_decay:.2f}x"
                _bar_decay_pct.update()
            if _peak_decay_slider is not None:
                _peak_decay_slider.value = max(_peak_decay_slider.min, min(_peak_decay_slider.max, float(self._spec_peak_decay)))
                _peak_decay_slider.update()
                _peak_decay_pct.value = f"{self._spec_peak_decay:.2f}x"
                _peak_decay_pct.update()
            for i, s in enumerate(_eq_sliders):
                s.value = max(s.min, min(s.max, float(self._spec_eq_gains[i])))
                s.update()
                _eq_value_texts[i].value = f"{self._spec_eq_gains[i]:.2f}x"
                _eq_value_texts[i].update()
            _active_eq_preset = _detect_eq_preset_name()
            _refresh_eq_preset_buttons()
            self._status(f"Source: {source_name}")
            self._config_dirty = True; self._update_save_buttons()

        def _build_source_buttons():
            if self._spec_audio_sources:
                _btns = []
                current = self._spec_selected_source
                if current:
                    _btns.append(ft.TextButton(current,
                        on_click=lambda _, n=current: on_source_selected(n),
                        style=ft.ButtonStyle(color="#ff9800")))
                    _btns.append(ft.TextButton("Default",
                        on_click=lambda _: on_source_selected("Default"),
                        style=ft.ButtonStyle(color="grey500")))
                    for name, _ in self._spec_audio_sources:
                        if name == current: continue
                        _btns.append(ft.TextButton(name,
                            on_click=lambda _, n=name: on_source_selected(n),
                            style=ft.ButtonStyle(color="grey500")))
                else:
                    _btns.append(ft.TextButton("Default",
                        on_click=lambda _: on_source_selected("Default"),
                        style=ft.ButtonStyle(color="#ff9800")))
                    for name, _ in self._spec_audio_sources:
                        _btns.append(ft.TextButton(name,
                            on_click=lambda _, n=name: on_source_selected(n),
                            style=ft.ButtonStyle(color="grey500")))
                return _btns
            return [
                ft.Text("No compatible sources detected.", size=12, color="orange400"),
                ft.Text("Tip: Enable Stereo Mix or play audio first.", size=11, color="grey500"),
            ]

        _sens_pct        = ft.Text(f"{int(self._spec_sensitivity * 100)}%",     size=12, color="#ff9800")
        _fps_txt         = ft.Text(f"{int(self._spec_target_fps)} FPS",          size=12, color="#ff9800")
        self._spec_fps_label = _fps_txt
        _bars_txt        = ft.Text(f"{int(self._spec_analysis_bands)}",           size=12, color="#ff9800")
        _react_pct       = ft.Text(f"{self._spec_reactivity:.2f}x",              size=12, color="#ff9800")
        _bar_decay_pct   = ft.Text(f"{self._spec_bar_decay:.2f}x",               size=12, color="#ff9800")
        _peak_decay_pct  = ft.Text(f"{self._spec_peak_decay:.2f}x",              size=12, color="#ff9800")
        _idle_timeout_txt= ft.Text(f"{int(self._spec_idle_timeout)}s",           size=12, color="#ff9800")
        _idle_speed_txt  = ft.Text(f"{self._spec_idle_speed:.2f}x",              size=12, color="#ff9800")

        def on_target_fps_change(e):
            self._spec_target_fps = max(8, min(_SA_MAX_FPS, int(round(float(e.control.value)))))
            _fps_txt.value = f"{int(self._spec_target_fps)} FPS (actual: {self._spec_actual_fps:.0f})"
            _fps_txt.update()
            self._config_dirty = True; self._update_save_buttons()

        def on_analysis_bars_change(e):
            _new = max(6, min(int(self._spec_bands), int(round(float(e.control.value)))))
            _bars_txt.value = f"{_new}"; _bars_txt.update()
            self._set_spec_analysis_bands(_new, restart_audio=True, reset_now=False)
            self._config_dirty = True; self._update_save_buttons()

        def on_sensitivity_change(e):
            self._spec_sensitivity = round(float(e.control.value), 2)
            _sens_pct.value = f"{int(self._spec_sensitivity * 100)}%"; _sens_pct.update()
            self._save_spec_profile()
            self._config_dirty = True; self._update_save_buttons()

        def on_reactivity_change(e):
            self._spec_reactivity = round(float(e.control.value), 2)
            _react_pct.value = f"{self._spec_reactivity:.2f}x"; _react_pct.update()
            self._save_spec_profile()
            self._config_dirty = True; self._update_save_buttons()

        def on_bar_decay_change(e):
            self._spec_bar_decay = round(float(e.control.value), 2)
            _bar_decay_pct.value = f"{self._spec_bar_decay:.2f}x"; _bar_decay_pct.update()
            self._save_spec_profile()
            self._config_dirty = True; self._update_save_buttons()

        def on_peak_decay_change(e):
            self._spec_peak_decay = round(float(e.control.value), 2)
            _peak_decay_pct.value = f"{self._spec_peak_decay:.2f}x"; _peak_decay_pct.update()
            self._save_spec_profile()
            self._config_dirty = True; self._update_save_buttons()

        def _do_mode_switch(new_mode):
            _old_mode = self._spec_mode
            _mode = str(new_mode).lower()
            self._spec_mode_transitioning = True
            try:
                self._capture_per_mode_settings(_old_mode)
                self._spec_mode = _mode if _mode in (
                    "classic", "vu", "cyber_city", "beat_saber", "neon_drift", "retro_tech",
                    "custom_vu", "hud_reactor", "neon_cascade", "rock_stage", "hallucination") else "classic"
                if self._spec_mode_random_enabled or self._spec_mode_random_on_song:
                    self._spec_mode_random_current = self._spec_mode
                if   _mode == "neon_drift":   self._neon_vu_theme = "neon_drift"
                elif _mode == "retro_tech":   self._neon_vu_theme = "retro_tech"
                elif _mode == "custom_vu":    self._neon_vu_theme = "custom_vu"
                elif _mode == "hud_reactor":  self._neon_vu_theme = "hud_reactor"
                elif _mode == "beat_saber":   self._neon_vu_theme = "beat_saber"
                elif _mode == "neon_cascade": self._neon_vu_theme = "neon_cascade"
                elif _mode == "rock_stage":   self._neon_vu_theme = "rock_stage"
                if _mode in self._spec_color_mode_per_mode:
                    _stored = self._spec_color_mode_per_mode[_mode]
                    if _stored != "random" and _mode != "rock_stage" and _stored in ("loop_smoke", "gradient_smoke"):
                        _stored = "gradient" if "gradient" in _stored else "loop"
                        self._spec_color_mode_per_mode[_mode] = _stored
                    self._spec_bs_color_mode = _stored
                self._apply_per_mode_settings(_mode)
                if _mode == "hallucination":
                    self._spec_hallu_prev_frame = None
                    self._spec_hallu_aux = {}
                self._config_dirty = True
                _tab = _tabs.selected_index
                _clear_panel_refs()
                self._show_combined_settings(initial_tab=_tab)
            finally:
                self._spec_mode_transitioning = False

        def on_group_change(e):
            _new_group = str(e.control.value or "classic_group")
            _group_def = next((m for m in _MODE_HIERARCHY if m["key"] == _new_group), None)
            if not _group_def:
                return
            if "submodes" not in _group_def:
                _do_mode_switch(_new_group)
            elif _new_group == "hallucination":
                _do_mode_switch("hallucination")
            else:
                _sm_keys = [sm["key"] for sm in _group_def["submodes"]]
                _new_mode = self._spec_mode if self._spec_mode in _sm_keys else _sm_keys[0]
                _do_mode_switch(_new_mode)

        def on_sub_change(e):
            _do_mode_switch(str(e.control.value or "classic"))

        def on_sample_rate_change(e):
            try:   _new_sr = int(str(e.control.value or "48000"))
            except: _new_sr = 48000
            if _new_sr not in (16000, 22050, 32000, 44100, 48000): _new_sr = 48000
            if _new_sr != int(self._spec_sample_rate or 48000):
                self._spec_sample_rate    = _new_sr
                self._spec_source_changed = True
                if self._spec_disabled:
                    self._spec_disabled = False
                    threading.Thread(target=self._audio_analyzer_loop,
                                    daemon=True, name="SA_AudioLoop").start()
                self._status(f"Sample rate → {self._spec_sample_rate} Hz")
                self._config_dirty = True; self._update_save_buttons()

        def on_idle_enabled_change(e):
            self._spec_idle_enabled = bool(e.control.value)
            self._sync_spec_quick_buttons()

        def on_idle_timeout_change(e):
            self._spec_idle_timeout = round(float(e.control.value), 1)
            _idle_timeout_txt.value = f"{int(round(self._spec_idle_timeout))}s"
            _idle_timeout_txt.update()
            self._config_dirty = True; self._update_save_buttons()

        def on_idle_effect_change(e):
            _fx = str(e.control.value or "random").lower()
            self._spec_idle_effect = _fx if _fx in (
                "random", "pulse", "text", "pacman", "tetris",
                "invaders", "snake", "starwars") else "random"
            self._config_dirty = True; self._update_save_buttons()

        def on_idle_speed_change(e):
            self._spec_idle_speed = round(float(e.control.value), 2)
            _idle_speed_txt.value = f"{self._spec_idle_speed:.2f}x"; _idle_speed_txt.update()
            self._config_dirty = True; self._update_save_buttons()

        def on_color_mode_change(e):
            _cm = str(e.control.value or "gradient").lower()
            _cm = _cm if _cm in ("loop", "gradient", "loop_smoke", "gradient_smoke", "random") else "gradient"
            if _cm == "random":
                self._cm_rand_current.pop(self._spec_mode, None)  # reset cycle on re-select
            self._spec_bs_color_mode = _cm
            if self._spec_mode in self._spec_color_mode_per_mode:
                self._spec_color_mode_per_mode[self._spec_mode] = _cm
            self._config_dirty = True
            self._update_save_buttons()

        def on_bg_change(e):
            self._spec_nvu_bg_force_reload = True
            if   self._spec_mode == "neon_drift":  self._spec_nvu_drift_bg   = e.control.value
            elif self._spec_mode == "retro_tech":  self._spec_nvu_retro_bg   = e.control.value
            elif self._spec_mode == "custom_vu":   self._spec_nvu_custom_bg  = e.control.value
            elif self._spec_mode == "hud_reactor": self._spec_nvu_hud_bg     = e.control.value
            elif self._spec_mode == "rock_stage":  self._spec_nvu_rock_bg    = e.control.value
            elif self._spec_mode == "beat_saber":  self._spec_nvu_bs_bg      = e.control.value
            elif self._spec_mode == "neon_cascade":self._spec_nvu_cascade_bg = e.control.value
            self._render_spectrum()
            self._config_dirty = True
            self._update_save_buttons()

        def _mode_to_group_key(mk):
            for _m in _MODE_HIERARCHY:
                if _m["key"] == mk:
                    return mk
                for _sm in _m.get("submodes", []):
                    if _sm.get("key") == mk:
                        return _m["key"]
            return "classic_group"

        _eff_mode      = self._spec_mode if self._spec_mode not in ("random", "random_song") else "classic"
        _cur_group_key = _mode_to_group_key(_eff_mode)
        _cur_group_def = next((m for m in _MODE_HIERARCHY if m["key"] == _cur_group_key), None)
        _is_container  = (_cur_group_def and "submodes" in _cur_group_def
                        and all("base_layers" not in sm for sm in _cur_group_def["submodes"]))

        _mode_dd = ft.Dropdown(
            width=200,
            value=_cur_group_key,
            options=[ft.dropdown.Option(m["key"], m["label"]) for m in _MODE_HIERARCHY],
            on_select=on_group_change, text_size=12, dense=True,

        )
        _sub_options = ([ft.dropdown.Option(sm["key"], sm["label"]) for sm in _cur_group_def["submodes"]]
                        if _is_container else [])
        _sub_mode_dd = ft.Dropdown(
            width=200,
            value=_eff_mode if _is_container else None,
            options=_sub_options,
            on_select=on_sub_change, text_size=12, dense=True,
        )
        _sub_row = ft.Row(
            [ft.Text("Type:", size=12, color="grey400"), _sub_mode_dd],
            spacing=8, vertical_alignment=ft.CrossAxisAlignment.CENTER,
            visible=bool(_is_container),
        )

        _jpg_names = sorted([os.path.basename(f) for f in glob.glob(os.path.join(self._version_dir, "*.jpg"))
                            if os.path.isfile(f)])
        _jpg_names.insert(0, "BLANK")

        _bg_dd = ft.Dropdown(
            width=200,
            options=[ft.dropdown.Option(n) for n in _jpg_names],
            value=(self._spec_nvu_drift_bg   if self._spec_mode == "neon_drift"   else
                self._spec_nvu_retro_bg   if self._spec_mode == "retro_tech"  else
                self._spec_nvu_hud_bg     if self._spec_mode == "hud_reactor" else
                self._spec_nvu_rock_bg    if self._spec_mode == "rock_stage"  else
                self._spec_nvu_bs_bg      if self._spec_mode == "beat_saber"  else
                self._spec_nvu_cascade_bg if self._spec_mode == "neon_cascade" else
                self._spec_nvu_custom_bg),
            on_select=on_bg_change, text_size=12, dense=True,

        )
        def on_bg_contain_change(e):
            self._spec_nvu_bg_contain[self._spec_mode] = bool(e.control.value)
            self._config_dirty = True
            self._update_save_buttons()

        _bg_contain_cb = ft.Checkbox(
            label="Show Full Image (no crop)", scale=0.85,
            value=self._spec_nvu_bg_contain.get(self._spec_mode, False),
            on_change=on_bg_contain_change,
            active_color="#ff9800",
        )
        _bg_col = ft.Column([
            ft.Row([
                ft.Text("VU BG Image:", size=12, color="grey400"),
                _bg_dd,
            ], spacing=8, vertical_alignment=ft.CrossAxisAlignment.CENTER),
            _bg_contain_cb,
        ], spacing=2,
        visible=(self._spec_mode in ("neon_drift", "retro_tech", "custom_vu", "hud_reactor", "rock_stage", "beat_saber", "neon_cascade")))

        def _color_mode_options(mode):
            _base = [ft.dropdown.Option("loop", "Color Loop"), ft.dropdown.Option("gradient", "Gradient")]
            if mode == "rock_stage":
                _base += [ft.dropdown.Option("loop_smoke", "Color Loop + Smoke"),
                        ft.dropdown.Option("gradient_smoke", "Gradient + Smoke")]
            _base.append(ft.dropdown.Option("random", "Random"))
            return _base

        _cm_init = self._spec_bs_color_mode
        if self._spec_mode != "rock_stage" and _cm_init in ("loop_smoke", "gradient_smoke"):
            _cm_init = "gradient" if "gradient" in _cm_init else "loop"
            self._spec_bs_color_mode = _cm_init
        _color_mode_dd = ft.Dropdown(
            width=180,
            options=_color_mode_options(self._spec_mode),
            value=_cm_init,
            on_select=on_color_mode_change, text_size=12, dense=True,

        )
        _color_mode_col = ft.Row([
            ft.Text("Color Mode:", size=12, color="grey400"),
            _color_mode_dd,
        ], spacing=8, vertical_alignment=ft.CrossAxisAlignment.CENTER,
        visible=(self._spec_mode in ("beat_saber", "neon_cascade", "rock_stage")))

        _canvas_bs_init = float(self._spec_mode_configs.get(self._spec_mode, {}).get(
            "extras", {}).get("beat_sens", 1.0))
        _canvas_bs_lbl = ft.Text(f"{_canvas_bs_init:.1f}", size=11, color="#ff9800", width=42)
        def on_canvas_beat_sens(e):
            v = round(float(e.control.value), 1)
            self._sa_beat_sens = v
            _canvas_bs_lbl.value = f"{v:.1f}"; _canvas_bs_lbl.update()
            self._config_dirty = True; self._update_save_buttons()
        _canvas_bs_slider = ft.Slider(min=0.2, max=5.0, value=_canvas_bs_init,
                                      divisions=48, on_change=on_canvas_beat_sens, width=160)
        _canvas_beat_sens_row = ft.Row([
            ft.Text("Beat Sens:", size=11, color="grey400", width=78),
            _canvas_bs_slider, _canvas_bs_lbl,
        ], spacing=4,
        visible=(self._spec_mode in ("beat_saber", "neon_cascade", "rock_stage")))

        # ── Hallucination sub-mode dropdown ──────────────────────────────
        def on_hallu_submode_change(e):
            _sub = str(e.control.value or "mirror").lower()
            _valid = ("mirror", "chroma", "perlin", "morph")
            self._capture_per_mode_settings("hallucination")
            self._spec_hallu_submode = _sub if _sub in _valid else "mirror"
            self._spec_hallu_prev_frame = None
            self._spec_hallu_aux = {}
            self._apply_per_mode_settings("hallucination")
            self._config_dirty = True
            _tab = _tabs.selected_index
            _clear_panel_refs()
            self._show_combined_settings(initial_tab=_tab)

        def on_hallu_base_change(e):
            self._capture_per_mode_settings("hallucination")
            self._spec_hallu_base_kind = str(e.control.value or "waveform")
            self._spec_hallu_prev_frame = None
            self._apply_per_mode_settings("hallucination")
            self._config_dirty = True
            _tab = _tabs.selected_index
            _clear_panel_refs()
            self._show_combined_settings(initial_tab=_tab)

        _hallu_options = [
            ft.dropdown.Option("mirror",   "1. Recursive Mirror"),
            ft.dropdown.Option("chroma",   "2. Chromatic Aberration"),
            ft.dropdown.Option("perlin",   "3. Perlin Flow Fields"),
            ft.dropdown.Option("morph",    "4. Geometry Morphing"),
        ]
        _valid_dd_sub = [o.key for o in _hallu_options]
        _hallu_dd_val = self._spec_hallu_submode if self._spec_hallu_submode in _valid_dd_sub else "mirror"
        _hallu_dd = ft.Dropdown(
            width=200, value=_hallu_dd_val,
            options=_hallu_options,
            on_select=on_hallu_submode_change,
            text_size=12, dense=True,
        )
        _hallu_base_options = [
            ft.dropdown.Option(bl["key"], bl["label"]) for bl in _HALLU_BASE_LAYERS
        ]
        _hallu_base_dd = ft.Dropdown(
            width=200,
            value=self._spec_hallu_base_kind
                if any(o.key == self._spec_hallu_base_kind for o in _hallu_base_options)
                else "waveform",
            options=_hallu_base_options,
            on_select=on_hallu_base_change,

            text_size=12, dense=True,
        )
        # ── Mirror-only live sliders (Inner Frame Scale / Rotation / Feedback) ──
        def _mirror_param_set(key, value):
            try:
                self._spec_hallu_params_per_submode.setdefault("mirror", {})[key] = float(value)
                self._config_dirty = True
                self._update_save_buttons()
            except Exception:
                pass

        _m_zoom_init = float(self._spec_hallu_params_per_submode.get("mirror", {}).get("zoom", 0.85))
        _m_rot_init  = float(self._spec_hallu_params_per_submode.get("mirror", {}).get("rotDeg", 10.0))
        _m_op_init   = float(self._spec_hallu_params_per_submode.get("mirror", {}).get("opacity", 1.0))

        # Ghost Spread slider is reversed: right = more spread (lower zoom value).
        # slider_val = 1.849 - zoom, so high slider → low zoom → more spread.
        _m_zoom_slider_val = max(0.85, min(0.999, round(1.849 - _m_zoom_init, 3)))
        _m_zoom_lbl = ft.Text(f"{int((0.999 - _m_zoom_init) / 0.149 * 100)}%", size=11, color="#ff9800", width=42)
        _m_rot_lbl  = ft.Text(f"{_m_rot_init:+.1f}°", size=11, color="#ff9800", width=42)
        _m_op_lbl   = ft.Text(f"{int(_m_op_init * 100)}%", size=11, color="#ff9800", width=42)

        def on_m_zoom(e):
            v = round(float(e.control.value), 3)
            zoom = max(0.85, min(0.999, round(1.849 - v, 3)))  # reversed: high slider = more spread
            _mirror_param_set("zoom", zoom)
            _m_zoom_lbl.value = f"{int((0.999 - zoom) / 0.149 * 100)}%"
            _m_zoom_lbl.update()
        def on_m_rot(e):
            v = round(float(e.control.value), 2)
            _mirror_param_set("rotDeg", v); _m_rot_lbl.value = f"{v:+.1f}°"; _m_rot_lbl.update()
        def on_m_op(e):
            v = round(float(e.control.value), 3)
            _mirror_param_set("opacity", v); _m_op_lbl.value = f"{int(v * 100)}%"; _m_op_lbl.update()

        _m_zoom_slider = ft.Slider(min=0.85, max=0.999, value=_m_zoom_slider_val,
                                divisions=149, on_change=on_m_zoom, width=160)
        _m_rot_slider  = ft.Slider(min=-10.0, max=10.0, value=_m_rot_init,
                                divisions=80,  on_change=on_m_rot,  width=160)
        _m_op_slider   = ft.Slider(min=0.5,  max=1.0,  value=_m_op_init,
                                divisions=50,  on_change=on_m_op,   width=160)

        _m_auto_spread_cb = ft.Checkbox(
            label="Auto", value=self._spec_hallu_auto_spread,
            on_change=lambda e: setattr(self, "_spec_hallu_auto_spread", bool(e.control.value)),
            active_color="#ff9800", scale=0.8,
        )
        _m_auto_rot_cb = ft.Checkbox(
            label="Auto", value=self._spec_hallu_auto_rot,
            on_change=lambda e: setattr(self, "_spec_hallu_auto_rot", bool(e.control.value)),
            active_color="#ff9800", scale=0.8,
        )
        _m_auto_blur_cb = ft.Checkbox(
            label="Auto", value=self._spec_hallu_auto_blur,
            on_change=lambda e: setattr(self, "_spec_hallu_auto_blur", bool(e.control.value)),
            active_color="#ff9800", scale=0.8,
        )
        _m_bs_init   = float(self._spec_hallu_params_per_submode.get("mirror", {}).get("beat_sens", 1.0))
        _m_bs_lbl    = ft.Text(f"{_m_bs_init:.1f}", size=11, color="#ff9800", width=42)
        def on_m_bs(e):
            v = round(float(e.control.value), 1)
            self._sa_beat_sens = v
            _mirror_param_set("beat_sens", v); _m_bs_lbl.value = f"{v:.1f}"; _m_bs_lbl.update()
        _m_bs_slider = ft.Slider(min=0.2, max=5.0, value=_m_bs_init,
                                divisions=48, on_change=on_m_bs, width=160)

        _mirror_sliders_col = ft.Column([
            ft.Row([ft.Text("Ghost Spread:", size=11, color="grey400", width=78),
                    _m_zoom_slider, _m_zoom_lbl, _m_auto_spread_cb], spacing=4),
            ft.Row([ft.Text("Rotation:",    size=11, color="grey400", width=78),
                    _m_rot_slider,  _m_rot_lbl,  _m_auto_rot_cb],  spacing=4),
            ft.Row([ft.Text("Trail Fade:",  size=11, color="grey400", width=78),
                    _m_op_slider,   _m_op_lbl,   _m_auto_blur_cb], spacing=4),
            ft.Row([ft.Text("Beat Sens:",   size=11, color="grey400", width=78),
                    _m_bs_slider,   _m_bs_lbl],                      spacing=4),
        ], spacing=2,
        visible=(self._spec_mode == "hallucination"
                    and self._spec_hallu_submode == "mirror"))

        def _morph_param_set(key, value):
            try:
                self._spec_hallu_params_per_submode.setdefault("morph", {})[key] = float(value)
                self._config_dirty = True
                self._update_save_buttons()
            except Exception:
                pass

        _morph_bs_init = float(self._spec_hallu_params_per_submode.get("morph", {}).get("beat_sens", 1.0))
        _morph_bs_lbl  = ft.Text(f"{_morph_bs_init:.1f}", size=11, color="#ff9800", width=42)
        def on_morph_bs(e):
            v = round(float(e.control.value), 1)
            self._sa_beat_sens = v
            _morph_param_set("beat_sens", v)
            _morph_bs_lbl.value = f"{v:.1f}"; _morph_bs_lbl.update()
        _morph_bs_slider = ft.Slider(min=0.2, max=5.0, value=_morph_bs_init,
                                     divisions=48, on_change=on_morph_bs, width=160)
        _morph_sliders_col = ft.Column([
            ft.Row([ft.Text("Beat Sens:", size=11, color="grey400", width=78),
                    _morph_bs_slider, _morph_bs_lbl], spacing=4),
        ], spacing=2,
        visible=(self._spec_mode == "hallucination"
                    and self._spec_hallu_submode == "morph"))

        _hallu_cm_init = self._spec_color_mode_per_mode.get("hallucination", "loop")
        _hallu_cm_dd = ft.Dropdown(
            width=180,
            options=_color_mode_options("hallucination"),
            value=_hallu_cm_init,
            on_select=on_color_mode_change, text_size=12, dense=True,

        )
        _hallu_row = ft.Column([
            ft.Row([ft.Text("Type:", size=12, color="grey400"), _hallu_dd],
                spacing=8, vertical_alignment=ft.CrossAxisAlignment.CENTER),
            ft.Row([ft.Text("Base Layer:", size=12, color="grey400"), _hallu_base_dd],
                spacing=8, vertical_alignment=ft.CrossAxisAlignment.CENTER),
            ft.Row([ft.Text("Color Mode:", size=12, color="grey400"), _hallu_cm_dd],
                spacing=8, vertical_alignment=ft.CrossAxisAlignment.CENTER),
            _mirror_sliders_col,
            _morph_sliders_col,
        ], spacing=2, visible=(self._spec_mode == "hallucination"))

        # EQ section
        _eq_labels      = ["60Hz", "170Hz", "310Hz", "600Hz", "1k", "3k", "6k", "12k", "14k", "15k"]
        _eq_value_texts = []
        _eq_sliders     = []
        _eq_preset_btns = {}
        _eq_presets = {
            "Flat":  [1.00]*10,
            "Bass+": [2.20, 1.90, 1.50, 1.25, 1.05, 0.95, 0.90, 0.88, 0.88, 0.88],
            "Smile": [1.70, 1.45, 1.15, 0.95, 0.85, 1.00, 1.20, 1.35, 1.40, 1.40],
            "Vocal": [0.85, 0.90, 0.95, 1.10, 1.25, 1.35, 1.15, 0.95, 0.90, 0.90],
        }

        def _detect_eq_preset_name():
            _cur = [round(float(v), 2) for v in self._spec_eq_gains]
            for _name, _vals in _eq_presets.items():
                if _cur == [round(float(x), 2) for x in _vals]: return _name
            return None

        _active_eq_preset = _detect_eq_preset_name()

        def _refresh_eq_preset_buttons():
            for _name, _btn in _eq_preset_btns.items():
                _color = "#ff9800" if _name == _active_eq_preset else "grey400"
                _btn.style = ft.ButtonStyle(color=_color,
                    padding=ft.Padding.symmetric(horizontal=6, vertical=2))
                try: _btn.update()
                except: pass

        def _apply_eq_preset(preset_name):
            nonlocal _active_eq_preset
            self._spec_eq_gains = list(_eq_presets.get(preset_name, _eq_presets["Flat"]))
            for i, s in enumerate(_eq_sliders):
                s.value = self._spec_eq_gains[i]
                _eq_value_texts[i].value = f"{self._spec_eq_gains[i]:.2f}x"
                _eq_value_texts[i].update(); s.update()
            _active_eq_preset = preset_name
            _refresh_eq_preset_buttons(); self._save_spec_profile()
            self._config_dirty = True; self._update_save_buttons()

        def _on_eq_change(idx, e):
            nonlocal _active_eq_preset
            v = round(float(e.control.value), 2)
            self._spec_eq_gains[idx]       = v
            _eq_value_texts[idx].value     = f"{v:.2f}x"
            _eq_value_texts[idx].update()
            _active_eq_preset = _detect_eq_preset_name()
            _refresh_eq_preset_buttons(); self._save_spec_profile()
            self._config_dirty = True; self._update_save_buttons()

        _eq_rows = []
        for i, lbl in enumerate(_eq_labels):
            _txt = ft.Text(f"{self._spec_eq_gains[i]:.2f}x", size=11, color="#ff9800", width=42)
            _eq_value_texts.append(_txt)
            _s = ft.Slider(min=0.25, max=3.0, value=float(self._spec_eq_gains[i]),
                        divisions=55, active_color="#ff9800",
                        on_change=lambda e, _i=i: _on_eq_change(_i, e), expand=True)
            _eq_sliders.append(_s)
            _eq_rows.append(ft.Row([ft.Text(lbl, size=11, color="grey400", width=38), _s, _txt], spacing=6))

        for _pname in ("Flat", "Bass+", "Smile", "Vocal"):
            _b = ft.TextButton(_pname, on_click=lambda _, n=_pname: _apply_eq_preset(n),
                            style=ft.ButtonStyle(color="grey400",
                                padding=ft.Padding.symmetric(horizontal=6, vertical=2)))
            _eq_preset_btns[_pname] = _b
        _refresh_eq_preset_buttons()

        # ── Idle effects options ──────────────────────────────────────────
        _idle_options = [
            ("pulse", "Pulse Field"), ("text", "Marquee Text"),
            ("pacman", "Pac-Man"),    ("tetris", "Tetris"),
            ("invaders", "Invaders"), ("snake", "Snake"),
            ("starwars", "Star Wars"),
        ]
        def _ensure_cycle_default():
            if not isinstance(self._spec_idle_cycle_effects, list):
                self._spec_idle_cycle_effects = [k for k, _ in _idle_options]
            self._spec_idle_cycle_effects = [k for k in self._spec_idle_cycle_effects
                                            if any(k == o[0] for o in _idle_options)]
            if not self._spec_idle_cycle_effects:
                self._spec_idle_cycle_effects = [k for k, _ in _idle_options]
        _ensure_cycle_default()

        def on_cycle_toggle(fx_key, enabled):
            _ensure_cycle_default()
            if enabled:
                if fx_key not in self._spec_idle_cycle_effects:
                    self._spec_idle_cycle_effects.append(fx_key)
            else:
                self._spec_idle_cycle_effects = [x for x in self._spec_idle_cycle_effects
                                                if x != fx_key]
                if not self._spec_idle_cycle_effects:
                    self._spec_idle_cycle_effects = [fx_key]

        _idle_checks = [
            ft.Checkbox(label=lbl, value=(k in self._spec_idle_cycle_effects),
                        on_change=lambda e, k=k: on_cycle_toggle(k, bool(e.control.value)),
                        active_color="#ff9800")
            for k, lbl in _idle_options
        ]
        _left_checks  = [c for i, c in enumerate(_idle_checks) if i % 2 == 0]
        _right_checks = [c for i, c in enumerate(_idle_checks) if i % 2 == 1]

        # ── Tab 1: SA Settings ────────────────────────────────────────────
        _tab_sa = ft.Container(
            content=ft.Column([
                ft.Row([ft.Text("Mode:", size=12, color="grey400"),
                        _mode_dd],
                    spacing=8, vertical_alignment=ft.CrossAxisAlignment.CENTER),
                _sub_row,
                _bg_col,
                _hallu_row,
                _color_mode_col,
                _canvas_beat_sens_row,
                ft.Divider(height=1, color="grey800"),
                ft.Row([ft.Text("FPS:", size=12, color="grey400"), _fps_txt,
                        ft.Slider(min=8, max=_SA_MAX_FPS, value=float(self._spec_target_fps),
                                divisions=22, active_color="#ff9800",
                                on_change=on_target_fps_change, expand=True)],
                    spacing=8, vertical_alignment=ft.CrossAxisAlignment.CENTER),
                ft.Row([ft.Text("Bars:", size=12, color="grey400"), _bars_txt,
                        ft.Slider(min=6, max=float(self._spec_bands),
                                value=float(self._spec_analysis_bands),
                                divisions=max(1, int(self._spec_bands) - 6),
                                active_color="#ff9800",
                                on_change=on_analysis_bars_change, expand=True)],
                    spacing=8, vertical_alignment=ft.CrossAxisAlignment.CENTER),
                ft.Row([ft.Text("Sensitivity:", size=12, color="grey400"), _sens_pct,
                        (_sens_slider := ft.Slider(min=0.1, max=1.5, value=self._spec_sensitivity,
                                                divisions=28, active_color="#ff9800",
                                                on_change=on_sensitivity_change, expand=True))],
                    spacing=8, vertical_alignment=ft.CrossAxisAlignment.CENTER),
                ft.Row([ft.Text("Reactivity:", size=12, color="grey400"), _react_pct,
                        (_react_slider := ft.Slider(min=0.25, max=3.0, value=self._spec_reactivity,
                                                    divisions=55, active_color="#ff9800",
                                                    on_change=on_reactivity_change, expand=True))],
                    spacing=8, vertical_alignment=ft.CrossAxisAlignment.CENTER),
                ft.Row([ft.Text("Bar Decay:", size=12, color="grey400"), _bar_decay_pct,
                        (_bar_decay_slider := ft.Slider(min=0.1, max=5.0, value=self._spec_bar_decay,
                                                        divisions=49, active_color="#ff9800",
                                                        on_change=on_bar_decay_change, expand=True))],
                    spacing=8, vertical_alignment=ft.CrossAxisAlignment.CENTER),
                ft.Row([ft.Text("Peak Decay:", size=12, color="grey400"), _peak_decay_pct,
                        (_peak_decay_slider := ft.Slider(min=0.1, max=5.0, value=self._spec_peak_decay,
                                                        divisions=49, active_color="#ff9800",
                                                        on_change=on_peak_decay_change, expand=True))],
                    spacing=8, vertical_alignment=ft.CrossAxisAlignment.CENTER),
            ], spacing=4, tight=True, scroll=ft.ScrollMode.AUTO),
            padding=ft.Padding.only(top=8),
            expand=True,
        )

        # ── Tab 2: Random/Idle ───────────────────────────────────────────

        # ── Random playlist tree helpers ──────────────────────────────────
        _mode_parent_cbs = {}
        _sm_parent_cbs   = {}
        _bl_cbs          = {}  # (mk, sk, bk) -> Checkbox

        def _group_state(mk):
            mv = self._spec_random_tree.get(mk, {})
            if not isinstance(mv, dict) or not mv.get("enabled", True):
                return False
            mode_def = next((m for m in _MODE_HIERARCHY if m["key"] == mk), None)
            if not mode_def:
                return True
            total = checked = 0
            for sm in mode_def.get("submodes", []):
                sk = sm["key"]
                if "base_layers" not in sm:
                    total += 1
                    if mv.get(sk, True):
                        checked += 1
                else:
                    sm_val = mv.get(sk, {})
                    if not isinstance(sm_val, dict) or not sm_val.get("enabled", True):
                        continue
                    for bl in sm["base_layers"]:
                        total += 1
                        if sm_val.get(bl["key"], True):
                            checked += 1
            if total == 0 or checked == 0:
                return None
            return True if checked == total else None

        def _sm_state(mk, sk):
            mv = self._spec_random_tree.get(mk, {})
            if not isinstance(mv, dict):
                return False
            sm_val = mv.get(sk, {})
            if not isinstance(sm_val, dict) or not sm_val.get("enabled", True):
                return False
            mode_def = next((m for m in _MODE_HIERARCHY if m["key"] == mk), None)
            sm_def   = next((s for s in mode_def.get("submodes", []) if s["key"] == sk), None) if mode_def else None
            if not sm_def:
                return True
            total   = len(sm_def["base_layers"])
            checked = sum(1 for bl in sm_def["base_layers"] if sm_val.get(bl["key"], True))
            if total == 0 or checked == 0:
                return None
            return True if checked == total else None

        def _refresh_group_cb(mk):
            cb = _mode_parent_cbs.get(mk)
            if cb:
                cb.value = _group_state(mk)
                try: cb.update()
                except: pass

        def _refresh_sm_cb(mk, sk):
            cb = _sm_parent_cbs.get((mk, sk))
            if cb:
                cb.value = _sm_state(mk, sk)
                try: cb.update()
                except: pass

        def _refresh_disabled(mk):
            """Grey out children whose ancestor group is disabled."""
            mv = self._spec_random_tree.get(mk, {})
            mode_on = isinstance(mv, dict) and bool(mv.get("enabled", True))
            mode_def = next((m for m in _MODE_HIERARCHY if m["key"] == mk), None)
            if not mode_def:
                return
            for sm in mode_def.get("submodes", []):
                sk = sm["key"]
                if "base_layers" not in sm:
                    cl_cb = _bl_cbs.get((mk, sk, None))
                    if cl_cb:
                        cl_cb.disabled = not mode_on
                        try: cl_cb.update()
                        except: pass
                else:
                    sm_val = mv.get(sk, {}) if isinstance(mv, dict) else {}
                    sm_on  = isinstance(sm_val, dict) and bool(sm_val.get("enabled", True))
                    sm_cb  = _sm_parent_cbs.get((mk, sk))
                    if sm_cb:
                        sm_cb.disabled = not mode_on
                        try: sm_cb.update()
                        except: pass
                    for bl in sm["base_layers"]:
                        bk    = bl["key"]
                        bl_cb = _bl_cbs.get((mk, sk, bk))
                        if bl_cb:
                            bl_cb.disabled = not (mode_on and sm_on)
                            try: bl_cb.update()
                            except: pass

        # ── Build tree rows from _MODE_HIERARCHY ──────────────────────────
        _tree_rows = []
        for _mode in _MODE_HIERARCHY:
            _mk = _mode["key"]
            if "submodes" not in _mode:
                def _on_flat(e, __mk=_mk):
                    self._spec_random_tree[__mk] = bool(e.control.value)
                    self._spec_mode_random_played = set()
                    self._config_dirty = True
                    self._update_save_buttons()
                _tree_rows.append(
                    ft.Checkbox(label=_mode["label"],
                                value=bool(self._spec_random_tree.get(_mk, True)),
                                on_change=_on_flat,
                                active_color="#ff9800", scale=0.9)
                )
            else:
                _mv = self._spec_random_tree.get(_mk, {})
                _mode_on = isinstance(_mv, dict) and bool(_mv.get("enabled", True))
                def _on_group(e, __mk=_mk):
                    _tv = self._spec_random_tree.get(__mk, {})
                    if isinstance(_tv, dict):
                        _tv["enabled"] = not bool(_tv.get("enabled", True))
                    self._spec_mode_random_played = set()
                    e.control.value = _group_state(__mk)
                    try: e.control.update()
                    except: pass
                    _refresh_disabled(__mk)
                    self._config_dirty = True
                    self._update_save_buttons()
                _pcb = ft.Checkbox(
                    label=_mode["label"], value=_group_state(_mk),
                    tristate=True, on_change=_on_group,
                    active_color="#ff9800", scale=0.9,
                )
                _mode_parent_cbs[_mk] = _pcb
                _tree_rows.append(_pcb)
                for _sm in _mode["submodes"]:
                    _sk = _sm["key"]
                    if "base_layers" not in _sm:
                        # container group: submode IS the leaf — simple checkbox
                        _cl_val = bool(_mv.get(_sk, True)) if isinstance(_mv, dict) else True
                        def _on_container_leaf(e, __mk=_mk, __sk=_sk):
                            _tv = self._spec_random_tree.get(__mk, {})
                            if isinstance(_tv, dict):
                                _tv[__sk] = bool(e.control.value)
                            self._spec_mode_random_played = set()
                            _refresh_group_cb(__mk)
                            self._config_dirty = True
                            self._update_save_buttons()
                        _clcb = ft.Checkbox(
                            label=_sm["label"], value=_cl_val,
                            disabled=not _mode_on,
                            on_change=_on_container_leaf,
                            active_color="#ff9800", scale=0.9,
                        )
                        _bl_cbs[(_mk, _sk, None)] = _clcb
                        _tree_rows.append(ft.Container(
                            content=_clcb, padding=ft.Padding.only(left=20)))
                    else:
                        # multi-renderer submode with base_layers (e.g. Hallucination)
                        _sv = _mv.get(_sk, {}) if isinstance(_mv, dict) else {}
                        _sm_on = isinstance(_sv, dict) and bool(_sv.get("enabled", True))
                        def _on_sm(e, __mk=_mk, __sk=_sk):
                            _tv = self._spec_random_tree.get(__mk, {})
                            if isinstance(_tv, dict):
                                _s = _tv.get(__sk, {})
                                if isinstance(_s, dict):
                                    _s["enabled"] = not bool(_s.get("enabled", True))
                            self._spec_mode_random_played = set()
                            e.control.value = _sm_state(__mk, __sk)
                            try: e.control.update()
                            except: pass
                            _refresh_group_cb(__mk)
                            _refresh_disabled(__mk)
                            self._config_dirty = True
                            self._update_save_buttons()
                        _smcb = ft.Checkbox(
                            label=_sm["label"], value=_sm_state(_mk, _sk),
                            disabled=not _mode_on,
                            tristate=True, on_change=_on_sm,
                            active_color="#ff9800", scale=0.9,
                        )
                        _sm_parent_cbs[(_mk, _sk)] = _smcb
                        _tree_rows.append(ft.Container(
                            content=_smcb, padding=ft.Padding.only(left=20)))
                        for _bl in _sm["base_layers"]:
                            _bk = _bl["key"]
                            _sv2 = _mv.get(_sk, {}) if isinstance(_mv, dict) else {}
                            _bl_val = bool(_sv2.get(_bk, True)) if isinstance(_sv2, dict) else True
                            def _on_leaf(e, __mk=_mk, __sk=_sk, __bk=_bk):
                                _tv = self._spec_random_tree.get(__mk, {})
                                if isinstance(_tv, dict):
                                    _s = _tv.get(__sk, {})
                                    if isinstance(_s, dict):
                                        _s[__bk] = bool(e.control.value)
                                self._spec_mode_random_played = set()
                                _refresh_sm_cb(__mk, __sk)
                                _refresh_group_cb(__mk)
                                self._config_dirty = True
                                self._update_save_buttons()
                            _blcb = ft.Checkbox(
                                label=_bl["label"], value=_bl_val,
                                disabled=not (_mode_on and _sm_on),
                                on_change=_on_leaf,
                                active_color="#ff9800", scale=0.9,
                            )
                            _bl_cbs[(_mk, _sk, _bk)] = _blcb
                            _tree_rows.append(ft.Container(
                                content=_blcb, padding=ft.Padding.only(left=40)))

        # ── Random cycle controls ─────────────────────────────────────────
        _rand_timeout_txt = ft.Text(f"{self._spec_mode_song_silence_seconds:.1f}s",
                                    size=12, color="#ff9800")

        def on_rand_timer_toggle(e):
            self._spec_mode_random_enabled = bool(e.control.value)
            if self._spec_mode_random_enabled:
                self._advance_random_mode()
                self._spec_mode_random_next_ts = time.monotonic() + float(self._spec_mode_random_cycle_seconds)
            self._config_dirty = True
            self._update_save_buttons()

        def on_rand_secs_change(e):
            try:
                self._spec_mode_random_cycle_seconds = max(5.0, min(3600.0, float(e.control.value)))
                self._config_dirty = True
                self._update_save_buttons()
            except Exception:
                pass

        def on_rand_song_toggle(e):
            self._spec_mode_random_on_song = bool(e.control.value)
            if self._spec_mode_random_on_song:
                self._advance_random_mode()
            self._config_dirty = True
            self._update_save_buttons()

        def on_rand_timeout_change(e):
            self._spec_mode_song_silence_seconds = round(float(e.control.value), 1)
            _rand_timeout_txt.value = f"{self._spec_mode_song_silence_seconds:.1f}s"
            _rand_timeout_txt.update()
            self._config_dirty = True; self._update_save_buttons()

        _tab_idle = ft.Container(
            content=ft.Column([
                ft.Text("Random Playback:", size=11, color="grey500", italic=True),
                ft.Row([
                    ft.Checkbox(label="Random cycle every",
                                value=self._spec_mode_random_enabled,
                                on_change=on_rand_timer_toggle,
                                active_color="#ff9800", scale=0.85),
                    ft.TextField(value=str(int(self._spec_mode_random_cycle_seconds)),
                                width=52, height=28, text_size=11, dense=True,
                                content_padding=ft.Padding.symmetric(horizontal=6, vertical=2),
                                on_submit=on_rand_secs_change, on_blur=on_rand_secs_change),
                    ft.Text("sec", size=11, color="grey400"),
                ], spacing=4, vertical_alignment=ft.CrossAxisAlignment.CENTER),
                ft.Row([
                    ft.Checkbox(label="New mode on song change",
                                value=self._spec_mode_random_on_song,
                                on_change=on_rand_song_toggle,
                                active_color="#ff9800", scale=0.85),
                ], spacing=4, vertical_alignment=ft.CrossAxisAlignment.CENTER),
                ft.Row([ft.Text("Song Timeout:", size=12, color="grey400", width=90),
                        _rand_timeout_txt,
                        ft.Slider(min=1.0, max=15.0,
                                value=float(self._spec_mode_song_silence_seconds),
                                divisions=28, active_color="#ff9800",
                                on_change=on_rand_timeout_change, expand=True)],
                    spacing=8, vertical_alignment=ft.CrossAxisAlignment.CENTER),
                ft.Divider(height=1, color="grey800"),
                ft.Text("Modes in Random Playlist:", size=11, color="grey500", italic=True),
                *_tree_rows,
                ft.Divider(height=1, color="grey800"),
                ft.Text("Idle Effects:", size=11, color="grey500", italic=True),
                ft.Row([ft.Text("Idle Effect:", size=12, color="grey400"),
                        ft.Dropdown(width=160, value=self._spec_idle_effect,
                            options=[ft.dropdown.Option(k, v) for k, v in [
                                ("random","Random Cycle"),("pulse","Pulse"),("text","Text"),
                                ("pacman","Pac-Man"),("tetris","Tetris"),("invaders","Invaders"),
                                ("snake","Snake"),("starwars","Star Wars")]],
                on_select=on_idle_effect_change, text_size=12, dense=True)],

                    spacing=8, vertical_alignment=ft.CrossAxisAlignment.CENTER),
                ft.Text("Cycle Selection:", size=11, color="grey500", italic=True),
                ft.Row([
                    ft.Column(_left_checks,  spacing=0, tight=True, expand=True),
                    ft.Column(_right_checks, spacing=0, tight=True, expand=True),
                ], spacing=10, expand=True),
                ft.Row([ft.Text("Timeout:", size=12, color="grey400", width=62), _idle_timeout_txt,
                        ft.Slider(min=2.0, max=30.0, value=self._spec_idle_timeout,
                                divisions=28, active_color="#ff9800",
                                on_change=on_idle_timeout_change, expand=True)],
                    spacing=8, vertical_alignment=ft.CrossAxisAlignment.CENTER),
                ft.Row([ft.Text("Idle Speed:", size=12, color="grey400", width=62), _idle_speed_txt,
                        ft.Slider(min=0.25, max=3.0, value=self._spec_idle_speed,
                                divisions=55, active_color="#ff9800",
                                on_change=on_idle_speed_change, expand=True)],
                    spacing=8, vertical_alignment=ft.CrossAxisAlignment.CENTER),
            ], spacing=4, tight=True, scroll=ft.ScrollMode.AUTO),
            padding=ft.Padding.only(top=8),
            expand=True,
        )

        # ── Tab 3: Visual EQ ──────────────────────────────────────────────
        _tab_eq = ft.Container(
            content=ft.Column([
                ft.Row([ft.Text("Presets:", size=12, color="grey400"),
                        *list(_eq_preset_btns.values())], spacing=2),
                ft.Divider(height=1, color="grey800"),
                ft.Column(_eq_rows, spacing=2, tight=True),
            ], spacing=6, tight=True, scroll=ft.ScrollMode.AUTO),
            padding=ft.Padding.only(top=8),
            expand=True,
        )

        # ── Tab 4: Sound Sources ──────────────────────────────────────────
        source_list = ft.Column(_build_source_buttons(), scroll="auto", tight=True)
        _tab_sources = ft.Container(
            content=ft.Column([
                ft.Row([ft.Text("Sample Rate:", size=12, color="grey400"),
                        ft.Dropdown(width=130, value=str(int(self._spec_sample_rate)),
                            options=[ft.dropdown.Option(str(r)) for r in (16000, 22050, 32000, 44100, 48000)],
                on_select=on_sample_rate_change, text_size=12, dense=True)],

                    spacing=8, vertical_alignment=ft.CrossAxisAlignment.CENTER),
                ft.Divider(height=1, color="grey800"),
                ft.Text("Select audio source:", size=12, color="grey400"),
                source_list,
            ], spacing=8, tight=True, scroll=ft.ScrollMode.AUTO),
            padding=ft.Padding.only(top=8),
            expand=True,
        )

        # ── Tabs widget ───────────────────────────────────────────────────
        _tabs = ft.Tabs(
            selected_index=initial_tab,
            length=4,
            animation_duration=ft.Duration(milliseconds=150),
            on_change=lambda e: self._on_settings_tab_change(int(e.control.selected_index or 0)),
            content=ft.Column([
                ft.TabBar(
                    tabs=[
                        ft.Tab(label="SA Settings"),
                        ft.Tab(label="Random/Idle"),
                        ft.Tab(label="Visual EQ"),
                        ft.Tab(label="Sources"),
                    ],
                    indicator_color="#ff9800",
                    label_color="#ff9800",
                    unselected_label_color="grey500",
                    label_text_style=ft.TextStyle(size=11),
                    unselected_label_text_style=ft.TextStyle(size=11),
                    scrollable=False,
                    tab_alignment=ft.TabAlignment.FILL,
                ),
                ft.TabBarView(
                    controls=[_tab_sa, _tab_idle, _tab_eq, _tab_sources],
                    expand=True,
                ),
            ], tight=True, expand=True, height=510),
        )

        _close_btn = ft.IconButton(
            icon=ft.Icons.CLOSE, icon_size=14,
            tooltip="Close (no save)",
            style=ft.ButtonStyle(
                bgcolor="transparent",
                shape=ft.RoundedRectangleBorder(radius=4),
                padding=ft.Padding.all(2),
            ),
            on_click=_do_close,
        )

        _dirty_lbl = ft.Text("", size=11, color="#e67e22", italic=True)
        self._settings_dirty_label = _dirty_lbl

        _save_btn = ft.Button(
            "SAVE", on_click=_do_save,
            bgcolor="#1a1a2e", color="white",
        )
        self._settings_save_btn = _save_btn

        # Reflect current dirty state immediately in case menu was reopened while dirty
        self._update_save_buttons()

        panel = ft.Container(
            content=ft.Column([
                ft.Row([
                    ft.Container(expand=True),
                    _close_btn,
                ], spacing=0),
                _tabs,
                ft.Divider(height=1, color="grey700"),
                ft.Row([
                    _dirty_lbl,
                    ft.TextButton("UNDO", on_click=_do_reload),
                    _save_btn,
                    ft.Button("Save & Exit", on_click=_do_save_and_exit,
                                    bgcolor="#1a1a2e", color="white"),
                    ft.TextButton("Close", on_click=_do_close),
                ], alignment=ft.MainAxisAlignment.END, spacing=8),
            ], tight=True, spacing=4),
            bgcolor="#0c0c18",
            border=ft.Border.all(1, "#2b2b3b"),
            border_radius=6,
            padding=ft.Padding.all(10),
        )
        self._menu_host.controls = [panel]
        self._menu_host.visible  = True
        self._expand_for_menu(_SA_MENU_W, _SA_MENU_H)
        try:   self._menu_host.update()
        except: self.page.update()

    # ── Render dispatcher ─────────────────────────────────────────────────────

    def _render_spectrum(self):
        if not self._spec_segments or self._spec_mode_transitioning:
            return

        if self._menu_rebuild_requested:
            self._menu_rebuild_requested = False
            try:
                self._show_combined_settings(initial_tab=self._menu_last_tab)
            except Exception:
                pass

        self._compute_audio_frame()
        _mode = str(self._spec_mode or "classic").lower()
        _timer_random = self._spec_mode_random_enabled or (_mode == "random")
        _song_random  = self._spec_mode_random_on_song  or (_mode == "random_song")
        if _timer_random or _song_random:
            _now = time.monotonic()
            if _timer_random and _now >= float(self._spec_mode_random_next_ts):
                self._advance_random_mode()
                self._spec_mode_random_next_ts = _now + max(1.0, self._spec_mode_random_cycle_seconds)
            if _song_random and self._spec_mode_song_switch_armed:
                if (_now - float(self._spec_last_audio_ts)) >= float(self._spec_mode_song_silence_seconds):
                    self._advance_random_mode()
                    self._spec_mode_song_switch_armed = False
            _mode = self._spec_mode_random_current

        if self._spec_idle_active:
            _idle_fx = str(self._spec_idle_effect or "random").lower()
            if _idle_fx == "random":
                _now = time.monotonic()
                if _now >= float(self._spec_idle_random_next_ts) and self._spec_idle_cycle_done:
                    _choices = list(self._spec_idle_cycle_effects or
                                    ["pulse","text","pacman","tetris","invaders","snake","starwars"])
                    if self._spec_idle_random_current in _choices and len(_choices) > 1:
                        _choices = [x for x in _choices if x != self._spec_idle_random_current]
                    self._spec_idle_random_current  = random.choice(_choices)
                    self._spec_idle_random_next_ts  = _now + max(0.1, float(self._spec_idle_random_cycle_seconds))
                    self._spec_idle_cycle_done       = False
                    self._spec_idle_phase            = 0.0
                    self._spec_idle_scroll           = 0
                _idle_fx = self._spec_idle_random_current
            if _idle_fx == "starwars":
                self._set_spectrum_render_mode("graphics")
                self._render_spectrum_idle_starwars()
                return
            self._set_spectrum_render_mode("grid")
            if   _idle_fx == "text":     self._render_spectrum_idle_text()
            elif _idle_fx == "pulse":    self._render_spectrum_idle_pulse()
            elif _idle_fx == "pacman":   self._render_spectrum_idle_pacman()
            elif _idle_fx == "tetris":   self._render_spectrum_idle_tetris()
            elif _idle_fx == "invaders": self._render_spectrum_idle_invaders()
            elif _idle_fx == "snake":    self._render_spectrum_idle_snake()
            else:                        self._render_spectrum_idle_pulse()
            return

        if _mode in ("neon_drift", "retro_tech", "custom_vu", "hud_reactor", "beat_saber", "neon_cascade", "rock_stage", "neon_vu"):
            if   _mode == "neon_drift":   self._neon_vu_theme = "neon_drift";   _bg = self._spec_nvu_drift_bg
            elif _mode == "retro_tech":   self._neon_vu_theme = "retro_tech";   _bg = self._spec_nvu_retro_bg
            elif _mode == "custom_vu":    self._neon_vu_theme = "custom_vu";    _bg = self._spec_nvu_custom_bg
            elif _mode == "hud_reactor":  self._neon_vu_theme = "hud_reactor";  _bg = self._spec_nvu_hud_bg
            elif _mode == "beat_saber":   self._neon_vu_theme = "beat_saber";   _bg = self._spec_nvu_bs_bg
            elif _mode == "neon_cascade": self._neon_vu_theme = "neon_cascade"; _bg = self._spec_nvu_cascade_bg
            elif _mode == "rock_stage":   self._neon_vu_theme = "rock_stage";   _bg = self._spec_nvu_rock_bg
            else:                         _bg = (self._spec_nvu_drift_bg if self._neon_vu_theme == "neon_drift"
                                                else self._spec_nvu_retro_bg)
            if self._neon_vu_bg_image:
                _v = (_bg != "BLANK") and os.path.isfile(os.path.join(self._version_dir, _bg))
                _s = _bg if _v else ""
                if getattr(self, "_spec_nvu_bg_force_reload", False):
                    _s = f"{_s}?t={time.time()}" if _s else ""
                _tgt_opacity = 0.50 if _mode == "rock_stage" else 0.80
                _tgt_fit = ft.BoxFit.CONTAIN if self._spec_nvu_bg_contain.get(_mode, False) else ft.BoxFit.COVER
                if (self._neon_vu_bg_image.src != _s or self._neon_vu_bg_image.visible != _v
                        or self._neon_vu_bg_image.opacity != _tgt_opacity
                        or self._neon_vu_bg_image.fit != _tgt_fit):
                    self._spec_nvu_bg_force_reload = False
                    self._neon_vu_bg_image.src     = _s
                    self._neon_vu_bg_image.visible = _v
                    self._neon_vu_bg_image.opacity = _tgt_opacity
                    self._neon_vu_bg_image.fit     = _tgt_fit
                    try: self._neon_vu_bg_image.update()
                    except: pass
            self._set_spectrum_render_mode("neon_vu")
            if   self._neon_vu_theme == "hud_reactor":  self._render_spectrum_hud_reactor()
            elif self._neon_vu_theme == "beat_saber":   self._render_spectrum_beatsaber()
            elif self._neon_vu_theme == "neon_cascade": self._render_spectrum_neon_cascade()
            elif self._neon_vu_theme == "rock_stage":   self._render_spectrum_rock_stage()
            else:                                        self._render_spectrum_neon_vu()
            return

        if _mode == "hallucination":
            self._set_spectrum_render_mode("hallucination")
            self._render_hallucination()
            return

        self._set_spectrum_render_mode("grid")
        if   _mode == "vu":         self._render_spectrum_vu()
        elif _mode == "cyber_city": self._render_spectrum_cybercity()
        else:                       self._render_spectrum_classic()
        try: self._spectrum_box.update()
        except: pass

    # ── Grid render modes ─────────────────────────────────────────────────────

    def _render_spectrum_classic(self):
        _analysis_count = max(1, len(self._spec_bars))
        for bi, segs in enumerate(self._spec_segments):
            _src_i = min(_analysis_count - 1, int((bi * _analysis_count) / max(1, self._spec_bands)))
            fill   = int(max(0.0, min(1.0, self._spec_bars[_src_i]))  * self._spec_levels)
            peak   = int(max(0.0, min(1.0, self._spec_peaks[_src_i])) * (self._spec_levels - 1))
            for top_idx, seg in enumerate(segs):
                lvl = self._spec_levels - 1 - top_idx
                if lvl == peak:          seg.bgcolor = "#ff2020"
                elif lvl < fill:         seg.bgcolor = self._spec_palette[lvl]
                else:                    seg.bgcolor = "#101010"

    def _render_spectrum_cybercity(self):
        """Cyber City mode: bands become glowing buildings with flickering windows."""
        _analysis_count = max(1, len(self._spec_bars))
        _bands  = self._spec_bands
        _levels = self._spec_levels
        _now    = time.monotonic()
        for bi, segs in enumerate(self._spec_segments):
            _src_i = min(_analysis_count - 1, int((bi * _analysis_count) / max(1, _bands)))
            val    = self._spec_bars[_src_i]
            peak   = self._spec_peaks[_src_i]
            fill_h = int(val * _levels)
            peak_h = int(peak * (_levels - 1))
            for top_idx, seg in enumerate(segs):
                y = _levels - 1 - top_idx
                if y == peak_h and peak_h > 0:
                    seg.bgcolor = "#ff3030"  # Neon Red helipad/beacon
                elif y < peak_h:
                    if (y % 2 == 0) and (bi % 2 == 0):
                        if y < fill_h:
                            _val = math.sin(_now * 3.5 + bi * 0.5 + y)
                            if _val > -0.8:
                                seg.bgcolor = "#00f2ff"  # Active Cyan window
                            else:
                                seg.bgcolor = "#333333"  # Unlit Grey window
                        else:
                            seg.bgcolor = "#333333"  # Static unlit window
                    else:
                        seg.bgcolor = "#0a0a20"  # Building shadow/dark facade
                else:
                    seg.bgcolor = "#050505"  # Night sky

    def _render_spectrum_beatsaber(self):
        """Glowing orbs + spectrum waveform laser: orb speed/brightness from volume, white bass flash, color shifts."""
        if cv is None or self._neon_vu_canvas is None: return
        _W, _H   = 300.0, 62.0
        _vx, _vy = _W / 2.0, _H / 2.0
        _now     = time.monotonic()
        _ana     = max(1, len(self._spec_bars))

        # ── Lazy-init persistent state ────────────────────────────────────────
        if not hasattr(self, '_bs_hue_from'):
            self._bs_hue_from  = 0.60
            self._bs_hue_to    = 0.60
            self._bs_hue_t     = 1.0
            self._bs_hit_flash = 0.0
            self._bs_last_t    = _now
            self._bs_hue_seq   = [0.00, 0.77, 0.50, 0.33, 0.08]  # red→purple→cyan→green→orange
            self._bs_orbs      = []    # list of live orb dicts
            self._bs_spawn_cd  = 0.0  # seconds until next spawn is allowed
            self._bs_silence_fade = 1.0

        _dt = min(0.08, _now - self._bs_last_t)
        self._bs_last_t = _now

        # ── Audio ─────────────────────────────────────────────────────────────
        _bar = self._bar
        _sb = self._sa_smth_bass
        _sv = self._sa_smth_vu

        # ── Silence fade ───────────────────────────────────────────────────────
        if self._sa_mono_vu < 0.015:
            self._bs_silence_fade = max(0.0, self._bs_silence_fade - _dt * 0.5)
        else:
            self._bs_silence_fade = min(1.0, self._bs_silence_fade + _dt * 3.0)
        _sf = self._bs_silence_fade
        self._current_sf = _sf
        if _sf <= 0.0:
            try: self._neon_vu_canvas.shapes = []; self._neon_vu_canvas.update()
            except: pass
            return

        # ── Color: smooth hue transition on bass hit ──────────────────────────
        _lerp_h = self._lerp_h; _ease = self._ease

        _new_beat_bs = self._sa_beat_detected
        if _new_beat_bs:
            self._bs_hue_from  = _lerp_h(self._bs_hue_from, self._bs_hue_to, _ease(self._bs_hue_t))
            self._bs_hue_to    = self._bs_hue_seq[0]
            self._bs_hue_seq   = self._bs_hue_seq[1:] + [self._bs_hue_seq[0]]
            self._bs_hue_t     = 0.0
            self._bs_hit_flash = 1.0
        self._bs_hue_t     = min(1.0, self._bs_hue_t + _dt / 0.55)
        self._bs_hit_flash = max(0.0, self._bs_hit_flash - _dt * 2.0)

        _hue = _lerp_h(self._bs_hue_from, self._bs_hue_to, _ease(self._bs_hue_t))
        self._spec_display_hue = _hue

        _rgb = self._rgb; _wo = self._wo

        _is_grad = (self._tick_random_cm("beat_saber", _new_beat_bs) == "gradient")
        def _ghue(frac): return frac * 0.33   # red→orange→yellow→green across 0‥1

        _C  = _rgb(_hue)               # main neon color (loop mode)
        _Cd = _rgb(0.16, 0.40, 0.18) if _is_grad else _rgb(_hue, 0.60, 0.28)
        _Cw = "#ffffff"

        shapes = []

        # ── Scrim — dark overlay to keep effects readable over BG image ────────
        if self._spec_nvu_bs_bg != "BLANK":
            shapes.append(cv.Rect(
                x=0.0, y=0.0, width=_W, height=_H,
                paint=ft.Paint(color=ft.Colors.with_opacity(0.45, "#000000"),
                            style=ft.PaintingStyle.FILL)))

        # ── Layer 1 — Background haze ─────────────────────────────────────────
        # Soft centered oval glow that blooms with volume
        _hr = 70.0 + _sv * 45.0
        for _rx, _ry, _oa in [(1.00, 0.30, 0.08), (0.60, 0.18, 0.05), (0.30, 0.10, 0.03)]:
            shapes.append(cv.Oval(
                x=_vx - _hr*_rx, y=_vy - _hr*_ry, width=_hr*_rx*2.0, height=_hr*_ry*2.0,
                paint=ft.Paint(color=_wo(_oa + _sv*0.06, _Cd), style=ft.PaintingStyle.FILL)))

        # ── Layer 2 — Spectrum waveform (the reactive laser) ──────────────────
        _WSAMP  = max(4, _ana)
        _W_AMP  = 20.0 + _sv * 6.0
        _wf_pts = []   # (x, y_top, y_bot)
        for _xi in range(_WSAMP + 1):
            _xpos  = _xi / float(_WSAMP) * _W
            _fi_f  = _xi / float(_WSAMP) * max(1, _ana - 1)
            _fi_lo = int(_fi_f);  _fi_hi = min(_ana - 1, _fi_lo + 1)
            _bval  = _bar(_fi_lo) * (1.0 - (_fi_f - _fi_lo)) + _bar(_fi_hi) * (_fi_f - _fi_lo)
            _disp  = _bval * _W_AMP
            _wf_pts.append((_xpos, _vy - _disp, _vy + _disp))
        def _chaikin(pts, iters):
            for _ in range(iters):
                out = [pts[0]]
                for i in range(len(pts) - 1):
                    p0, p1 = pts[i], pts[i + 1]
                    out.append((0.75*p0[0] + 0.25*p1[0], 0.75*p0[1] + 0.25*p1[1]))
                    out.append((0.25*p0[0] + 0.75*p1[0], 0.25*p0[1] + 0.75*p1[1]))
                out.append(pts[-1])
                pts = out
            return pts
        _chk_top = _chaikin([(x, yt) for (x, yt, yb) in _wf_pts], 1 if _is_grad else 2)
        _chk_bot = _chaikin([(x, yb) for (x, yt, yb) in _wf_pts], 1 if _is_grad else 2)
        _wf_pts  = [(_chk_top[i][0], _chk_top[i][1], _chk_bot[i][1]) for i in range(len(_chk_top))]
        _top_f   = [cv.Path.MoveTo(_chk_top[0][0], _chk_top[0][1])]
        for _x, _y in _chk_top[1:]:
            _top_f.append(cv.Path.LineTo(_x, _y))
        _bot_f   = [cv.Path.MoveTo(_chk_bot[0][0], _chk_bot[0][1])]
        for _x, _y in _chk_bot[1:]:
            _bot_f.append(cv.Path.LineTo(_x, _y))

        if _is_grad:
            _ghue_cap = _ghue   # capture by value to avoid any closure ambiguity
            def _bs_cfn(frac, _gh=_ghue_cap):
                r, g, b = colorsys.hsv_to_rgb(_gh(frac) % 1.0, 1.0, 1.0)
                return (int(r * 255), int(g * 255), int(b * 255))
            _top_pts = [(_p[0], _p[1]) for _p in _wf_pts]
            _bot_pts = [(_p[0], _p[2]) for _p in _wf_pts]
            shapes.append(_PilGradPolyline(
                _top_pts, _bs_cfn,
                [(9.0, 0.06*_sf), (4.5, 0.16*_sf), (1.8, 0.55*_sf), (0.6, 1.00*_sf)],
                _W))
            shapes.append(_PilGradPolyline(
                _bot_pts, _bs_cfn,
                [(9.0*0.85, 0.06*0.75*_sf), (4.5*0.85, 0.16*0.75*_sf),
                (1.8*0.85, 0.55*0.75*_sf), (0.6*0.85, 0.75*_sf)],
                _W))
        else:
            _fill_pts = list(_top_f)
            for _x, _y in reversed(_chk_bot):
                _fill_pts.append(cv.Path.LineTo(_x, _y))
            _fill_pts.append(cv.Path.Close())
            shapes.append(cv.Path(elements=_fill_pts,
                paint=ft.Paint(color=_wo(0.10 + _sv*0.08, _C), style=ft.PaintingStyle.FILL)))
            for _gw, _ga in ((9.0, 0.06), (4.5, 0.16), (1.8, 0.55), (0.6, 1.00)):
                shapes.append(cv.Path(elements=_top_f,
                    paint=ft.Paint(color=_wo(_ga, _C),
                                stroke_width=_gw, style=ft.PaintingStyle.STROKE)))
                shapes.append(cv.Path(elements=_bot_f,
                    paint=ft.Paint(color=_wo(_ga * 0.75, _C),
                                stroke_width=_gw * 0.85, style=ft.PaintingStyle.STROKE)))

        # ── Layer 3 — Sweeping laser lines (react hard to their band) ──────────
        # Three horizontal beams that become bright and thick when their band is loud
        for _k, (_fi, _period, _sw_max, _amp) in enumerate([
            (0,        3.5, 7.0, 0.40),   # bass: slow thick sweep
            (_ana//3,  5.2, 4.0, 0.27),   # mids
            (_ana-1,   7.8, 2.2, 0.17),   # highs: fast thin
        ]):
            _bval = _bar(_fi)
            _yoff = math.sin(_now / _period + _k * 2.09) * _H * _amp * (0.3 + _bval * 0.7)
            _ya   = _vy + _yoff
            _sw   = _sw_max * (0.15 + _bval * 0.85)
            _la   = 0.10 + _bval * 0.80
            _lc   = _rgb(_ghue(_fi / max(1, _ana - 1))) if _is_grad else _C
            for _gw, _gm in ((_sw*5.0, 0.05), (_sw*2.5, 0.14), (_sw, 0.55), (_sw*0.25, 1.0)):
                if _gw < 0.1: continue
                shapes.append(cv.Line(x1=0.0, y1=_ya, x2=_W, y2=_ya,
                    paint=ft.Paint(color=_wo(_la*_gm, _lc), stroke_width=_gw)))

        # ── Layer 4 — Glowing orbs (spawned by audio, physics-driven) ────────────
        _MAX_ORBS  = 8
        _SPAWN_TH  = 0.42    # band level needed to spawn an orb
        _SUST_TH   = 0.28    # band level to sustain an orb's life
        _SPAWN_CD  = 0.20    # min seconds between spawns
        _LIFE_IN   = 3.5     # life gain per second while sustained
        _LIFE_OUT  = 0.70    # life loss per second when band drops out
        _BASE_VX   = 55.0    # pixels/sec horizontal speed at VU=1.0
        _BASE_VY   = 18.0    # pixels/sec vertical speed at VU=1.0 (canvas is short)

        # Advance spawn cooldown
        self._bs_spawn_cd = max(0.0, self._bs_spawn_cd - _dt)

        # Try to spawn a new orb from the loudest untracked band
        if self._bs_spawn_cd <= 0.0 and len(self._bs_orbs) < _MAX_ORBS and _sv > 0.18:
            _tracked = {o['fi'] for o in self._bs_orbs}
            _best_fi = -1;  _best_val = _SPAWN_TH
            for _fi in range(_ana):
                if _fi not in _tracked and _bar(_fi) > _best_val:
                    _best_val = _bar(_fi);  _best_fi = _fi
            if _best_fi >= 0:
                _ang = random.uniform(0.0, 2.0 * math.pi)
                self._bs_orbs.append({
                    'x':  random.uniform(18.0, _W - 18.0),
                    'y':  random.uniform(8.0,  _H  - 8.0),
                    'vx': math.cos(_ang) * _BASE_VX * random.uniform(0.4, 1.0),
                    'vy': math.sin(_ang) * _BASE_VY * random.uniform(0.4, 1.0),
                    'fi': _best_fi,
                    'sz': random.uniform(4.2, 6.8),
                    'life': 0.01,
                })
                self._bs_spawn_cd = _SPAWN_CD

        # Physics update + sustain/fade each orb
        _spd_mul = 0.25 + _sv * 1.0    # 0.25× at silence → 1.25× at full volume
        _alive = []
        for _o in self._bs_orbs:
            _o['x'] += _o['vx'] * _dt * _spd_mul
            _o['y'] += _o['vy'] * _dt * _spd_mul
            # Bounce off canvas walls
            if _o['x'] < 14.0:    _o['x'] = 14.0;    _o['vx'] =  abs(_o['vx'])
            if _o['x'] > _W-14:   _o['x'] = _W-14;   _o['vx'] = -abs(_o['vx'])
            if _o['y'] < 7.0:     _o['y'] = 7.0;     _o['vy'] =  abs(_o['vy'])
            if _o['y'] > _H-7:    _o['y'] = _H-7;    _o['vy'] = -abs(_o['vy'])
            # Life: grow while band is loud, fade when it drops
            if _bar(_o['fi']) >= _SUST_TH:
                _o['life'] = min(1.0, _o['life'] + _dt * _LIFE_IN)
            else:
                _o['life'] = max(0.0, _o['life'] - _dt * _LIFE_OUT)
            if _o['life'] > 0.0:
                _alive.append(_o)
        self._bs_orbs = _alive

        # Render each live orb
        for _o in self._bs_orbs:
            _ox    = _o['x'];  _oy = _o['y'];  _life = _o['life']
            _bval  = _bar(_o['fi'])
            _bright = _life * (0.25 + _sv*0.45 + _bval*0.35)
            _r_live = _o['sz'] * _life * (0.65 + _sv*0.45 + _bval*0.45)
            _oc    = _rgb(_ghue(_o['fi'] / max(1, _ana - 1))) if _is_grad else _C
            for _r2, _ra in ((_r_live*5.5, 0.03), (_r_live*3.0, 0.09),
                            (_r_live*1.8, 0.22), (_r_live,     0.72)):
                shapes.append(cv.Circle(x=_ox, y=_oy, radius=_r2,
                    paint=ft.Paint(color=_wo(min(1.0, _ra*_bright), _oc),
                                style=ft.PaintingStyle.FILL)))
            shapes.append(cv.Circle(x=_ox, y=_oy, radius=max(0.5, _r_live*0.30),
                paint=ft.Paint(color=_wo(min(1.0, 0.55 + _bright*0.5), _Cw),
                            style=ft.PaintingStyle.FILL)))

        # ── Layer 5 — White bass flash ────────────────────────────────────────
        _hf = self._bs_hit_flash
        if _hf > 0.01:
            _fe = _hf * _hf  # ease-out
            # Expanding white ring
            _ring_r = 10.0 + (1.0 - _hf) * 85.0
            shapes.append(cv.Circle(x=_vx, y=_vy, radius=_ring_r,
                paint=ft.Paint(color=_wo(_fe * 0.75, _Cw),
                            stroke_width=3.5 + _fe*4.0, style=ft.PaintingStyle.STROKE)))
            # Central white burst
            shapes.append(cv.Circle(x=_vx, y=_vy, radius=6.0 + _fe*28.0,
                paint=ft.Paint(color=_wo(_fe * 0.85, _Cw), style=ft.PaintingStyle.FILL)))
            # Subtle full-canvas bloom in current color
            shapes.append(cv.Oval(x=0.0, y=0.0, width=_W, height=_H,
                paint=ft.Paint(color=_wo(_fe * 0.18, _C), style=ft.PaintingStyle.FILL)))

        try:
            self._neon_vu_canvas.shapes = shapes
            self._neon_vu_canvas.update()
        except Exception:
            pass

    def _render_spectrum_neon_cascade(self):
        """Neon Cascade: rising pillar ribbons + aurora sweep + spectrum curve + spark fountain."""
        if cv is None or self._neon_vu_canvas is None: return
        _W, _H = 300.0, 62.0
        _now   = time.monotonic()
        _ana   = max(1, len(self._spec_bars))

        # ── Lazy-init persistent state ────────────────────────────────────────
        if not hasattr(self, '_nc_hue_from'):
            self._nc_hue_from    = 0.55   # start: cyan-blue
            self._nc_hue_to      = 0.55
            self._nc_hue_t       = 1.0
            self._nc_hit_flash   = 0.0
            self._nc_last_t      = _now
            self._nc_hue_seq     = [0.00, 0.77, 0.50, 0.16, 0.33]  # red→purple→cyan→orange→green
            self._nc_sparks      = []
            self._nc_spawn_cd    = 0.0
            self._nc_aurora_ph   = 0.0
            self._nc_curve_peaks = [0.0] * _ana
            self._nc_curve_hold  = [0.0] * _ana  # seconds remaining before each peak starts falling
            self._nc_silence_fade = 1.0

        _dt = min(0.08, _now - self._nc_last_t)
        self._nc_last_t = _now

        # ── Audio ─────────────────────────────────────────────────────────────
        _bar = self._bar
        _sb = self._sa_smth_bass
        _sv = self._sa_smth_vu

        # ── Silence fade ───────────────────────────────────────────────────────
        if self._sa_mono_vu < 0.015:
            self._nc_silence_fade = max(0.0, self._nc_silence_fade - _dt * 0.5)
        else:
            self._nc_silence_fade = min(1.0, self._nc_silence_fade + _dt * 3.0)
        _sf = self._nc_silence_fade
        self._current_sf = _sf
        if _sf <= 0.0:
            try: self._neon_vu_canvas.shapes = []; self._neon_vu_canvas.update()
            except: pass
            return

        # ── Hue: smooth transition on bass hit ────────────────────────────────
        _lerp_h = self._lerp_h; _ease = self._ease

        _new_beat_nc = self._sa_beat_detected
        if _new_beat_nc:
            self._nc_hue_from  = _lerp_h(self._nc_hue_from, self._nc_hue_to, _ease(self._nc_hue_t))
            self._nc_hue_to    = self._nc_hue_seq[0]
            self._nc_hue_seq   = self._nc_hue_seq[1:] + [self._nc_hue_seq[0]]
            self._nc_hue_t     = 0.0
            self._nc_hit_flash = 1.0
        self._nc_hue_t     = min(1.0, self._nc_hue_t + _dt / 0.55)
        self._nc_hit_flash = max(0.0, self._nc_hit_flash - _dt * 2.0)

        _hue = _lerp_h(self._nc_hue_from, self._nc_hue_to, _ease(self._nc_hue_t))
        self._spec_display_hue = _hue

        _rgb = self._rgb; _wo = self._wo

        _is_grad = (self._tick_random_cm("neon_cascade", _new_beat_nc) == "gradient")
        def _ghue(frac): return frac * 0.33   # red→orange→yellow→green across 0‥1

        _C  = _rgb(_hue)
        _Cw = "#ffffff"
        _Cd = _rgb(0.16, 0.40, 0.18) if _is_grad else _rgb(_hue, 0.50, 0.22)

        shapes = []

        # ── Scrim — dark overlay to keep effects readable over BG image ────────
        if self._spec_nvu_cascade_bg != "BLANK":
            shapes.append(cv.Rect(
                x=0.0, y=0.0, width=_W, height=_H,
                paint=ft.Paint(color=ft.Colors.with_opacity(0.45, "#000000"),
                            style=ft.PaintingStyle.FILL)))

        # ── Layer 1 — Background ambient bloom ────────────────────────────────
        # Soft horizontal glow at bottom that grows with volume
        _bloom_h = 14.0 + _sv * 18.0
        shapes.append(cv.Oval(
            x=0.0, y=_H - _bloom_h * 1.6, width=_W, height=_bloom_h * 3.2,
            paint=ft.Paint(color=_wo(0.06 + _sv * 0.08, _Cd), style=ft.PaintingStyle.FILL)))

        # ── Layer 2 — Neon pillar ribbons (vertical, rising from bottom) ──────
        _BAR_W  = _W / max(1, _ana)
        _MAX_PH = _H * 0.80  # tallest possible pillar

        for _bi in range(_ana):
            _bval = _bar(_bi)
            if _bval < 0.015: continue
            _ph   = _bval * _MAX_PH
            _bx   = (_bi + 0.5) * _BAR_W
            _pw   = max(2.0, _BAR_W * 0.82)
            _bh   = _ghue(_bi / max(1, _ana - 1)) if _is_grad else (_hue + (_bi / max(1, _ana - 1) - 0.5) * 0.10) % 1.0
            _bc   = _rgb(_bh)
            _bright = 0.45 + _bval * 0.55
            # Multi-pass neon glow (wide+dim → narrow+bright)
            for _gw, _ga in ((_pw * 4.0, 0.03), (_pw * 2.2, 0.09), (_pw, 0.28), (_pw * 0.42, 0.82)):
                shapes.append(cv.Line(
                    x1=_bx, y1=_H, x2=_bx, y2=_H - _ph,
                    paint=ft.Paint(color=_wo(_ga * _bright, _bc), stroke_width=_gw)))

        # ── Layer 3 — Spectrum waveform curve (slow-decay caps, classic-SA style) ─
        # Instant attack, slow linear decay — curve sits above the pillars and drifts down
        if len(self._nc_curve_peaks) != _ana:
            self._nc_curve_peaks = [0.0] * _ana
            self._nc_curve_hold  = [0.0] * _ana
        _PEAK_DECAY = 0.5 * float(self._spec_peak_decay)
        # Hold time mirrors classic SA: max(2, round(8/reactivity)) frames ÷ target fps
        _HOLD_TIME  = max(2, round(8.0 / max(0.25, float(self._spec_reactivity)))) / max(8, float(self._spec_target_fps))
        for _pi in range(_ana):
            _bv = _bar(_pi)
            if _bv >= self._nc_curve_peaks[_pi]:
                self._nc_curve_peaks[_pi] = _bv
                self._nc_curve_hold[_pi]  = _HOLD_TIME
            else:
                if self._nc_curve_hold[_pi] > 0:
                    self._nc_curve_hold[_pi] = max(0.0, self._nc_curve_hold[_pi] - _dt)
                else:
                    self._nc_curve_peaks[_pi] = max(0.0, self._nc_curve_peaks[_pi] - _PEAK_DECAY * _dt)
        def _peak(i): return self._nc_curve_peaks[min(_ana-1, max(0, i))]

        # Raw points at pillar centers, then Chaikin corner-cutting for rounded transitions
        _raw_pts = [((_bi + 0.5) * _BAR_W, _H - _peak(_bi) * _MAX_PH) for _bi in range(_ana)]
        def _chaikin(pts, iters):
            for _ in range(iters):
                out = [pts[0]]
                for i in range(len(pts) - 1):
                    p0, p1 = pts[i], pts[i + 1]
                    out.append((0.75*p0[0] + 0.25*p1[0], 0.75*p0[1] + 0.25*p1[1]))
                    out.append((0.25*p0[0] + 0.75*p1[0], 0.25*p0[1] + 0.75*p1[1]))
                out.append(pts[-1])
                pts = out
            return pts
        _smooth = _chaikin(_raw_pts, 1 if _is_grad else 2)

        _fill_c = _rgb(0.16, 0.6, 0.5) if _is_grad else _C
        _fill_pts = [cv.Path.MoveTo(0.0, _H)]
        for _x, _y in _smooth:
            _fill_pts.append(cv.Path.LineTo(_x, _y))
        _fill_pts.extend([cv.Path.LineTo(_W, _H), cv.Path.Close()])
        shapes.append(cv.Path(elements=_fill_pts,
            paint=ft.Paint(color=_wo(0.07 + _sv * 0.06, _fill_c), style=ft.PaintingStyle.FILL)))

        _curve_pts = [cv.Path.MoveTo(_smooth[0][0], _smooth[0][1])]
        for _x, _y in _smooth[1:]:
            _curve_pts.append(cv.Path.LineTo(_x, _y))
        if _is_grad:
            _nc_base_a = (0.4 + _sv * 0.6) * _sf
            def _nc_cfn(frac):
                r, g, b = colorsys.hsv_to_rgb(_ghue(frac) % 1.0, 0.9, 1.0)
                return (int(r * 255), int(g * 255), int(b * 255))
            shapes.append(_PilGradPolyline(
                _smooth, _nc_cfn,
                [(8.0, 0.05*_nc_base_a), (3.8, 0.15*_nc_base_a),
                (1.5, 0.55*_nc_base_a), (0.6, 1.00*_nc_base_a)],
                _W))
        else:
            for _gw, _ga in ((8.0, 0.05), (3.8, 0.15), (1.5, 0.55), (0.6, 1.00)):
                shapes.append(cv.Path(elements=_curve_pts,
                    paint=ft.Paint(color=_wo(_ga * (0.4 + _sv * 0.6), _rgb(_hue, 0.7, 1.0)),
                                stroke_width=_gw, style=ft.PaintingStyle.STROKE)))

        # ── Layer 4 — Aurora sweep (drifting sine waves near top) ─────────────
        _aurora_spd = 0.35 + _sv * 1.1
        self._nc_aurora_ph = (self._nc_aurora_ph + _dt * _aurora_spd) % (math.pi * 200.0)
        _aph = self._nc_aurora_ph
        _aurora_base_y = 7.0 + _sv * 4.0  # aurora lives in top ~15px

        for _ai, (_afreq, _aamp, _aoff, _aop) in enumerate([
            (0.048, 5.5, 0.00, 0.38),
            (0.075, 3.5, 1.10, 0.22),
            (0.030, 4.5, 2.20, 0.16),
        ]):
            _ab = (0.12 + _sv * 0.50) * _aop
            if _is_grad:
                _na_g = 8
                _a_xy = []
                for _xi in range(_na_g + 1):
                    _xpos = _xi / float(_na_g) * _W
                    _yoff = math.sin(_aph * _afreq + (_xi / float(_na_g)) * 8.8 + _aoff) * _aamp * (0.35 + _sv * 0.85)
                    _a_xy.append((_xpos, _aurora_base_y + _yoff + _ai * 3.5))
                def _aurora_cfn(frac, _gh=_ghue):
                    r, g, b = colorsys.hsv_to_rgb(_gh(frac) % 1.0, 1.0, 1.0)
                    return (int(r * 255), int(g * 255), int(b * 255))
                shapes.append(_PilGradPolyline(
                    _a_xy, _aurora_cfn,
                    [(9.0, _ab*0.06*_sf), (4.0, _ab*0.22*_sf), (1.4, _ab*0.80*_sf)],
                    _W))
            else:
                _aurora_pts = []
                _na = 40
                for _xi in range(_na + 1):
                    _xpos = _xi / float(_na) * _W
                    _yoff = math.sin(_aph * _afreq + _xi * 0.22 + _aoff) * _aamp * (0.35 + _sv * 0.85)
                    _ypos = _aurora_base_y + _yoff + _ai * 3.5
                    _mv   = cv.Path.MoveTo if _xi == 0 else cv.Path.LineTo
                    _aurora_pts.append(_mv(_xpos, _ypos))
                for _gw, _gm in ((9.0, 0.06), (4.0, 0.22), (1.4, 0.80)):
                    shapes.append(cv.Path(elements=_aurora_pts,
                        paint=ft.Paint(color=_wo(_ab * _gm, _C),
                                    stroke_width=_gw, style=ft.PaintingStyle.STROKE)))

        # ── Layer 5 — Spark fountain (spawned from loud pillar tops, float up) ─
        _MAX_SPARKS = 22
        _SPAWN_TH   = 0.52
        _SPAWN_CD   = 0.10
        _GRAVITY    = 28.0
        _LIFE_OUT   = 0.50
        _LIFE_IN    = 4.5

        self._nc_spawn_cd = max(0.0, self._nc_spawn_cd - _dt)
        if self._nc_spawn_cd <= 0.0 and len(self._nc_sparks) < _MAX_SPARKS and _sv > 0.14:
            _tracked = {s['fi'] for s in self._nc_sparks}
            _best_fi = -1;  _best_val = _SPAWN_TH
            for _fi in range(_ana):
                if _fi not in _tracked and _bar(_fi) > _best_val:
                    _best_val = _bar(_fi);  _best_fi = _fi
            if _best_fi >= 0:
                _bx = (_best_fi + 0.5) * _BAR_W
                _by = _H - _bar(_best_fi) * _MAX_PH
                self._nc_sparks.append({
                    'x':  _bx + random.uniform(-4.0, 4.0),
                    'y':  _by,
                    'vx': random.uniform(-20.0, 20.0),
                    'vy': random.uniform(-52.0, -24.0),
                    'fi': _best_fi,
                    'life': 0.01,
                })
                self._nc_spawn_cd = _SPAWN_CD

        _spd_mul = 0.30 + _sv * 0.85
        _alive   = []
        for _s in self._nc_sparks:
            _s['x']  += _s['vx'] * _dt * _spd_mul
            _s['y']  += _s['vy'] * _dt * _spd_mul
            _s['vy'] += _GRAVITY * _dt
            if _s['x'] < 0:  _s['x'] = 0;  _s['vx'] = abs(_s['vx'])
            if _s['x'] > _W: _s['x'] = _W; _s['vx'] = -abs(_s['vx'])
            if _bar(_s['fi']) >= _SPAWN_TH * 0.65:
                _s['life'] = min(1.0, _s['life'] + _dt * _LIFE_IN)
            else:
                _s['life'] = max(0.0, _s['life'] - _dt * _LIFE_OUT)
            if _s['y'] > _H + 8: _s['life'] = 0.0
            if _s['life'] > 0.0: _alive.append(_s)
        self._nc_sparks = _alive

        for _s in self._nc_sparks:
            _bright = _s['life'] * (0.38 + _sv * 0.45)
            _sr     = 2.2 * _s['life']
            _sc     = _rgb(_ghue(_s['fi'] / max(1, _ana - 1))) if _is_grad else _C
            for _r2, _ra in ((_sr * 4.2, 0.04), (_sr * 2.2, 0.13), (_sr * 1.2, 0.42), (_sr, 0.92)):
                if _r2 < 0.3: continue
                shapes.append(cv.Circle(x=_s['x'], y=_s['y'], radius=_r2,
                    paint=ft.Paint(color=_wo(min(1.0, _ra * _bright), _sc),
                                style=ft.PaintingStyle.FILL)))
            shapes.append(cv.Circle(x=_s['x'], y=_s['y'], radius=max(0.4, _sr * 0.35),
                paint=ft.Paint(color=_wo(min(1.0, 0.55 + _bright * 0.45), _Cw),
                            style=ft.PaintingStyle.FILL)))

        # ── Layer 6 — White bass flash ─────────────────────────────────────────
        _hf = self._nc_hit_flash
        if _hf > 0.01:
            _fe = _hf * _hf  # ease-out
            _cx, _cy = _W / 2.0, _H / 2.0
            _ring_r = 8.0 + (1.0 - _hf) * 72.0
            shapes.append(cv.Circle(x=_cx, y=_cy, radius=_ring_r,
                paint=ft.Paint(color=_wo(_fe * 0.78, _Cw),
                            stroke_width=3.0 + _fe * 3.5, style=ft.PaintingStyle.STROKE)))
            shapes.append(cv.Circle(x=_cx, y=_cy, radius=5.0 + _fe * 22.0,
                paint=ft.Paint(color=_wo(_fe * 0.82, _Cw), style=ft.PaintingStyle.FILL)))
            shapes.append(cv.Oval(x=0.0, y=0.0, width=_W, height=_H,
                paint=ft.Paint(color=_wo(_fe * 0.15, _C), style=ft.PaintingStyle.FILL)))

        try:
            self._neon_vu_canvas.shapes = shapes
            self._neon_vu_canvas.update()
        except Exception:
            pass

    def _render_spectrum_rock_stage(self):
        """Rock Stage: spotlight cones + floor waveform + smoke + pyro bursts + sparks + bass flash."""
        if cv is None or self._neon_vu_canvas is None: return
        _W, _H = 300.0, 62.0
        _now   = time.monotonic()
        _ana   = max(1, len(self._spec_bars))

        # Paired palettes (spot_hue, floor_hue) — loop mode cycles through these on bass hit
        _RS_PAL = [
            (0.60, 0.50),   # royal blue + cyan
            (0.00, 0.08),   # red + orange
            (0.77, 0.85),   # purple + pink
            (0.33, 0.22),   # green + lime
            (0.55, 0.40),   # teal + turquoise
            (0.08, 0.16),   # amber + yellow
            (0.92, 0.00),   # magenta + crimson
        ]

        # ── Lazy-init ─────────────────────────────────────────────────────────
        _N_SPOTS = 6
        if not hasattr(self, '_rsp_spots'):
            _xs = [_W * (i + 0.5) / _N_SPOTS for i in range(_N_SPOTS)]
            self._rsp_spots        = [{'x': _xs[i], 'angle': 0.0, 'target_angle': 0.0,
                                    'band': 0, 'flash': 0.0} for i in range(_N_SPOTS)]
            self._rsp_spot_h_from  = _RS_PAL[0][0]
            self._rsp_spot_h_to    = _RS_PAL[0][0]
            self._rsp_spot_h_t     = 1.0
            self._rsp_flr_h_from   = _RS_PAL[0][1]
            self._rsp_flr_h_to     = _RS_PAL[0][1]
            self._rsp_flr_h_t      = 1.0
            self._rsp_pal_idx      = 0
            self._rsp_hit_flash    = 0.0
            self._rsp_last_t       = _now
            self._rsp_routine      = 'sweep_lr'
            self._rsp_routine_t    = 0.0
            self._rsp_routine_cd   = random.uniform(10.0, 16.0)
            self._rsp_scatter_tgt  = [random.uniform(-0.5, 0.5) for _ in range(_N_SPOTS)]
            self._rsp_roll_offset  = 0.0    # rolling gradient phase (0..1)
            self._rsp_smk_bands    = [
                {'y': 5.0 + _bi2 * 9.0, 'vy': random.uniform(-4.0, 4.0),
                'ph1': random.uniform(0.0, 6.28), 'ph2': random.uniform(0.0, 6.28),
                'pv1': random.uniform(0.18, 0.42), 'pv2': random.uniform(0.10, 0.28)}
                for _bi2 in range(5)
            ]
            self._rsp_sparks       = []
            self._rsp_spark_cd     = 0.0
            self._rsp_spark_cd2    = 0.0    # secondary (moderate-beat) spark cooldown
            self._rsp_pyros        = []
            self._rsp_silence_fade = 1.0    # 1.0 = full, 0.0 = off

        _dt = min(0.08, _now - self._rsp_last_t)
        self._rsp_last_t = _now

        for _i, _sp in enumerate(self._rsp_spots):
            _sp['band'] = int(_i * (_ana - 1) / max(1, _N_SPOTS - 1))

        # ── Audio ─────────────────────────────────────────────────────────────
        _bar = self._bar
        _sb = self._sa_smth_bass
        _sv = self._sa_smth_vu

        # ── Silence fade ───────────────────────────────────────────────────────
        _is_silent = self._sa_mono_vu < 0.015
        if _is_silent:
            self._rsp_silence_fade = max(0.0, self._rsp_silence_fade - _dt * 0.5)
        else:
            self._rsp_silence_fade = min(1.0, self._rsp_silence_fade + _dt * 3.0)
        _sf = self._rsp_silence_fade
        self._current_sf = _sf
        if _sf <= 0.0:
            try: self._neon_vu_canvas.shapes = []; self._neon_vu_canvas.update()
            except: pass
            return

        # ── Color helpers (defined early so palette logic can use them) ────────
        _lerp_h = self._lerp_h; _ease = self._ease
        _rgb = self._rgb; _wo = self._wo

        # Rolling gradient offset — speeds up with volume
        self._rsp_roll_offset = (self._rsp_roll_offset + _dt * (0.10 + _sv * 0.22)) % 1.0
        _ro = self._rsp_roll_offset

        def _grad_hue(frac):
            """Rolling full-wheel gradient: hue shifts position left→right and rolls over time."""
            return (_ro + frac * 0.55) % 1.0

        # ── Bass-hit detection & palette transitions ───────────────────────────
        _new_beat = self._sa_beat_detected
        _cm_rs   = self._tick_random_cm("rock_stage", _new_beat)
        _is_grad  = _cm_rs in ("gradient", "gradient_smoke")
        _is_smoke = _cm_rs in ("loop_smoke", "gradient_smoke")
        if _new_beat:
            if not _is_grad:
                self._rsp_pal_idx     = (self._rsp_pal_idx + 1) % len(_RS_PAL)
                _nh_s, _nh_f          = _RS_PAL[self._rsp_pal_idx]
                self._rsp_spot_h_from = _lerp_h(self._rsp_spot_h_from, self._rsp_spot_h_to, _ease(self._rsp_spot_h_t))
                self._rsp_spot_h_to   = _nh_s
                self._rsp_spot_h_t    = 0.0
                self._rsp_flr_h_from  = _lerp_h(self._rsp_flr_h_from, self._rsp_flr_h_to, _ease(self._rsp_flr_h_t))
                self._rsp_flr_h_to    = _nh_f
                self._rsp_flr_h_t     = 0.0
            self._rsp_hit_flash = 1.0
            if random.random() < 0.40:
                _rts   = ['sweep_lr', 'fan_pulse', 'orbit', 'scatter']
                _other = [r for r in _rts if r != self._rsp_routine]
                self._rsp_routine    = random.choice(_other)
                self._rsp_routine_t  = 0.0
                self._rsp_routine_cd = random.uniform(9.0, 17.0)

        self._rsp_spot_h_t   = min(1.0, self._rsp_spot_h_t  + _dt / 0.55)
        self._rsp_flr_h_t    = min(1.0, self._rsp_flr_h_t   + _dt / 0.55)
        self._rsp_hit_flash  = max(0.0, self._rsp_hit_flash  - _dt * 2.0)

        _spot_hue = _lerp_h(self._rsp_spot_h_from, self._rsp_spot_h_to, _ease(self._rsp_spot_h_t))
        _flr_hue  = _lerp_h(self._rsp_flr_h_from,  self._rsp_flr_h_to,  _ease(self._rsp_flr_h_t))
        self._spec_display_hue = _spot_hue

        _C  = _rgb(_spot_hue if not _is_grad else _grad_hue(0.0))
        _FC = _rgb(_flr_hue  if not _is_grad else _grad_hue(0.5))
        _Cw = "#ffffff"
        _Cd = _rgb(_spot_hue if not _is_grad else _grad_hue(0.25), 0.55, 0.18)

        _MAX_ANG = 0.52
        _FLOOR_Y = 62.0
        _CONE_H  = 0.22

        # ── Routine auto-cycle (frozen while silent) ───────────────────────────
        if not _is_silent:
            self._rsp_routine_t  += _dt
            self._rsp_routine_cd  = max(0.0, self._rsp_routine_cd - _dt)
            if self._rsp_routine_cd <= 0.0:
                _rts   = ['sweep_lr', 'fan_pulse', 'orbit', 'scatter']
                _other = [r for r in _rts if r != self._rsp_routine]
                self._rsp_routine    = random.choice(_other)
                self._rsp_routine_t  = 0.0
                self._rsp_routine_cd = random.uniform(11.0, 19.0)

        # ── Spotlight target angles (frozen while silent) ──────────────────────
        _rt  = self._rsp_routine
        _rph = self._rsp_routine_t

        for _i, _sp in enumerate(self._rsp_spots):
            _fi   = _sp['band']
            _bval = _bar(_fi)
            _norm = (_i / max(1, _N_SPOTS - 1)) * 2.0 - 1.0

            if not _is_silent:
                if _rt == 'sweep_lr':
                    _t_ang = math.sin(_rph * 0.52 + _i * 0.15) * _MAX_ANG
                elif _rt == 'fan_pulse':
                    _pulse = 0.5 + 0.5 * math.sin(_rph * 1.1)
                    _t_ang = _norm * _MAX_ANG * _pulse
                elif _rt == 'orbit':
                    _t_ang = math.sin(_rph * 0.75 + _i * (math.pi / max(1, _N_SPOTS - 1))) * _MAX_ANG
                else:
                    _diff = self._rsp_scatter_tgt[_i] - _sp['angle']
                    if abs(_diff) < 0.06:
                        self._rsp_scatter_tgt[_i] = random.uniform(-_MAX_ANG, _MAX_ANG)
                    _t_ang = self._rsp_scatter_tgt[_i]

                _t_ang += (_bval - 0.5) * (_sv * 0.10)
                _t_ang  = max(-_MAX_ANG, min(_MAX_ANG, _t_ang))
                _sp['target_angle'] = _t_ang
                _sp['angle'] += (_t_ang - _sp['angle']) * min(1.0, 4.5 * _dt)
            else:
                _sp['angle'] += (0.0 - _sp['angle']) * min(1.0, 0.8 * _dt)
            if _new_beat:
                _sp['flash'] = 1.0
            _sp['flash'] = max(0.0, _sp['flash'] - _dt * 2.5)

        shapes = []

        # ── Scrim — dark overlay to keep effects readable over BG image ────────
        if self._spec_nvu_rock_bg != "BLANK":
            shapes.append(cv.Rect(
                x=0.0, y=0.0, width=_W, height=_H,
                paint=ft.Paint(color=ft.Colors.with_opacity(0.45, "#000000"),
                            style=ft.PaintingStyle.FILL)))

        # ── Layer 0 — Ceiling rig haze ─────────────────────────────────────────
        shapes.append(cv.Oval(
            x=-20.0, y=-10.0, width=_W + 40.0, height=28.0,
            paint=ft.Paint(color=_wo(0.10 + _sv * 0.07, _Cd), style=ft.PaintingStyle.FILL)))

        # ── Layer 0.5 — Stage truss bar connecting all mounts ─────────────────
        _truss_b = 0.16 + _sb * 0.28 + self._rsp_hit_flash * 0.12
        for _tw, _ta in ((5.0, 0.05), (2.2, 0.14), (0.8, 0.38)):
            shapes.append(cv.Line(x1=0.0, y1=1.5, x2=_W, y2=1.5,
                paint=ft.Paint(color=_wo(_ta * _truss_b, _C), stroke_width=_tw)))
        for _sp in self._rsp_spots:
            _mc = _rgb(_grad_hue(_sp['x'] / _W)) if _is_grad else _rgb(_spot_hue, 0.7, 1.0)
            for _mr, _ma in ((4.5, 0.06), (2.2, 0.20), (0.9, 0.60)):
                shapes.append(cv.Circle(x=_sp['x'], y=1.5, radius=_mr,
                    paint=ft.Paint(color=_wo(_ma * (0.25 + _sp['flash'] * 0.55),
                                            _Cw if _sp['flash'] > 0.55 else _mc),
                                style=ft.PaintingStyle.FILL)))

        # ── Layer 1 — Spotlight beams ──────────────────────────────────────────
        for _i, _sp in enumerate(self._rsp_spots):
            _sx    = _sp['x']
            _ang   = _sp['angle']
            _fi    = _sp['band']
            _bval  = _bar(_fi)
            _flash = _sp['flash']

            _bright   = 0.20 + _sv * 0.28 + _bval * 0.32 + _flash * 0.38
            _ch       = min(1.38, _CONE_H * (0.65 + _bval * 0.55 + _flash * 0.50))
            _cx_floor = _sx + _FLOOR_Y * math.sin(_ang)

            if _is_grad:
                _sc = _rgb(_grad_hue(_i / max(1, _N_SPOTS - 1)))
            else:
                _sc = _rgb((_spot_hue + (_i - (_N_SPOTS - 1) / 2.0) * 0.022) % 1.0,
                        1.0 - _flash * 0.5, 1.0)

            for _pw_f, _pa in ((2.8, 0.022 + _sv * 0.018),
                            (1.6, 0.055 + _sv * 0.038),
                            (1.0, 0.16  + _bval * 0.18),
                            (0.32, 0.50 + _bval * 0.32)):
                _hw = _FLOOR_Y * math.tan(min(1.38, _ch * _pw_f))
                _beam_pts = [cv.Path.MoveTo(_sx, 0.0),
                            cv.Path.LineTo(max(-35.0, _cx_floor - _hw), _FLOOR_Y),
                            cv.Path.LineTo(min(_W + 35.0, _cx_floor + _hw), _FLOOR_Y),
                            cv.Path.Close()]
                shapes.append(cv.Path(elements=_beam_pts,
                    paint=ft.Paint(color=_wo(_pa * _bright, _Cw if _flash > 0.75 else _sc),
                                style=ft.PaintingStyle.FILL)))

            # Spotlight head glow (rendered on top of truss mounts)
            _hr0 = 3.0 + _flash * 3.0 + _sv * 1.2
            shapes.append(cv.Circle(x=_sx, y=1.5, radius=_hr0,
                paint=ft.Paint(color=_wo(0.90 * (0.35 + _bright * 0.55),
                                        _Cw if _flash > 0.45 else _sc),
                            style=ft.PaintingStyle.FILL)))

            # Floor pool — uses floor color (loop) or rolling gradient position
            _hw_floor = _FLOOR_Y * math.tan(min(1.38, _ch))
            _pool_w   = max(2.5, _hw_floor * 1.5)
            _pc       = _rgb(_grad_hue(_cx_floor / _W)) if _is_grad else _rgb(_flr_hue, 1.0 - _flash * 0.4, 1.0)
            for _pw2, _pa2 in ((_pool_w,        0.05 + _bval * 0.18 + _flash * 0.18),
                                (_pool_w * 0.45, 0.20 + _bval * 0.42 + _flash * 0.30)):
                shapes.append(cv.Oval(x=_cx_floor - _pw2, y=_FLOOR_Y - 3.5,
                    width=_pw2 * 2.0, height=7.0,
                    paint=ft.Paint(color=_wo(_pa2 * _bright, _pc), style=ft.PaintingStyle.FILL)))

        # ── Layer 2 — Stage floor line (floor color) ───────────────────────────
        _flb = 0.24 + _sv * 0.34
        for _fw, _fa in ((6.5, 0.04), (3.0, 0.13), (1.0, 0.52)):
            shapes.append(cv.Line(x1=0.0, y1=_FLOOR_Y, x2=_W, y2=_FLOOR_Y,
                paint=ft.Paint(color=_wo(_fa * _flb, _FC), stroke_width=_fw)))

        # ── Layer 3 — Frequency waveform (X=freq, Y=amp rising from floor) ─────
        _WF_MAX = 14.0 + _sv * 26.0
        _wf_pts = []
        for _xi in range(_ana + 1):
            _xf   = _xi / float(_ana) * _W
            _fi_f = _xi / float(_ana) * max(1, _ana - 1)
            _flo  = int(_fi_f);  _fhi = min(_ana - 1, _flo + 1)
            _bv   = _bar(_flo) * (1.0 - (_fi_f - _flo)) + _bar(_fhi) * (_fi_f - _flo)
            _wf_pts.append((_xf, _FLOOR_Y - _bv * _WF_MAX))
        def _chaikin(pts, iters):
            for _ in range(iters):
                out = [pts[0]]
                for i in range(len(pts) - 1):
                    p0, p1 = pts[i], pts[i + 1]
                    out.append((0.75*p0[0] + 0.25*p1[0], 0.75*p0[1] + 0.25*p1[1]))
                    out.append((0.25*p0[0] + 0.75*p1[0], 0.25*p0[1] + 0.75*p1[1]))
                out.append(pts[-1])
                pts = out
            return pts
        _wf_pts = _chaikin(_wf_pts, 1 if _is_grad else 2)

        _fill_e = [cv.Path.MoveTo(0.0, _FLOOR_Y)]
        for _xp, _yp in _wf_pts:
            _fill_e.append(cv.Path.LineTo(_xp, _yp))
        _fill_e.extend([cv.Path.LineTo(_W, _FLOOR_Y), cv.Path.Close()])
        shapes.append(cv.Path(elements=_fill_e,
            paint=ft.Paint(color=_wo(0.13 + _sv * 0.10, _FC), style=ft.PaintingStyle.FILL)))

        _wf_line = [cv.Path.MoveTo(_wf_pts[0][0], _wf_pts[0][1])]
        for _xp, _yp in _wf_pts[1:]:
            _wf_line.append(cv.Path.LineTo(_xp, _yp))
        if _is_grad:
            _rs_base_a = (0.30 + _sv * 0.58) * _sf
            def _rs_cfn(frac, _gh=_grad_hue):
                r, g, b = colorsys.hsv_to_rgb(_gh(frac) % 1.0, 1.0, 1.0)
                return (int(r * 255), int(g * 255), int(b * 255))
            shapes.append(_PilGradPolyline(
                _wf_pts, _rs_cfn,
                [(6.0, 0.04*_rs_base_a), (2.8, 0.14*_rs_base_a),
                (1.1, 0.50*_rs_base_a), (0.4, 1.00*_rs_base_a)],
                _W))
        else:
            for _gw, _ga in ((7.0, 0.04), (3.5, 0.13), (1.4, 0.48), (0.5, 0.98)):
                shapes.append(cv.Path(elements=_wf_line,
                    paint=ft.Paint(color=_wo(_ga * (0.30 + _sv * 0.58), _FC),
                                stroke_width=_gw, style=ft.PaintingStyle.STROKE)))

        # Color, band value, cone width, and ct base are all constant per spot per frame
        _spot_rgb = []; _spot_ch = []; _spot_ctb = []
        for _spi0, _spt0 in enumerate(self._rsp_spots):
            _sh0 = _grad_hue(_spt0['x'] / _W) if _is_grad else \
                (_spot_hue + (_spi0 - (_N_SPOTS - 1) / 2.0) * 0.022) % 1.0
            _spot_rgb.append(colorsys.hsv_to_rgb(_sh0 % 1.0, 0.75, 1.0))
            _bv0 = _bar(_spt0['band'])
            _spot_ch.append(min(1.38, _CONE_H * (0.65 + _bv0 * 0.55 + _spt0['flash'] * 0.50)))
            _spot_ctb.append(0.22 + _bv0 * 0.52 + _spt0['flash'] * 0.35)

        # ── Layer 4 — Smoke wisps (only in smoke modes) ───────────────────────
        _na_smk = 12
        if _is_smoke and _sf > 0.02:
            for _b in self._rsp_smk_bands:
                _b['ph1']  = (_b['ph1'] + _b['pv1'] * _dt * (0.7 + _sv * 0.7)) % (math.pi * 200)
                _b['ph2']  = (_b['ph2'] + _b['pv2'] * _dt * (0.5 + _sv * 0.5)) % (math.pi * 200)
                _b['y']   += _b['vy'] * _dt * (0.5 + _sv * 0.8)
                if _b['y'] < 5.0:   _b['y'] = 5.0;   _b['vy'] =  abs(_b['vy'])
                if _b['y'] > 47.0:  _b['y'] = 47.0;  _b['vy'] = -abs(_b['vy'])
                if random.random() < 0.006: _b['vy'] = random.uniform(-5.0, 5.0)

                _amp  = 2.0 + _sv * 3.5
                _els  = []
                for _xi in range(_na_smk + 1):
                    _xp  = _xi / float(_na_smk) * _W
                    _yp  = _b['y'] + (math.sin(_b['ph1'] * 0.042 + _xi * 0.26) * _amp +
                                    math.sin(_b['ph2'] * 0.027 + _xi * 0.15) * _amp * 0.40)
                    _els.append(cv.Path.MoveTo(_xp, _yp) if _xi == 0 else cv.Path.LineTo(_xp, _yp))
                _alph = 0.22 + _sv * 0.10
                for _gw, _ga in ((22.0, 0.10), (4.0, 0.45)):
                    shapes.append(cv.Path(elements=_els,
                        paint=ft.Paint(color=_wo(_alph * _ga, "#90a8c4"),
                                    stroke_width=_gw, style=ft.PaintingStyle.STROKE)))

        # ── Layer 5 — Sparks: big burst on beat + threshold burst at bar x ───────
        _MAX_SPARKS  = 36
        _SPARK_THRESH = 0.50
        self._rsp_spark_cd = max(0.0, self._rsp_spark_cd - _dt)

        if _new_beat and len(self._rsp_sparks) < _MAX_SPARKS:
            _sp_b = random.choice(self._rsp_spots)
            _cx_b = _sp_b['x'] + _FLOOR_Y * math.sin(_sp_b['angle'])
            for _ in range(random.randint(10, 16)):
                _ab  = random.uniform(0.0, 2.0 * math.pi)
                _spb = random.uniform(45.0, 110.0)
                self._rsp_sparks.append({
                    'x': _cx_b + random.uniform(-8.0, 8.0), 'y': _FLOOR_Y - 1.5,
                    'vx': math.cos(_ab) * _spb,
                    'vy': -abs(math.sin(_ab)) * _spb * random.uniform(0.8, 1.3),
                    'life': 0.01,
                })

        if self._rsp_spark_cd <= 0.0 and len(self._rsp_sparks) < _MAX_SPARKS:
            _best_i, _best_v = -1, _SPARK_THRESH
            for _bi in range(_ana):
                _bv = _bar(_bi)
                if _bv > _best_v:
                    _best_v, _best_i = _bv, _bi
            if _best_i >= 0:
                _bx = (_best_i / max(1, _ana - 1)) * _W
                for _ in range(random.randint(2, 4)):
                    _ang3 = random.uniform(0.0, 2.0 * math.pi)
                    _spd3 = random.uniform(25.0, 70.0)
                    self._rsp_sparks.append({
                        'x': _bx + random.uniform(-4.0, 4.0), 'y': _FLOOR_Y - 1.5,
                        'vx': math.cos(_ang3) * _spd3,
                        'vy': -abs(math.sin(_ang3)) * _spd3 * random.uniform(0.7, 1.2),
                        'life': 0.01,
                    })
                self._rsp_spark_cd = 0.60

        _GRAVITY = 60.0
        _spark_alive = []
        for _sk in self._rsp_sparks:
            _sk['x']  += _sk['vx'] * _dt
            _sk['y']  += _sk['vy'] * _dt
            _sk['vy'] += _GRAVITY * _dt
            if _sk['x'] < 0.0:  _sk['x'] = 0.0;  _sk['vx'] = abs(_sk['vx'])
            if _sk['x'] > _W:   _sk['x'] = _W;   _sk['vx'] = -abs(_sk['vx'])
            _sk['life'] = min(1.0, _sk['life'] + _dt * 4.5) if _sk['y'] <= _FLOOR_Y + 2 \
                        else max(0.0, _sk['life'] - _dt * 3.0)
            if _sk['y'] > _H + 5:  _sk['life'] = 0.0
            if _sk['life'] > 0.0:  _spark_alive.append(_sk)
        self._rsp_sparks = _spark_alive

        for _sk in self._rsp_sparks:
            _bright2 = _sk['life'] * (0.38 + _sv * 0.42)
            _sr3     = 1.9 * _sk['life']
            _skc     = _rgb(_grad_hue(_sk['x'] / _W)) if _is_grad else _rgb(_spot_hue, 0.9, 1.0)
            for _r2, _ra in ((_sr3 * 3.8, 0.04), (_sr3 * 2.0, 0.14), (_sr3, 0.52)):
                if _r2 < 0.3: continue
                shapes.append(cv.Circle(x=_sk['x'], y=_sk['y'], radius=_r2,
                    paint=ft.Paint(color=_wo(min(1.0, _ra * _bright2), _skc),
                                style=ft.PaintingStyle.FILL)))
            shapes.append(cv.Circle(x=_sk['x'], y=_sk['y'], radius=max(0.4, _sr3 * 0.38),
                paint=ft.Paint(color=_wo(min(1.0, 0.58 + _bright2 * 0.42), _Cw),
                            style=ft.PaintingStyle.FILL)))

        # ── Layer 6 — White bass flash ─────────────────────────────────────────
        _hf = self._rsp_hit_flash
        if _hf > 0.01:
            _fe = _hf * _hf
            shapes.append(cv.Circle(x=_W / 2.0, y=_H / 2.0, radius=8.0 + (1.0 - _hf) * 68.0,
                paint=ft.Paint(color=_wo(_fe * 0.70, _Cw),
                            stroke_width=3.0 + _fe * 4.0, style=ft.PaintingStyle.STROKE)))
            shapes.append(cv.Circle(x=_W / 2.0, y=_H / 2.0, radius=5.0 + _fe * 18.0,
                paint=ft.Paint(color=_wo(_fe * 0.78, _Cw), style=ft.PaintingStyle.FILL)))
            shapes.append(cv.Oval(x=0.0, y=0.0, width=_W, height=_H,
                paint=ft.Paint(color=_wo(_fe * 0.13, _C), style=ft.PaintingStyle.FILL)))

        try:
            self._neon_vu_canvas.shapes = shapes
            self._neon_vu_canvas.update()
        except Exception:
            pass

    def _render_spectrum_vu(self):
        _bg     = "#101010"
        _bands  = max(1, self._spec_bands)
        _me     = max(1, _bands - 3)
        _mw     = max(1, _me)
        _l_fill = int(round(max(0.0, min(1.0, self._spec_vu_left))       * _mw))
        _r_fill = int(round(max(0.0, min(1.0, self._spec_vu_right))      * _mw))
        _l_peak = int(round(max(0.0, min(1.0, self._spec_vu_peak_left))  * _mw))
        _r_peak = int(round(max(0.0, min(1.0, self._spec_vu_peak_right)) * _mw))
        _top    = list(range(2, min(self._spec_levels, 7)))
        _bot    = list(range(max(0, self._spec_levels - 7), self._spec_levels - 2))
        _tp     = _top[:5] if len(_top) >= 5 else _top
        _bp     = _bot[-5:] if len(_bot) >= 5 else _bot
        for bi, segs in enumerate(self._spec_segments):
            for seg in segs: seg.bgcolor = _bg
            if bi < _me:
                _x     = bi
                _cidx  = int((_x / max(1, _mw - 1)) * (len(self._spec_palette) - 1))
                _color = self._spec_palette[min(_cidx, len(self._spec_palette) - 1)]
                if _x < _l_fill:
                    for _r in _top: segs[_r].bgcolor = _color
                if _x < _r_fill:
                    for _r in _bot: segs[_r].bgcolor = _color
                if _x == _l_peak and _l_peak > 0:
                    for _r in _tp:
                        if 0 <= _r < self._spec_levels: segs[_r].bgcolor = "#ff2020"
                if _x == _r_peak and _r_peak > 0:
                    for _r in _bp:
                        if 0 <= _r < self._spec_levels: segs[_r].bgcolor = "#ff2020"
            else:
                _ls  = max(0, _bands - 3)
                _gx  = bi - _ls
                _lr  = ["100","100","100","100","111"]
                _rr  = ["110","101","110","101","101"]
                _lr0 = 1
                _rr0 = max(0, self._spec_levels - 6)
                if 0 <= _gx < 3:
                    for _ry in range(5):
                        _row = _lr0 + _ry
                        if 0 <= _row < self._spec_levels and _lr[_ry][_gx] == "1":
                            segs[_row].bgcolor = "#8a8a8a"
                    for _ry in range(5):
                        _row = _rr0 + _ry
                        if 0 <= _row < self._spec_levels and _rr[_ry][_gx] == "1":
                            segs[_row].bgcolor = "#8a8a8a"

    # ── Neon VU canvas renders ────────────────────────────────────────────────

    def _render_spectrum_neon_vu(self):
        if cv is None or self._neon_vu_canvas is None: return
        _theme = self._neon_vu_theme
        if _theme == "retro_tech":
            _col_l = _col_r = "#FF7700"; _arc_col = "#E0E0E0"
        elif _theme == "custom_vu":
            _col_l = _col_r = "#000000"; _arc_col = "transparent"
        else:
            _col_l = _col_r = "#00FFFF"; _arc_col = "#6600FF"

        _ATT, _REL = 0.30, 0.70
        _raw_l = max(0.0, min(1.0, float(self._spec_vu_left  or 0.0)))
        _raw_r = max(0.0, min(1.0, float(self._spec_vu_right or 0.0)))
        self._neon_vu_left_smooth  = _raw_l * _ATT + self._neon_vu_left_smooth  * _REL
        self._neon_vu_right_smooth = _raw_r * _ATT + self._neon_vu_right_smooth * _REL

        _CX_L = 75; _CX_R = 225; _CY = 86; _R = 76
        _ANG_START = 210.0; _ANG_END = 330.0; _ANG_SPAN = 120.0

        def _ang(val): return _ANG_START + max(0.0, min(1.0, float(val))) * _ANG_SPAN
        def _pt(cx, r, a):
            rad = math.radians(a)
            return cx + r * math.cos(rad), _CY + r * math.sin(rad)

        shapes = []
        _is_retro  = (_theme == "retro_tech")
        _is_custom = (_theme == "custom_vu")

        if not _is_retro and not _is_custom:
            for _cx in (_CX_L, _CX_R):
                for _ro in [22, 45, 68]:
                    shapes.append(cv.Circle(x=float(_cx), y=float(_CY), radius=float(_ro),
                        paint=ft.Paint(color=ft.Colors.with_opacity(0.12, "#00FFFF"),
                                    stroke_width=0.8, style=ft.PaintingStyle.STROKE)))

        if _is_retro:
            _num_labels = [(-20, 0.0), (-10, 0.25), (-5, 0.5), (0, 0.75), ("+3", 1.0)]
            for _cx, _sl in [(_CX_L, "L"), (_CX_R, "R")]:
                shapes.append(cv.Text(x=_cx, y=_CY - 42, value=_sl,
                    style=ft.TextStyle(size=10, weight=ft.FontWeight.BOLD, color="white60"),
                    alignment=ft.Alignment.CENTER))
                for _txt, _v in _num_labels:
                    _lx, _ly = _pt(_cx, _R + 1, _ang(_v))
                    shapes.append(cv.Text(x=_lx, y=_ly, value=str(_txt),
                        style=ft.TextStyle(size=6.5, color="white38"),
                        alignment=ft.Alignment.CENTER))
        elif not _is_custom:
            _num_labels = [("-20", 0.0), ("-10", 0.25), ("-5", 0.5), ("0", 0.75), ("+3", 1.0)]
            for _cx, _sl in [(_CX_L, "L-CH"), (_CX_R, "R-CH")]:
                shapes.append(cv.Text(x=_cx, y=_CY - 44, value=_sl,
                    style=ft.TextStyle(size=9, weight=ft.FontWeight.BOLD,
                                    color="#00FFFF", italic=True),
                    alignment=ft.Alignment.CENTER))
                for _txt, _v in _num_labels:
                    _lx, _ly = _pt(_cx, _R + 1, _ang(_v))
                    shapes.append(cv.Text(x=_lx, y=_ly, value=str(_txt),
                        style=ft.TextStyle(size=6.2, color="#FF00FF",
                                        weight=ft.FontWeight.W_600),
                        alignment=ft.Alignment.CENTER))

        if not _is_custom:
            for _cx in (_CX_L, _CX_R):
                if _is_retro:
                    shapes.append(cv.Circle(x=_cx, y=_CY, radius=_R - 5,
                        paint=ft.Paint(color="white10", stroke_width=1,
                                    style=ft.PaintingStyle.STROKE)))
                    continue
                _pts_base = []
                for _a in range(int(_ANG_START), int(_ANG_END) + 1, 5):
                    px, py = _pt(_cx, _R - 5, _a)
                    if _pts_base: _pts_base.append(cv.Path.LineTo(px, py))
                    else:         _pts_base.append(cv.Path.MoveTo(px, py))
                shapes.append(cv.Path(elements=_pts_base,
                    paint=ft.Paint(color=ft.Colors.with_opacity(0.35, _arc_col),
                                stroke_width=5, style=ft.PaintingStyle.STROKE)))
                _ang_zero = _ang(0.75)
                _pts_c = []
                for _a in range(int(_ANG_START), int(_ang_zero) + 1, 2):
                    px, py = _pt(_cx, _R - 5, _a)
                    if _pts_c: _pts_c.append(cv.Path.LineTo(px, py))
                    else:      _pts_c.append(cv.Path.MoveTo(px, py))
                if _pts_c:
                    shapes.append(cv.Path(elements=_pts_c,
                        paint=ft.Paint(color=ft.Colors.with_opacity(0.85, "#00FFFF"),
                                    stroke_width=1.2, style=ft.PaintingStyle.STROKE)))
                _pts_m = []
                for _a in range(int(_ang_zero), int(_ANG_END) + 1, 2):
                    px, py = _pt(_cx, _R - 5, _a)
                    if _pts_m: _pts_m.append(cv.Path.LineTo(px, py))
                    else:      _pts_m.append(cv.Path.MoveTo(px, py))
                if _pts_m:
                    shapes.append(cv.Path(elements=_pts_m,
                        paint=ft.Paint(color=ft.Colors.with_opacity(0.85, "#FF00FF"),
                                    stroke_width=1.2, style=ft.PaintingStyle.STROKE)))

        if not _is_custom:
            for _cx in (_CX_L, _CX_R):
                _tc = 41 if _is_retro else 13
                for _i in range(_tc):
                    _v = _i / float(_tc - 1)
                    _a = _ang(_v)
                    if _is_retro:
                        _major = (_i % 10 == 0); _tlen = 7 if _major else 4
                        _tcol  = "#00CC44" if _v < 0.65 else ("#FFCC00" if _v < 0.85 else "#FF2222")
                        _topa  = 0.8 if _major else 0.4
                    else:
                        _major = (_i % 3 == 0); _tlen = 6 if _major else 4
                        _tcol  = "#00FFFF" if _v < 0.75 else "#FF00FF"
                        _topa  = 0.8 if _major else 0.35
                    _ix, _iy = _pt(_cx, _R - 5 - _tlen, _a)
                    _ox, _oy = _pt(_cx, _R - 5, _a)
                    shapes.append(cv.Line(x1=_ix, y1=_iy, x2=_ox, y2=_oy,
                        paint=ft.Paint(color=ft.Colors.with_opacity(_topa, _tcol),
                                    stroke_width=1.8 if _major else 1.0)))

        if not _is_retro and not _is_custom:
            for _cx in (_CX_L, _CX_R):
                for _v0, _v1, _zcol, _zopa in [(0.00, 0.75, "#00FFFF", 0.30), (0.75, 1.00, "#FF00FF", 0.40)]:
                    _zpts = []
                    for _a in range(int(_ang(_v0)), int(_ang(_v1)) + 1, 2):
                        px, py = _pt(_cx, _R - 5, _a)
                        if _zpts: _zpts.append(cv.Path.LineTo(px, py))
                        else:     _zpts.append(cv.Path.MoveTo(px, py))
                    if _zpts:
                        shapes.append(cv.Path(elements=_zpts,
                            paint=ft.Paint(color=ft.Colors.with_opacity(_zopa, _zcol),
                                        stroke_width=4, style=ft.PaintingStyle.STROKE)))

        for _cx, _val, _col in ((_CX_L, self._neon_vu_left_smooth, _col_l),
                                (_CX_R, self._neon_vu_right_smooth, _col_r)):
            _tip_x, _tip_y = _pt(_cx, _R - 8, _ang(_val))
            shapes.append(cv.Line(x1=float(_cx), y1=float(_CY),
                                x2=_tip_x, y2=_tip_y,
                                paint=ft.Paint(color=_col, stroke_width=1.25)))

        for _cx, _val, _col in ((_CX_L, self._neon_vu_left_smooth, _col_l),
                                (_CX_R, self._neon_vu_right_smooth, _col_r)):
            shapes.append(cv.Circle(x=float(_cx), y=float(_CY), radius=2.5,
                paint=ft.Paint(color=_col, style=ft.PaintingStyle.FILL)))

        try:
            self._neon_vu_canvas.shapes = shapes
            self._neon_vu_canvas.update()
        except Exception:
            pass

    def _render_spectrum_hud_reactor(self):
        if cv is None or self._neon_vu_canvas is None: return
        _W, _H   = 300.0, 62.0
        _cx, _cy = 150.0, 31.0
        _N  = 12; _XS = 11.6; _YS = 2.35
        _CYN = "#00EEFF"; _WHITE = "#FFFFFF"
        _lL  = max(0.0, min(1.0, float(self._spec_vu_left  or 0.0)))
        _rL  = max(0.0, min(1.0, float(self._spec_vu_right or 0.0)))

        def _bracket_pts(sx, ty, by, cap_dir, cap_w, bev):
            return [cv.Path.MoveTo(sx + cap_dir * cap_w, ty),
                    cv.Path.LineTo(sx + cap_dir * bev,   ty),
                    cv.Path.LineTo(sx,                   ty + bev),
                    cv.Path.LineTo(sx,                   by - bev),
                    cv.Path.LineTo(sx + cap_dir * bev,   by),
                    cv.Path.LineTo(sx + cap_dir * cap_w, by)]

        shapes = []
        _avg   = (_lL + _rL) * 0.5
        _ch_w  = 4.5 + _avg * 4.5; _ch_h = 10.0 + _avg * 20.0
        _core_a= min(1.0, 0.25 + _avg * 1.1)

        shapes.append(cv.Path(elements=[
                cv.Path.MoveTo(_cx, _cy - _ch_h), cv.Path.LineTo(_cx + _ch_w, _cy),
                cv.Path.LineTo(_cx, _cy + _ch_h), cv.Path.LineTo(_cx - _ch_w, _cy),
                cv.Path.Close()],
            paint=ft.Paint(color=ft.Colors.with_opacity(_core_a * 0.65, _CYN),
                        stroke_width=1.2 + _avg * 1.5, style=ft.PaintingStyle.STROKE)))

        _pillar_h = _ch_h * 0.72
        for _pw, _pa in ((12, 0.12), (6, 0.25)):
            shapes.append(cv.Line(x1=_cx, y1=_cy - _pillar_h, x2=_cx, y2=_cy + _pillar_h,
                paint=ft.Paint(color=ft.Colors.with_opacity(_pa * _core_a, _CYN), stroke_width=_pw)))
        shapes.append(cv.Line(x1=_cx, y1=_cy - _pillar_h, x2=_cx, y2=_cy + _pillar_h,
            paint=ft.Paint(color=ft.Colors.with_opacity(_core_a, _CYN), stroke_width=1.8)))

        for _y_off in (-5, 5):
            _tw = 6.5 + _avg * 6.5
            shapes.append(cv.Line(x1=_cx - _tw, y1=_cy + _y_off, x2=_cx + _tw, y2=_cy + _y_off,
                paint=ft.Paint(color=ft.Colors.with_opacity(_core_a * 0.5, _CYN), stroke_width=1.1)))

        shapes.append(cv.Circle(x=_cx, y=_cy, radius=1.4 + _avg * 1.5,
            paint=ft.Paint(color=ft.Colors.with_opacity(min(1.0, 0.6 + _avg * 0.4), _WHITE),
                        style=ft.PaintingStyle.FILL)))

        for _i in range(1, _N + 1):
            _ah = _i * _YS; _sx_l = _cx - _i * _XS; _sx_r = _cx + _i * _XS
            _ty = _cy - _ah; _by   = _cy + _ah
            _cap_w = 3.5 + _i * 1.1
            _bev   = min(1.8 + _i * 0.4, _ah * 0.45, _cap_w * 0.75)
            _thresh = (_i - 0.85) / _N
            for _is_right, _sx, _lvl in ((False, _sx_l, _lL), (True, _sx_r, _rL)):
                _lit     = _lvl >= _thresh
                _cap_dir = -1 if _is_right else +1
                _pts     = _bracket_pts(_sx, _ty, _by, _cap_dir, _cap_w, _bev)
                if not _lit:
                    shapes.append(cv.Path(elements=_pts,
                        paint=ft.Paint(color=ft.Colors.with_opacity(0.07, _CYN),
                                    stroke_width=0.8, style=ft.PaintingStyle.STROKE)))
                    shapes.append(cv.Line(x1=_sx + _cap_dir * 3.8, y1=_ty + _bev,
                                        x2=_sx + _cap_dir * 3.8, y2=_by - _bev,
                        paint=ft.Paint(color=ft.Colors.with_opacity(0.04, _CYN), stroke_width=0.5)))
                    continue
                _gm = 0.3 + _lvl * 1.7
                for _gw, _ga in ((13, 0.05), (8, 0.13), (3.5, 0.24)):
                    shapes.append(cv.Path(elements=_pts,
                        paint=ft.Paint(color=ft.Colors.with_opacity(min(0.95, _ga * _gm), _CYN),
                                    stroke_width=_gw, style=ft.PaintingStyle.STROKE)))
                shapes.append(cv.Path(elements=_pts,
                    paint=ft.Paint(color=ft.Colors.with_opacity(min(1.0, 0.7 + _lvl * 0.3), _CYN),
                                stroke_width=1.3, style=ft.PaintingStyle.STROKE)))
                _sp = _cap_dir * 3.8
                shapes.append(cv.Line(x1=_sx + _sp, y1=_ty + _bev, x2=_sx + _sp, y2=_by - _bev,
                    paint=ft.Paint(color=ft.Colors.with_opacity(0.28, _CYN), stroke_width=0.5)))
                for _ec_y in (_ty + 2.8, _by - 2.8):
                    shapes.append(cv.Line(x1=_sx + _cap_dir * _cap_w, y1=_ec_y,
                                        x2=_sx + _cap_dir * (_bev + 2.0), y2=_ec_y,
                        paint=ft.Paint(color=ft.Colors.with_opacity(0.20, _CYN), stroke_width=0.5)))
                _tx = _sx + _cap_dir * _cap_w
                for _tk_y in (_ty, _by):
                    shapes.append(cv.Line(x1=_tx, y1=_tk_y - 2.5, x2=_tx, y2=_tk_y + 2.5,
                        paint=ft.Paint(color=ft.Colors.with_opacity(0.65, _CYN), stroke_width=0.8)))
                _bmx = _sx + _cap_dir * _bev * 0.5
                for _dy in (_ty + _bev * 0.5, _by - _bev * 0.5):
                    shapes.append(cv.Circle(x=_bmx, y=_dy, radius=1.2,
                        paint=ft.Paint(color=ft.Colors.with_opacity(0.85, _WHITE),
                                    style=ft.PaintingStyle.FILL)))
                if _i == _N:
                    for _ny in (_ty + _bev, _by - _bev):
                        shapes.append(cv.Line(x1=_sx, y1=_ny,
                                            x2=_sx - _cap_dir * 5, y2=_ny,
                            paint=ft.Paint(color=ft.Colors.with_opacity(0.38, _CYN), stroke_width=0.8)))

        try:
            self._neon_vu_canvas.shapes = shapes
            self._neon_vu_canvas.update()
        except Exception:
            pass

    # ── Idle render effects ───────────────────────────────────────────────────

    def _build_spec_text_columns(self, text):
        _font = {
            " ":["00000"]*7,
            "A":["01110","10001","10001","11111","10001","10001","10001"],
            "C":["01110","10001","10000","10000","10000","10001","01110"],
            "E":["11111","10000","10000","11110","10000","10000","11111"],
            "L":["10000","10000","10000","10000","10000","10000","11111"],
            "M":["10001","11011","10101","10101","10001","10001","10001"],
            "N":["10001","11001","10101","10011","10001","10001","10001"],
            "P":["11110","10001","10001","11110","10000","10000","10000"],
            "R":["11110","10001","10001","11110","10100","10010","10001"],
            "S":["01111","10000","10000","01110","00001","00001","11110"],
            "T":["11111","00100","00100","00100","00100","00100","00100"],
            "U":["10001","10001","10001","10001","10001","10001","01110"],
            "Y":["10001","10001","01010","00100","00100","00100","00100"],
            "Z":["11111","00001","00010","00100","01000","10000","11111"],
            "D":["11100","10010","10001","10001","10001","10010","11100"],
            "F":["11111","10000","10000","11110","10000","10000","10000"],
            "G":["01110","10001","10000","10111","10001","10001","01110"],
            "H":["10001","10001","10001","11111","10001","10001","10001"],
            "I":["11111","00100","00100","00100","00100","00100","11111"],
            "O":["01110","10001","10001","10001","10001","10001","01110"],
            "W":["10001","10001","10001","10101","10101","11011","10001"],
            "X":["10001","10001","01010","00100","01010","10001","10001"],
            "+":["00000","00100","00100","11111","00100","00100","00000"],
            ".":["00000","00000","00000","00000","00000","00110","00110"],
        }
        _rows = [""] * 7
        for _ch in str(text).upper():
            _g = _font.get(_ch, _font[" "])
            for _r in range(7): _rows[_r] += _g[_r] + "0"
        _cols = []
        for _x in range(len(_rows[0]) if _rows and _rows[0] else 0):
            _cols.append([(_rows[_y][_x] == "1") for _y in range(7)])
        return _cols

    def _render_spectrum_idle_text(self):
        if not self._spec_segments: return
        _cols = self._build_spec_text_columns(self._spec_idle_text)
        if not _cols: return
        _spd = max(0.25, min(3.0, float(self._spec_idle_speed)))
        _old = self._spec_idle_scroll
        self._spec_idle_phase += 0.18 * _spd
        while self._spec_idle_phase >= 1.0:
            self._spec_idle_phase  -= 1.0
            self._spec_idle_scroll  = (self._spec_idle_scroll + 1) % len(_cols)
        if self._spec_idle_scroll < _old:
            self._spec_idle_cycle_done = True
        _y_off = max(0, (self._spec_levels - 7) // 2)
        _bg    = "#101010"
        for bi, segs in enumerate(self._spec_segments):
            _cx    = (bi + self._spec_idle_scroll) % len(_cols)
            _bits  = _cols[_cx]
            _color = self._spec_palette[(bi + int(self._spec_idle_scroll / 2)) % len(self._spec_palette)]
            for top_idx, seg in enumerate(segs):
                _y = top_idx - _y_off
                seg.bgcolor = _color if (0 <= _y < 7 and _bits[_y]) else _bg
        try: self._spectrum_box.update()
        except: pass

    def _render_spectrum_idle_pulse(self):
        if not self._spec_segments: return
        _bg    = "#101010"
        _bands = max(1, self._spec_bands); _levels = max(1, self._spec_levels)
        _spd   = max(0.25, min(3.0, float(self._spec_idle_speed)))
        _old_p = self._spec_idle_phase
        self._spec_idle_phase += 0.11 * _spd
        if self._spec_idle_phase >= 1000.0: self._spec_idle_phase = 0.0
        _p  = self._spec_idle_phase
        _cx = (_bands - 1) / 2.0; _cy = (_levels - 1) / 2.0
        _md = ((_cx**2 + _cy**2)**0.5) + 2.0
        _sg = max(2.0, _md * 0.65)
        _cy2= _md + _sg
        _r1 = (_p * 0.9) % _cy2
        _r2 = (_r1 - _sg) % _cy2
        if (_p * 0.9 % _cy2) < (_old_p * 0.9 % _cy2):
            self._spec_idle_cycle_done = True
        for bi, segs in enumerate(self._spec_segments):
            for top_idx, seg in enumerate(segs):
                _dx = bi - _cx; _dy = top_idx - _cy
                _d  = (_dx**2 + _dy**2)**0.5
                _best = 999.0
                for _r in (_r1, _r2):
                    if _r <= _md + 0.6: _best = min(_best, abs(_d - _r))
                if _best < 0.55:
                    seg.bgcolor = self._spec_palette[(bi + int(_p * 9.0)) % len(self._spec_palette)]
                elif _best < 1.2: seg.bgcolor = "#2a2a2a"
                else:             seg.bgcolor = _bg

        # 8 drifting stars that move outward from centre
        _gkey = (_bands, _levels)
        if not hasattr(self, '_pul_key') or self._pul_key != _gkey:
            _rng = random.Random(13)
            _max_r = ((_cx**2 + _cy**2)**0.5) + 1.5
            self._pul_stars = [
                [_rng.uniform(0, 6.2832), _rng.uniform(min(5.0, _max_r * 0.35), _max_r), _rng.uniform(0.36, 2.7)]
                for _ in range(8)
            ]
            self._pul_key = _gkey
        _max_r = ((_cx**2 + _cy**2)**0.5) + 1.5
        for _st in self._pul_stars:
            _st[1] += _st[2] * 0.18 * _spd
            if _st[1] > _max_r:
                _st[1] = min(5.0, _max_r * 0.35)
                _st[0] = random.uniform(0, 6.2832)
            _bx = int(round(_cx + math.cos(_st[0]) * _st[1]))
            _by = int(round(_cy + math.sin(_st[0]) * _st[1]))
            if 0 <= _bx < _bands and 0 <= _by < _levels:
                self._spec_segments[_bx][_by].bgcolor = "#b0b0b0"

        try: self._spectrum_box.update()
        except: pass

    def _render_spectrum_idle_pacman(self):
        if not self._spec_segments: return
        _bands  = max(1, self._spec_bands); _levels = max(1, self._spec_levels)
        _spd    = max(0.25, min(3.0, float(self._spec_idle_speed)))
        _bg     = "#101010"
        _track  = _bands + 20
        _old_p  = self._spec_idle_phase
        self._spec_idle_phase = (self._spec_idle_phase + 0.35 * _spd) % float(_track)
        if self._spec_idle_phase < _old_p:
            self._spec_idle_cycle_done = True
        _y0     = max(0, min(_levels - 5, (_levels // 2) - 2))
        _pac_x  = int(self._spec_idle_phase) - 6
        _ghost_x= _pac_x + 10
        if _ghost_x > _bands + 5:
            _ghost_x -= _track

        _pac_closed = ["01110","11111","11111","11111","01110"]
        _pac_open   = ["01110","11100","11000","11100","01110"]
        _ghost      = ["01110","11111","10101","11111","10101"]
        _pac        = _pac_open if (int(time.monotonic() * 5.0) % 2) else _pac_closed

        _set_px = self._set_px; _draw_mask = self._draw_mask

        try:
            for _x in range(_bands):
                for _y in range(_levels):
                    self._spec_segments[_x][_y].bgcolor = _bg
            _draw_mask(_pac, _pac_x, _y0, "#ffd400")
            _draw_mask(_ghost, _ghost_x, _y0, "#ff4d6d")
            _set_px(_ghost_x + 1, _y0 + 1, "#c8f7ff")
            _set_px(_ghost_x + 3, _y0 + 1, "#c8f7ff")
        except Exception:
            self._render_spectrum_idle_pulse()
            return

        try: self._spectrum_box.update()
        except: pass

    def _render_spectrum_idle_tetris(self):
        if not self._spec_segments: return
        _bands  = max(1, self._spec_bands); _levels = max(1, self._spec_levels)
        _spd    = max(0.25, min(3.0, float(self._spec_idle_speed)))
        _bg     = "#101010"
        self._spec_idle_cycle_done = True
        self._spec_idle_phase = (self._spec_idle_phase + 0.85 * _spd) % 100000.0
        _tick   = int(self._spec_idle_phase)

        _well_w = max(6, min(10, _bands - 2))
        _left   = max(0, (_bands - _well_w) // 2)
        _wall_l = _left - 1; _wall_r = _left + _well_w

        _pieces = [
            ([(0,1),(1,1),(2,1),(3,1)], "#4dd0e1"),
            ([(1,0),(2,0),(1,1),(2,1)], "#ffd54f"),
            ([(1,0),(0,1),(1,1),(2,1)], "#ba68c8"),
            ([(0,0),(0,1),(1,1),(2,1)], "#ff8a65"),
            ([(2,0),(0,1),(1,1),(2,1)], "#64b5f6"),
            ([(1,0),(2,0),(0,1),(1,1)], "#81c784"),
            ([(0,0),(1,0),(1,1),(2,1)], "#f06292"),
        ]
        _stack_pal = ["#2aa198","#d79921","#6c71c4","#859900","#cb4b16","#268bd2","#d33682"]
        _set_px = self._set_px

        try:
            for _x in range(_bands):
                for _y in range(_levels): self._spec_segments[_x][_y].bgcolor = _bg

            for _y in range(_levels): _set_px(_wall_l, _y, "#2f2f2f"); _set_px(_wall_r, _y, "#2f2f2f")

            for _wx in range(_well_w):
                for _wy in range(_levels):
                    if ((_wx + _wy) % 2) == 0: _set_px(_left + _wx, _wy, "#121212")

            _stack_h = []
            for _wx in range(_well_w):
                _h = 2 + int(((math.sin(_wx * 0.9 + _tick * 0.08) + 1.0) * 1.5))
                _stack_h.append(max(1, min(_levels - 5, _h)))

            _cycle      = _levels + 7
            _pi         = (_tick // _cycle) % len(_pieces)
            _pc, _pcol  = _pieces[_pi]
            _px         = ((_tick // _cycle) * 3) % max(1, _well_w - 4)
            _py         = -3 + (_tick % _cycle)

            for _dx, _ in _pc:
                _col = _px + _dx
                if 0 <= _col < _well_w: _stack_h[_col] = max(1, _stack_h[_col] - 2)

            for _wx in range(_well_w):
                for _n in range(_stack_h[_wx]):
                    _set_px(_left + _wx, _levels - 1 - _n, _stack_pal[(_wx + _n + _tick // 3) % len(_stack_pal)])

            if (_tick % 40) >= 34:
                _fy = _levels - 1 - ((_tick // 2) % 2)
                for _wx in range(_well_w): _set_px(_left + _wx, _fy, "#f0f0f0")

            for _dx, _dy in _pc: _set_px(_left + _px + _dx, _py + _dy, _pcol)
        except Exception:
            self._render_spectrum_idle_pulse(); return

        try: self._spectrum_box.update()
        except: pass

    def _render_spectrum_idle_invaders(self):
        if not self._spec_segments: return
        _bands  = max(1, self._spec_bands); _levels = max(1, self._spec_levels)
        _spd    = max(0.25, min(3.0, float(self._spec_idle_speed)))
        _bg     = "#101010"
        _old_p  = self._spec_idle_phase
        self._spec_idle_phase = (self._spec_idle_phase + 0.22 * _spd) % 100000.0
        _phase  = self._spec_idle_phase

        _inv_a = ["00100100","01111110","11011011","11111111","01111110","01000010"]
        _inv_b = ["00100100","01111110","11011011","11111111","00111100","01100110"]

        _set_px = self._set_px; _draw_mask = self._draw_mask

        try:
            for _x in range(_bands):
                for _y in range(_levels): self._spec_segments[_x][_y].bgcolor = _bg

            _frame   = int(_phase)
            _wiggle  = 1 if ((_frame // 2) % 2) else 0
            _mask    = _inv_a if ((_frame // 3) % 2) else _inv_b
            _span    = max(1, _bands - 26)
            _step    = _frame % (2 * _span)
            _old_step= int(_old_p) % (2 * _span)
            if _step < _old_step: self._spec_idle_cycle_done = True
            _offset  = _step if _step < _span else (2 * _span - _step)
            _x0      = max(0, min(_bands - 1, 1 + _offset))

            for _i in range(3): _draw_mask(_mask, _x0 + _i * 9, 2 + _wiggle, "#8cff66")

            _laser_x   = _x0 + 12
            _laser_top = 9 + (_frame % max(2, _levels - 9))
            for _y in range(_laser_top, min(_levels, _laser_top + 4)): _set_px(_laser_x, _y, "#ff5252")
        except Exception:
            self._render_spectrum_idle_pulse(); return

        try: self._spectrum_box.update()
        except: pass

    def _render_spectrum_idle_snake(self):
        if not self._spec_segments: return
        _bands  = max(1, self._spec_bands); _levels = max(1, self._spec_levels)
        _spd    = max(0.25, min(3.0, float(self._spec_idle_speed)))
        _bg     = "#101010"
        _slen   = max(4, _bands - 2)

        # reset state when grid size changes or on first run
        _gkey = (_bands, _levels)
        if not hasattr(self, '_sk_gkey') or self._sk_gkey != _gkey:
            import random as _r
            self._sk_gkey  = _gkey
            self._sk_x, self._sk_y   = 0, _r.randint(0, _levels - 1)
            self._sk_dx, self._sk_dy = 1, 0
            self._sk_body  = [(0, self._sk_y)] * _slen
            self._sk_food  = (_r.randint(0, _bands - 1), _r.randint(0, _levels - 1))
            self._sk_tick  = 0.0

        self._sk_tick += 0.55 * _spd
        _steps = max(1, int(self._sk_tick))
        self._sk_tick -= _steps

        import random as _r
        for _ in range(_steps):
            _hx, _hy         = self._sk_x, self._sk_y
            _dx, _dy         = self._sk_dx, self._sk_dy
            _fx, _fy         = self._sk_food
            _nx, _ny         = _hx + _dx, _hy + _dy

            if _dx != 0:                               # moving horizontally
                if _nx < 0 or _nx >= _bands:           # hit side wall
                    _nx = _hx
                    if _hy == _fy:                     # already on food row → turn toward food
                        _dx = 1 if _fx > _hx else -1; _dy = 0
                    else:                              # turn toward food row
                        _dx = 0; _dy = 1 if _fy > _hy else -1
                    _nx, _ny = _hx + _dx, _hy + _dy
            else:                                      # moving vertically
                if _ny == _fy or _hy == _fy:           # reached food row → turn toward food
                    _ny = _fy
                    _dx = 1 if _fx >= _hx else -1; _dy = 0
                    _nx = _hx + _dx
                elif _ny < 0 or _ny >= _levels:        # hit top/bottom → turn toward food
                    _ny = _hy
                    _dx = 1 if _fx >= _hx else -1; _dy = 0
                    _nx = _hx + _dx

            self._sk_x = max(0, min(_bands - 1, _nx))
            self._sk_y = max(0, min(_levels - 1, _ny))
            self._sk_dx, self._sk_dy = _dx, _dy
            self._sk_body = [(self._sk_x, self._sk_y)] + self._sk_body[:_slen - 1]

            if (self._sk_x, self._sk_y) == self._sk_food:
                self._sk_food = (_r.randint(0, _bands - 1), _r.randint(0, _levels - 1))
                self._spec_idle_cycle_done = True

        try:
            for _x in range(_bands):
                for _y in range(_levels): self._spec_segments[_x][_y].bgcolor = _bg
            _set_px = self._set_px
            _set_px(*self._sk_food, "#ff6a3d")
            for _si, (_bx, _by) in enumerate(self._sk_body):
                _c = "#d7ff8a" if _si == 0 else f"#00{max(72, 255 - _si * 9):02x}28"
                _set_px(_bx, _by, _c)
        except Exception:
            self._render_spectrum_idle_pulse(); return

        try: self._spectrum_box.update()
        except: pass

    def _ensure_spectrum_graphics_controls(self, width, height):
        """Create/update reusable controls for non-grid spectrum graphics effects."""
        _w = max(120, int(width))
        _h = max(80, int(height))
        _size = (_w, _h)
        if self._spec_graphics_ready and self._spec_graphics_view_size == _size:
            return

        self._spec_graphics_layer.controls.clear()
        self._spec_graphics_stars = []
        self._spec_graphics_lines = []

        _rng = random.Random(0x51A7)
        _star_count = max(24, min(96, int((_w * _h) / 2200)))
        for _ in range(_star_count):
            _dot = ft.Container(
                left=_rng.randint(0, max(0, _w - 3)),
                top=_rng.randint(0, max(0, _h - 3)),
                width=2,
                height=2,
                border_radius=1,
                bgcolor="#6a6a6a",
                opacity=0.45,
            )
            self._spec_graphics_stars.append(_dot)
            self._spec_graphics_layer.controls.append(_dot)

        for _ in range(18):
            _txt = ft.Text(
                "",
                size=12,
                color="#ffd76a",
                text_align=ft.TextAlign.CENTER,
                no_wrap=True,
                weight=ft.FontWeight.W_600,
            )
            _slot = ft.Container(
                content=_txt,
                left=0,
                top=0,
                width=1,
                height=1,
                alignment=ft.Alignment.CENTER,
                visible=False,
            )
            self._spec_graphics_lines.append((_slot, _txt))
            self._spec_graphics_layer.controls.append(_slot)

        self._spec_graphics_ready = True
        self._spec_graphics_view_size = _size

    def _render_spectrum_idle_starwars(self):
        """Star Wars crawl using pre-allocated graphics controls."""
        _w = int(self._spectrum_box.width or self._spec_box_graphics_size[0])
        _h = int(self._spectrum_box.height or self._spec_box_graphics_size[1])
        _w = max(120, _w)
        _h = max(80, _h)

        self._ensure_spectrum_graphics_controls(_w, _h)

        _spd = max(0.25, min(3.0, float(self._spec_idle_speed)))
        _lines = [
            ("STAR WARS", True),
            ("IN A LAND FAR AWAY...", False),
            ("WLED COMMAND CENTER+", False),
            ("A NEW HOPE", False),
            ("FOR SMART LIGHT CONTROL", False),
            ("MAY YOUR LIGHTS", False),
            ("BE WITH YOU", False),
        ]

        _line_gap = 16
        _start_y = _h - 28
        _line_count = max(1, len(_lines))
        _cycle_px = _start_y + ((_line_count - 1) * _line_gap) + 80
        _old_p = self._spec_idle_phase
        self._spec_idle_phase = (self._spec_idle_phase + (0.30 * _spd)) % float(max(1, _cycle_px))
        if self._spec_idle_phase < _old_p:
            self._spec_idle_cycle_done = True
        _base_y = _start_y - self._spec_idle_phase

        _now = time.monotonic()
        for _i, _dot in enumerate(self._spec_graphics_stars):
            _tw = int(_now * 3.4 + (_i * 1.23)) % 8
            _alpha = (0.22, 0.35, 0.5, 0.7, 0.45, 0.3, 0.18, 0.08)[_tw]
            _v = (120, 145, 180, 220, 160, 140, 115, 90)[_tw]
            _dot.bgcolor = f"#{_v:02x}{_v:02x}{_v:02x}"
            _dot.opacity = _alpha

        for _idx, (_slot, _txt) in enumerate(self._spec_graphics_lines):
            if _idx >= len(_lines):
                _slot.visible = False
                continue

            _text, _is_title = _lines[_idx]
            _y = _base_y + (_idx * _line_gap)
            if (not _text) or _y < -80 or _y > (_h + 60):
                _slot.visible = False
                continue

            _depth = max(0.0, min(1.0, _y / max(1.0, float(_h))))
            _scale = 0.18 + ((_depth ** 1.18) * 1.30)
            _base_fs = 30 if _is_title else 22
            _font_size = max(8, int(_base_fs * _scale))

            _char_units = 0.0
            for _ch in _text:
                if _ch == " ":
                    _char_units += 0.42
                elif _ch in "WM@#%&":
                    _char_units += 1.0
                elif _ch in "I|.,:;!'":
                    _char_units += 0.40
                else:
                    _char_units += 0.72

            _side_pad = max(14, int(_font_size * 0.95))
            _est_w = max(30, int((_char_units * _font_size) + (_side_pad * 2)))
            _est_h = max(14, int(_font_size * 1.75))

            _slot.left = int((_w - _est_w) / 2)
            _slot.top = int(_y)
            _slot.width = _est_w
            _slot.height = _est_h
            _slot.visible = True

            if _is_title:
                _r, _g, _b = 255, 140, 20
                _txt.weight = ft.FontWeight.BOLD
            else:
                _r, _g, _b = 255, 214, 80
                _txt.weight = ft.FontWeight.W_600

            _txt.value = _text
            _txt.size = _font_size
            _txt.color = f"#{_r:02x}{_g:02x}{_b:02x}"

        try:
            self._spectrum_box.update()
        except Exception:
            pass

    # ── Hallucination mode ────────────────────────────────────────────────────

    def _compute_audio_frame(self):
        """Called once per render frame. Writes shared audio values all modes can read."""
        self._sa_raw_bass = self._bar(0)
        self._sa_mono_vu  = max(0.0, min(1.0,
            (float(self._spec_vu_left or 0) + float(self._spec_vu_right or 0)) * 0.5))
        (self._sa_bass, self._sa_mid, self._sa_treble,
        self._sa_beat, self._sa_peak) = self._extract_audio_bands()
        _sm = self._sm
        self._sa_smth_bass      = _sm(self._sa_smth_bass, self._sa_raw_bass, 0.50, 0.06)
        self._sa_smth_vu        = _sm(self._sa_smth_vu,   self._sa_mono_vu,  0.30, 0.05)
        self._sa_beat_bass_avg  = self._sa_beat_bass_avg * 0.92 + self._sa_bass * 0.08
        _bt = max(0.06, self._sa_beat_bass_avg * max(1.05, 1.35 / max(0.1, self._sa_beat_sens)))
        _beat_now = self._sa_bass > _bt
        self._sa_beat_detected  = _beat_now and not self._sa_beat_prev
        self._sa_beat_prev      = _beat_now
        self._sa_prev_smth_bass = self._sa_smth_bass

    def _extract_audio_bands(self):
        """Return (bass, mid, treble, beat, peak) scalars [0..1].
        Reads _spec_bars (already sensitivity- and reactivity-scaled by the audio loop).
        Tracks a per-band running max for adaptive beat detection."""
        bars = self._spec_bars
        n = len(bars)
        if n == 0:
            return 0.0, 0.0, 0.0, False, 0.0

        lo = max(1, n // 3)
        hi = max(lo + 1, (2 * n) // 3)

        raw_bass   = max(bars[:lo])
        raw_mid    = max(bars[lo:hi])
        raw_treble = max(bars[hi:])

        bass   = min(1.0, raw_bass   * 1.4)
        mid    = min(1.0, raw_mid    * 1.6)
        treble = min(1.0, raw_treble * 1.8)

        avg = float(getattr(self, "_spec_hallu_bass_avg", 0.0))
        avg = avg * 0.92 + bass * 0.08
        self._spec_hallu_bass_avg = avg
        beat = bool(bass > max(0.18, avg * 1.35))

        peak = max(bass, mid, treble)
        return bass, mid, treble, beat, peak

    def _effective_hallu_submode(self):
        if self._spec_hallu_submode != "random":
            return self._spec_hallu_submode
        now = time.monotonic()
        if now >= self._spec_hallu_random_next_ts or self._spec_hallu_random_current is None:
            self._advance_hallu_random()
            self._spec_hallu_random_next_ts = now + float(self._spec_hallu_random_cycle_seconds)
        return self._spec_hallu_random_current

    def _advance_hallu_random(self):
        pool = [s for s in self._spec_hallu_random_cycle_choices
                if s != self._spec_hallu_random_current]
        if not pool:
            pool = list(self._spec_hallu_random_cycle_choices)
        self._spec_hallu_random_current = random.choice(pool) if pool else "mirror"
        self._spec_hallu_aux = {}
        self._spec_hallu_prev_frame = None

    def _render_hallucination(self):
        if not _PIL_OK:
            return
        W, H = 600, 124
        sub = self._effective_hallu_submode()

        # Song-change armed → advance random
        if (self._spec_hallu_song_switch_armed and self._spec_hallu_submode == "random"):
            _now = time.monotonic()
            if (_now - float(self._spec_last_audio_ts)) >= float(self._spec_mode_song_silence_seconds):
                self._advance_hallu_random()
                sub = self._spec_hallu_random_current
                self._spec_hallu_song_switch_armed = False

        if (self._spec_hallu_prev_frame is None or
                self._spec_hallu_prev_frame.size != (W, H)):
            self._spec_hallu_prev_frame = _PILImage.new("RGBA", (W, H), (0, 0, 0, 255))

        bass, mid, treble, beat, peak = self._extract_audio_bands()

        # ── Excited state logic (Big Bass hits only) ──────────────────
        _now = time.monotonic()
        _smth = self._spec_hallu_aux.get("_excited_smth_bass", 0.0)
        # Fast rise, slow decay to catch the peak
        _smth = (_smth * 0.5 + bass * 0.5) if bass > _smth else (_smth * 0.94 + bass * 0.06)
        _prev = self._spec_hallu_aux.get("_excited_prev_bass", 0.0)

        # Trigger only on rising edge of a heavy bass hit (>0.75)
        if (_smth > 0.85 and _prev <= 0.85):
            self._spec_hallu_excited = True
            self._spec_hallu_excited_ts = _now

        self._spec_hallu_aux["_excited_smth_bass"] = _smth
        self._spec_hallu_aux["_excited_prev_bass"] = _smth

        # cooldown
        if _now - self._spec_hallu_excited_ts > 2.0:
            self._spec_hallu_excited = False

        # Update status log on state change
        if self._spec_hallu_excited != self._spec_hallu_excited_prev:
            if self._spec_hallu_excited:
                self._status("Hallucination: EXCITED", "cyan", debug_only=True)
            else:
                self._status("Hallucination: Calm", "grey500", debug_only=True)
            self._spec_hallu_excited_prev = self._spec_hallu_excited

        # ── Color-mode tick: drive _spec_display_hue and gradient flag ──
        _hallu_cm = self._spec_color_mode_per_mode.get("hallucination", "loop")
        if _hallu_cm == "random":
            _hallu_cm = self._tick_random_cm("hallucination", beat) or "loop"
        if _hallu_cm == "loop":
            self._spec_display_hue = (time.monotonic() / 20.0) % 1.0
        self._spec_hallu_gradient = (_hallu_cm == "gradient")

        params = self._spec_hallu_params_per_submode.get(sub, {})
        fn = {
            "mirror":   self._hallu_mirror,
            "chroma":   self._hallu_chroma,
            "perlin":   self._hallu_perlin,
            "morph":    self._hallu_morph,
        }.get(sub, self._hallu_mirror)
        try:
            frame = fn(W, H, bass, mid, treble, beat, peak, params)
        except Exception:
            frame = self._draw_hallu_base(W, H, bass, mid, treble)
        self._spec_hallu_prev_frame = frame.copy()
        self._blit_hallu_frame(frame)

    def _blit_hallu_frame(self, pil_img):
        try:
            buf = io.BytesIO()
            pil_img.convert("RGB").save(buf, format="PNG", compress_level=1)
            b64 = base64.b64encode(buf.getvalue()).decode()
            if self._hallu_img is not None:
                self._hallu_img.src = "data:image/png;base64," + b64
                self._hallu_img.update()
        except Exception:
            pass

    def _draw_hallu_base(self, W, H, bass, mid, treble, mirror_mode=False):
        """Render the configured base layer as a PIL RGBA Image."""
        kind = self._spec_hallu_base_kind
        img = _PILImage.new("RGBA", (W, H), (0, 0, 0, 255))
        draw = _PILDraw.Draw(img)
        h_val = self._spec_display_hue

        def _col(h, s=1.0, v=1.0, a=255):
            r, g, b = colorsys.hsv_to_rgb(h % 1.0, s, v)
            return (int(r*255), int(g*255), int(b*255), a)

        def peak_alpha_helper(b, m, t):
            return min(0.4, b * 0.4 + m * 0.2 + t * 0.15)

        # Gradient-mode multiplier: widens per-element hue spread for rainbow effect
        _hue_spread = 0.7 if getattr(self, "_spec_hallu_gradient", False) else 0.3

        bars = self._spec_bars
        n = max(1, len(bars))

        if kind == "bars":
            bar_w = max(1, W // n)
            # Mirror mode: alpha 140 so trail behind shows through; otherwise opaque
            _alpha = 140 if mirror_mode else 255
            for i, bv in enumerate(bars[:n]):
                bh = max(1, int(bv * H))
                x0 = i * bar_w
                x1 = x0 + bar_w - 1
                col = _col((h_val + i / n * _hue_spread) % 1.0, 1.0, 0.5 + bv * 0.5, _alpha)
                draw.rectangle([x0, H - bh, x1, H - 1], fill=col)

        elif kind == "waveform":
            # Continuous sine-sum trace (oscilloscope style) — sampled every 2px.
            # Each band drives a different harmonic: bass=slow, treble=fast shimmer.
            t_now = time.monotonic()
            cy = H / 2
            A_bass   = H * 0.35
            A_mid    = H * 0.28
            A_treble = H * 0.14
            pts = []
            for x in range(0, W, 2):
                f = x / W
                y = (cy
                    + math.sin(f * 14 + t_now * 4.0) * A_mid    * mid
                    + math.sin(f * 30 + t_now * 7.0) * A_treble * treble
                    + math.sin(f * 5  + t_now * 2.0) * A_bass   * bass)
                pts.append((x, int(y)))
            if len(pts) >= 2:
                _gA = 50  if mirror_mode else 80
                _lA = 180 if mirror_mode else 255
                glow_col = _col(h_val, 0.6, 1.0, _gA)
                draw.line(pts, fill=glow_col, width=5)
                line_col = _col(h_val, 1.0, 0.9, _lA)
                draw.line(pts, fill=line_col, width=2)

        elif kind == "circle":
            cx, cy = W // 2, H // 2
            R_base = min(cx, cy) * 0.55
            steps = 128
            t_now = time.monotonic()
            # Continuous sin formula — no per-bar indexing so curve closes cleanly
            pts = []
            for i in range(steps):
                ang = 2 * math.pi * i / steps
                r = (R_base
                    + math.sin(ang * 6  + t_now * 3.0) * 7.0 * mid
                    + math.sin(ang * 14 + t_now * 5.0) * 4.0 * treble
                    + bass * 16.0)
                pts.append((int(cx + r * math.cos(ang)), int(cy + r * math.sin(ang))))
            _gA = 50  if mirror_mode else 80
            _lA = 180 if mirror_mode else 255
            # polygon auto-closes (last→first vertex), eliminating the seam
            glow_col = _col(h_val, 0.6, 1.0, _gA)
            draw.polygon(pts, outline=glow_col)
            line_col = _col(h_val, 1.0, 0.9, _lA)
            draw.polygon(pts, outline=line_col)

        elif kind == "particles":
            # Radial emission from center so particles trail outward under mirror feedback
            aux = self._spec_hallu_aux
            cx, cy = W / 2.0, H / 2.0
            if "bp" not in aux:
                aux["bp"] = []
            parts = aux["bp"]
            target = 80
            while len(parts) < target:
                ang = random.uniform(0, 2 * math.pi)
                spd = 0.4 + random.random() * 0.6
                parts.append([cx, cy,
                            math.cos(ang) * spd, math.sin(ang) * spd,
                            random.randint(40, 90)])
            energy = bass + mid * 0.5
            _alpha = 130 if mirror_mode else 200
            new_p = []
            for pt in parts:
                px, py, vx, vy, life = pt
                vx *= (1.0 + energy * 0.06)
                vy *= (1.0 + energy * 0.06)
                px += vx * (1 + bass * 1.5)
                py += vy * (1 + bass * 1.5)
                life -= 1
                if life <= 0 or px < -2 or px > W + 2 or py < -2 or py > H + 2:
                    ang = random.uniform(0, 2 * math.pi)
                    spd = 0.4 + random.random() * 0.6 + bass * 0.4
                    px, py = cx, cy
                    vx, vy = math.cos(ang) * spd, math.sin(ang) * spd
                    life = random.randint(40, 90)
                new_p.append([px, py, vx, vy, life])
                r_px = max(1, int(1 + bass * 2 + treble * 1.5))
                _ph = (h_val + math.atan2(py - cy, px - cx) / (2 * math.pi)) % 1.0
                col = _col(_ph, 1.0, 0.6 + peak_alpha_helper(bass, mid, treble), _alpha)
                draw.ellipse([px - r_px, py - r_px, px + r_px, py + r_px], fill=col)
            aux["bp"] = new_p

        elif kind != "BLANK":
            try:
                jp = os.path.join(self._version_dir, kind)
                if os.path.isfile(jp):
                    bg = _PILImage.open(jp).convert("RGBA").resize((W, H))
                    if mirror_mode:
                        r, g, bl, al = bg.split()
                        al = al.point(lambda v: int(v * 0.55))
                        bg = _PILImage.merge("RGBA", (r, g, bl, al))
                        img.alpha_composite(bg)
                    else:
                        img.paste(bg, (0, 0))
            except Exception:
                pass
        return img

    def _hallu_mirror(self, W, H, bass, mid, treble, beat, peak, p):
        """Droste tunnel (particles base) / Ghost ribbon (waveform/circle/image bases).

        Sliders:
        rotDeg  (-10..+10): rotation per history layer (all bases).
        zoom    (0.85..0.99): per-layer scale / vertical spread.
        opacity: particles base = scatter (0=radial inward, 1=random);
                other bases  = ghost blur amount.
        Bars slider  -> particle count.
        Peak Decay   -> beat-burst cooldown duration.
        """
        aux    = self._spec_hallu_aux
        N      = 26
        kind   = self._spec_hallu_base_kind
        _grad  = getattr(self, "_spec_hallu_gradient", False)
        h_val  = self._spec_display_hue
        cx, cy = W / 2.0, H / 2.0
        t_auto = time.monotonic()

        # Big-hit detector (rising edge of smoothed bass > 0.68) -- shared by all paths
        _smth_bass = aux.get("_smth_bass", 0.0)
        _smth_bass = (_smth_bass * 0.50 + bass * 0.50 if bass > _smth_bass
                    else _smth_bass * 0.94 + bass * 0.06)
        _prev_smth = aux.get("_prev_smth", 0.0)
        _big_hit   = (_smth_bass > 0.68 and _prev_smth <= 0.68)
        aux["_smth_bass"] = _smth_bass
        aux["_prev_smth"] = _smth_bass

        def _osc(key):
            st = aux.setdefault(key, {"pos": 0.0, "vel": 0.005, "pause_until": 0.0, "target": 1.0})
            if t_auto < st["pause_until"]:
                return st["pos"]
            spd = 0.0001 + peak * 0.0015
            st["vel"] = st["vel"] * (1.0 - spd) + (st["target"] - st["pos"]) * spd
            st["pos"] = max(-1.0, min(1.0, st["pos"] + st["vel"]))
            if abs(st["pos"]) >= 0.98:
                st["vel"] *= -0.3
                st["target"] = -math.copysign(1.0, st["pos"]) * random.uniform(0.3, 0.75)
            elif _big_hit:
                if random.random() < 0.45:
                    if random.random() < 0.65:
                        st["pause_until"] = t_auto + random.uniform(1.5, 5.0)
                    else:
                        st["target"] = -math.copysign(1.0, st["vel"]) * random.uniform(0.3, 0.8)
            return st["pos"]

        # ================================================================
        # PARTICLES PATH -- single-buffer Droste feedback
        # ================================================================
        if kind == "particles":
            _bi = getattr(_PILImage, "Resampling", _PILImage).BILINEAR

            # ── Smoothers ─────────────────────────────────────────────
            local_vu   = aux.get("_local_vu",   0.0)
            local_vu   = local_vu * 0.80 + peak * 0.20
            aux["_local_vu"] = local_vu

            fast_vu    = aux.get("_fast_vu",    0.0)
            fast_vu    = fast_vu * 0.55 + bass * 0.45
            aux["_fast_vu"] = fast_vu

            local_bass = aux.get("_local_bass", 0.0)
            local_bass = local_bass * 0.65 + bass * 0.35
            aux["_local_bass"] = local_bass

            # ── Brightness / dim floor ────────────────────────────────
            dim_thresh  = max(0.0, min(0.5, float(p.get("dim_thresh", 0.25))))
            bright_held = aux.get("_bright_held", 0.0)
            if fast_vu > dim_thresh:
                bright_held = bright_held * 0.4 + fast_vu * 0.6
            else:
                bright_held = bright_held * 0.97          # ~2s fade at 30fps
            aux["_bright_held"] = bright_held
            brightness = min(1.0, bright_held)

            # ── Particle count / beat cooldown ────────────────────────
            N_P        = max(10, min(120, int(getattr(self, "_spec_analysis_bands", 32)) * 2))
            _pd        = max(0.4, float(getattr(self, "_spec_peak_decay", 1.0)))
            beat_decay = max(0.85, min(0.975, 1.0 - 0.12 / _pd))

            # ── Beat detection ────────────────────────────────────────
            local_beat = self._sa_beat_detected

            # ── Speed burst + beat pop ────────────────────────────────
            beat_mul    = aux.get("beat_mul",    1.0)
            beat_energy = aux.get("beat_energy", 0.0)
            if local_beat:
                beat_mul    = 2.0 + bass * 3.0
                beat_energy = min(1.0, bass * 1.5)
            beat_mul    = beat_mul    * beat_decay + 1.0 * (1.0 - beat_decay)
            beat_energy = beat_energy * 0.88
            aux["beat_mul"]    = beat_mul
            aux["beat_energy"] = beat_energy

            # ── Slider params ─────────────────────────────────────────
            rot_base   = float(p.get("rotDeg",  2.0))
            zoom_base  = float(p.get("zoom",    0.94))
            trail_fade = max(0.5, min(1.0, float(p.get("opacity", 0.92))))

            excited = getattr(self, "_spec_hallu_excited", False)
            cap     = 1.0 if excited else 0.5

            if getattr(self, "_spec_hallu_auto_rot", False):
                driven_rot = max(0.5, abs(rot_base)) * cap * _osc("rot_osc")
            else:
                driven_rot = rot_base

            if getattr(self, "_spec_hallu_auto_spread", False):
                osc_v       = abs(_osc("spread_osc"))
                driven_zoom = 0.85 + (zoom_base - 0.85) * (1.0 - osc_v * cap)
            else:
                driven_zoom = zoom_base

            # beat pop: on kick the buffer briefly scales outward
            frame_zoom = driven_zoom * (1.0 + beat_energy * 0.08)

            # scatter from treble: auto-varies the particle spray angle
            driven_scatter = 0.1 + treble * 0.5

            # ── Particles ─────────────────────────────────────────────
            def _spawn():
                px    = random.uniform(0.0, W)
                py    = random.uniform(0.0, H)
                angle = random.uniform(0.0, 2.0 * math.pi)  # random straight-line direction
                spd   = random.uniform(0.5, 1.5)
                return {
                    "px": float(px), "py": float(py),
                    "vx": math.cos(angle) * spd,
                    "vy": math.sin(angle) * spd,
                    "wobble_angle": 0.0,
                    "wobble_rate":  random.uniform(-0.003, 0.003),
                }

            particles = aux.get("particles")
            if particles is None or len(particles) != N_P:
                particles = [_spawn() for _ in range(N_P)]
                aux["particles"] = particles

            effective_speed = local_vu * beat_mul * 1.5
            dot_r           = max(1, int(2 + local_bass * 1.5))
            edge            = dot_r + 4

            for pt in particles:
                pt["wobble_angle"] += pt["wobble_rate"]
                wa    = math.sin(pt["wobble_angle"]) * 0.006  # gentle drift only
                cos_w = math.cos(wa);  sin_w = math.sin(wa)
                pt["vx"], pt["vy"] = (pt["vx"] * cos_w - pt["vy"] * sin_w,
                                    pt["vx"] * sin_w + pt["vy"] * cos_w)
                pt["px"] += pt["vx"] * effective_speed
                pt["py"] += pt["vy"] * effective_speed
                if pt["px"] < -edge:      pt["px"] = W + edge
                elif pt["px"] > W + edge: pt["px"] = -edge
                if pt["py"] < -edge:      pt["py"] = H + edge
                elif pt["py"] > H + edge: pt["py"] = -edge

            # ── Draw fresh dots (transparent bg) ──────────────────────
            frame = _PILImage.new("RGBA", (W, H), (0, 0, 0, 0))
            if brightness > 0.01:
                fdraw      = _PILDraw.Draw(frame, "RGBA")
                rv, gv, bv = colorsys.hsv_to_rgb(h_val, 1.0, brightness)
                col        = (int(rv * 255), int(gv * 255), int(bv * 255))
                cr, cg, cb = colorsys.hsv_to_rgb(h_val, 0.4, brightness)
                wh         = (int(cr * 255), int(cg * 255), int(cb * 255))
                r3 = dot_r + 3;  r1 = dot_r + 1
                for pt in particles:
                    x = int(pt["px"]);  y = int(pt["py"])
                    fdraw.ellipse([x-r3, y-r3, x+r3, y+r3], fill=(*col,  60))
                    fdraw.ellipse([x-r1, y-r1, x+r1, y+r1], fill=(*col, 140))
                    fdraw.ellipse([x-dot_r, y-dot_r, x+dot_r, y+dot_r], fill=(*wh, 220))

            # ── Single-buffer Droste feedback ─────────────────────────
            prev = aux.get("prev_frame")
            if prev is None or prev.size != (W, H):
                prev = _PILImage.new("RGBA", (W, H), (0, 0, 0, 255))

            # Affine: rotate + scale around canvas center
            # inv_zoom < 1 in the inverse mapping → content shrinks toward center
            inv_zoom = 1.0 / max(0.5, frame_zoom)
            cos_r = math.cos(math.radians(driven_rot))
            sin_r = math.sin(math.radians(driven_rot))
            a_m = inv_zoom * cos_r;  b_m = -inv_zoom * sin_r
            c_m = inv_zoom * sin_r;  d_m =  inv_zoom * cos_r
            tx  = cx - (cx * a_m + cy * b_m)
            ty  = cy - (cx * c_m + cy * d_m)
            warped = prev.transform(
                (W, H), _PILImage.AFFINE, (a_m, b_m, tx, c_m, d_m, ty),
                resample=_bi, fillcolor=(0, 0, 0, 255),
            )

            # Fade trail each frame (trail_fade slider, 0.5-1.0)
            r2, g2, b2, a2 = warped.split()
            a2 = a2.point(lambda v, op=trail_fade: int(v * op))
            warped = _PILImage.merge("RGBA", (r2, g2, b2, a2))

            # Composite: history + fresh dots on top
            canvas = _PILImage.new("RGBA", (W, H), (0, 0, 0, 255))
            canvas = _PILImage.alpha_composite(canvas, warped)
            canvas = _PILImage.alpha_composite(canvas, frame)
            aux["prev_frame"] = canvas.copy()
            return canvas

        # ================================================================
        # SHARED SETUP for waveform, circle, image/bars paths
        # ================================================================
        feedback = float(p.get("opacity", 0.92))

        rot_base = float(p.get("rotDeg", 0.0)) * 1.5
        if getattr(self, "_spec_hallu_auto_rot", False):
            target_rot = max(0.5, abs(rot_base)) * _osc("rot_osc")
        else:
            target_rot = rot_base

        if kind == "waveform":
            if not getattr(self, "_spec_hallu_excited", False):
                target_rot *= 0.25
                if peak < 0.15:
                    _grav = max(0.0, min(1.0, (peak - 0.02) / 0.13))
                    target_rot *= _grav

        lerp_f = 0.08
        self._spec_hallu_rot_smooth += (target_rot - self._spec_hallu_rot_smooth) * lerp_f
        rot_step = self._spec_hallu_rot_smooth

        if getattr(self, "_spec_hallu_auto_spread", False):
            zoom_val = 0.92 + 0.06 * _osc("spread_osc")
        else:
            zoom_val = float(p.get("zoom", 0.94))
        y_step = (1.0 - zoom_val) * 20.0

        if getattr(self, "_spec_hallu_auto_blur", False):
            blur_r = max(0.0, 1.2 + 1.2 * _osc("blur_osc"))
        else:
            blur_r = max(0.0, (feedback - 0.5) * 5.0 + max(0.0, 1.0 - y_step) * 0.5)

        is_silent = (peak < 0.02)

        # ================================================================
        # WAVEFORM PATH
        # ================================================================
        if kind == "waveform":
            cy_line  = H / 2.0
            A_bass   = H * 0.35
            A_mid    = H * 0.28
            A_treble = H * 0.14
            t_now    = time.monotonic()

            fresh = []
            for x in range(0, W, 2):
                f = x / W
                y = (cy_line
                    + math.sin(f * 5  + t_now * 2.0) * A_bass   * bass
                    + math.sin(f * 14 + t_now * 4.0) * A_mid    * mid
                    + math.sin(f * 30 + t_now * 7.0) * A_treble * treble)
                fresh.append((float(x), float(y)))

            hist = aux.setdefault("wv_hist", [])
            hist.insert(0, None if is_silent else list(fresh))
            while len(hist) > N:
                hist.pop()

            if _grad:
                h_val = (time.monotonic() / 20.0) % 1.0

            ghost = _PILImage.new("RGBA", (W, H), (0, 0, 0, 255))
            gdraw = _PILDraw.Draw(ghost, "RGBA")
            n_hist = len(hist)

            for idx in range(n_hist - 1, -1, -1):
                if hist[idx] is None:
                    continue
                frac  = idx / max(1, N - 1)
                alpha = int(255 * ((1.0 - frac) ** 1.5))
                if alpha < 3:
                    continue
                angle = math.radians(idx * rot_step)
                cos_a = math.cos(angle);  sin_a = math.sin(angle)
                y_off = idx * y_step

                pts = []
                for (px, py) in hist[idx]:
                    fy = py + (cy_line - py) * frac
                    fy -= y_off
                    dx = px - cx;  dy = fy - cy
                    pts.append((int(cx + dx*cos_a - dy*sin_a),
                                int(cy + dx*sin_a + dy*cos_a)))
                if len(pts) < 2:
                    continue

                brt = max(0.05, 0.88 - frac * 0.80)
                sat = max(0.20, 1.00 - frac * 0.55)
                hue = (h_val + frac * 1.0) % 1.0 if _grad else h_val
                rv, gv, bv = colorsys.hsv_to_rgb(hue, sat, brt)
                col = (int(rv*255), int(gv*255), int(bv*255))
                sharp_w = max(1, int(3.5 - frac * 2.5))
                gdraw.line(pts, fill=(*col, alpha), width=sharp_w)

            if blur_r > 0.3 and _PILFilter is not None:
                ghost = ghost.filter(_PILFilter.GaussianBlur(radius=blur_r))

            live_pts = [(int(px), int(py)) for (px, py) in fresh]
            if len(live_pts) >= 2:
                rv, gv, bv = colorsys.hsv_to_rgb(h_val, 1.0, 0.95)
                ldraw = _PILDraw.Draw(ghost, "RGBA")
                glow  = (int(rv*255), int(gv*255), int(bv*255), 70)
                sharp = (int(rv*255), int(gv*255), int(bv*255), 255)
                ldraw.line(live_pts, fill=glow,  width=5)
                ldraw.line(live_pts, fill=sharp, width=2)
            return ghost

        # ================================================================
        # CIRCLE PATH
        # ================================================================
        elif kind == "circle":
            R_base = min(cx, cy) * 0.55
            steps  = 128
            t_now  = time.monotonic()

            fresh = []
            for i in range(steps):
                ang = 2 * math.pi * i / steps
                r = (R_base
                    + math.sin(ang * 6  + t_now * 3.0) * 7.0 * mid
                    + math.sin(ang * 14 + t_now * 5.0) * 4.0 * treble
                    + bass * 16.0)
                fresh.append((cx + r * math.cos(ang), cy + r * math.sin(ang)))

            hist = aux.setdefault("circle_hist", [])
            hist.insert(0, None if is_silent else list(fresh))
            N_c = 48
            while len(hist) > N_c:
                hist.pop()

            if _grad:
                h_val = (time.monotonic() / 20.0) % 1.0

            ghost = _PILImage.new("RGBA", (W, H), (0, 0, 0, 255))
            gdraw = _PILDraw.Draw(ghost, "RGBA")
            n_hist = len(hist)

            for idx in range(n_hist - 1, -1, -1):
                if hist[idx] is None:
                    continue
                frac  = idx / max(1, N_c - 1)
                alpha = int(255 * ((1.0 - frac) ** 1.5))
                if alpha < 3:
                    continue
                angle = math.radians(idx * rot_step)
                cos_a = math.cos(angle);  sin_a = math.sin(angle)
                y_off = idx * y_step

                pts = []
                for (px, py) in hist[idx]:
                    dx = px - cx;  dy = py - cy
                    scale = 1.0 + frac * 3.0
                    dx *= scale;  dy *= scale
                    pts.append((int(cx + dx*cos_a - dy*sin_a),
                                int(cy + dx*sin_a + dy*cos_a + y_off)))
                if len(pts) < 3:
                    continue

                brt = max(0.05, 0.88 - frac * 0.80)
                sat = max(0.20, 1.00 - frac * 0.55)
                hue = (h_val + frac * 1.0) % 1.0 if _grad else h_val
                rv, gv, bv = colorsys.hsv_to_rgb(hue, sat, brt)
                col = (int(rv*255), int(gv*255), int(bv*255), alpha)
                gdraw.polygon(pts, outline=col)

            if blur_r > 0.3 and _PILFilter is not None:
                ghost = ghost.filter(_PILFilter.GaussianBlur(radius=blur_r))

            live_pts = [(int(px), int(py)) for (px, py) in fresh]
            if len(live_pts) >= 3:
                rv, gv, bv = colorsys.hsv_to_rgb(h_val, 1.0, 0.95)
                ldraw = _PILDraw.Draw(ghost, "RGBA")
                glow  = (int(rv*255), int(gv*255), int(bv*255), 70)
                sharp = (int(rv*255), int(gv*255), int(bv*255), 255)
                ldraw.polygon(live_pts, outline=glow)
                ldraw.polygon(live_pts, outline=sharp)
            return ghost

        # ================================================================
        # IMAGE / BARS / BLANK PATH -- affine ghost trail
        # ================================================================
        fresh_img = self._draw_hallu_base(W, H, bass, mid, treble)
        hist      = aux.setdefault("img_hist", [])
        hist.insert(0, None if is_silent else fresh_img.copy())
        while len(hist) > N:
            hist.pop()

        ghost = _PILImage.new("RGBA", (W, H), (0, 0, 0, 255))
        _BI   = getattr(_PILImage, "Resampling", _PILImage).BILINEAR

        for idx in range(len(hist) - 1, -1, -1):
            if hist[idx] is None:
                continue
            frac  = idx / max(1, N - 1)
            a_mul = (1.0 - frac) ** 1.5
            if a_mul < 0.01:
                continue

            rot_r = math.radians(idx * rot_step)
            cs    = math.cos(rot_r);  sn = math.sin(rot_r)
            y_off = idx * y_step

            af = (cs,  sn, cx - cs*cx - sn*cy,
                -sn, cs, cy + sn*cx - cs*cy + y_off)
            warped = hist[idx].transform((W, H), _PILImage.AFFINE, af,
                                        resample=_BI, fillcolor=(0, 0, 0, 0))

            rr, gg, bb, aa = warped.split()
            aa = aa.point(lambda v: int(v * a_mul))
            warped = _PILImage.merge("RGBA", (rr, gg, bb, aa))
            ghost.alpha_composite(warped)

        if blur_r > 0.3 and _PILFilter is not None:
            ghost = ghost.filter(_PILFilter.GaussianBlur(radius=blur_r))

        ghost.alpha_composite(fresh_img)
        return ghost

    def _hallu_chroma(self, W, H, bass, mid, treble, beat, peak, p):
        """Chromatic aberration — shift R/G/B channels independently."""
        try:
            import numpy as np
        except ImportError:
            return self._draw_hallu_base(W, H, bass, mid, treble)

        base = np.array(self._draw_hallu_base(W, H, bass, mid, treble), dtype=np.float32)
        off  = int(2 + treble * float(p.get("maxSplit", 14)))
        offY = int((mid - 0.5) * float(p.get("maxSplit", 14)) * 0.4)

        out = np.zeros_like(base)
        out[..., 0] = np.roll(base[..., 0], (-offY, -off), axis=(0, 1))
        out[..., 1] = base[..., 1]
        out[..., 2] = np.roll(base[..., 2], (offY,  off), axis=(0, 1))
        out[..., 3] = 255

        trail = float(p.get("trail", 0.18))
        prev_arr = np.array(self._spec_hallu_prev_frame, dtype=np.float32)
        blended = out * (1 - trail) + prev_arr * trail * 0.85
        return _PILImage.fromarray(np.clip(blended, 0, 255).astype(np.uint8))

    def _hallu_perlin(self, W, H, bass, mid, treble, beat, peak, p):
        """Perlin-style flow field particles."""
        try:
            import numpy as np
        except ImportError:
            return self._draw_hallu_base(W, H, bass, mid, treble)

        aux = self._spec_hallu_aux
        noise_scale = float(p.get("noiseScale", 0.012))
        evolve_rate = float(p.get("evolveRate", 0.30))

        if "noise_table" not in aux:
            rng = np.random.default_rng(42)
            aux["noise_table"] = rng.random((256, 256), dtype=np.float32)
        noise_t = aux["noise_table"]

        if "parts" not in aux:
            aux["parts"] = np.column_stack([
                np.random.uniform(0, W, 140).astype(np.float32),
                np.random.uniform(0, H, 140).astype(np.float32),
            ])
        parts = aux["parts"]
        phase = aux.get("phase", 0.0) + evolve_rate * 0.01 * (1 + mid * 2)
        aux["phase"] = phase

        xi = (parts[:, 0] * noise_scale * W + phase * W).astype(int) % 256
        yi = (parts[:, 1] * noise_scale * H + phase * H * 0.7).astype(int) % 256
        angles = noise_t[yi, xi] * (2 * math.pi * 2)
        speed = 0.8 + (bass + mid) * 1.5
        parts[:, 0] = (parts[:, 0] + np.cos(angles) * speed) % W
        parts[:, 1] = (parts[:, 1] + np.sin(angles) * speed) % H
        aux["parts"] = parts

        prev_arr = np.array(self._spec_hallu_prev_frame, dtype=np.float32)
        fade = 0.93 - bass * 0.06
        prev_arr[..., :3] *= fade
        canvas = _PILImage.fromarray(np.clip(prev_arr, 0, 255).astype(np.uint8))
        draw = _PILDraw.Draw(canvas, "RGBA")
        h_val = self._spec_display_hue
        r_px  = 1 if bass < 0.25 else (2 if bass < 0.6 else 3)
        a_px  = int(180 + treble * 75)
        for px, py in parts:
            ix, iy = int(px), int(py)
            hue = (h_val + float(px) / W * 0.4 + float(py) / H * 0.15) % 1.0
            rv, gv, bv = colorsys.hsv_to_rgb(hue, 1.0, 0.55 + peak * 0.45)
            col = (int(rv*255), int(gv*255), int(bv*255), a_px)
            draw.ellipse([ix - r_px, iy - r_px, ix + r_px, iy + r_px], fill=col)
        return canvas

    def _hallu_morph(self, W, H, bass, mid, treble, beat, peak, p):
        """Geometry morphing: layered polygon rings with audio-driven vertex jitter."""
        aux = self._spec_hallu_aux

        dt = 0.005 + peak * 0.18
        t = aux.get("t", 0.0) + dt
        aux["t"] = t

        layers = max(1, int(p.get("layers", 3)))
        jitter = float(p.get("jitter", 1.0))

        faded = _PILImage.blend(_PILImage.new("RGBA", (W, H), (0, 0, 0, 255)),
                                self._spec_hallu_prev_frame, 0.78)
        draw = _PILDraw.Draw(faded, "RGBA")
        cx, cy = W // 2, H // 2
        R_max  = min(cx, cy) - 2
        h_val  = self._spec_display_hue
        N      = 120

        beat_kick = 1.0 + (0.18 if self._sa_beat_detected else 0.0)
        A_bass   = 14.0 * jitter
        A_mid    =  9.0 * jitter
        A_treble =  6.0 * jitter

        for L in range(layers):
            R_base = R_max * (0.30 + 0.70 * (L + 1) / layers) * beat_kick
            hue = (h_val + L / max(1, layers) * 0.25) % 1.0
            rc, gc, bc = colorsys.hsv_to_rgb(hue, 1.0, 0.7 + bass * 0.3)
            alpha = max(70, 200 - L * 45)
            color = (int(rc*255), int(gc*255), int(bc*255), alpha)
            pts = []
            for i in range(N):
                theta = 2 * math.pi * i / N
                rv = (R_base
                    + math.sin(5  * theta + 2 * t + L * 0.7) * A_bass   * bass
                    + math.sin(11 * theta + 4 * t + L * 1.3) * A_mid    * mid
                    + math.sin(23 * theta + 7 * t + L * 2.1) * A_treble * treble)
                pts.append((int(cx + rv * math.cos(theta)),
                            int(cy + rv * math.sin(theta))))
            if len(pts) >= 3:
                draw.polygon(pts, outline=color)
        return faded

    # ── Audio analyzer loop ───────────────────────────────────────────────────

    def _audio_analyzer_loop(self):
        time.sleep(1.0)
        _current_device      = None
        _last_idle_only_render = 0.0
        _was_sampling        = bool(self._spec_sampling_enabled)

        while self.running and not self._spec_disabled:
            _now      = time.monotonic()
            _sampling = bool(self._spec_sampling_enabled)

            if _was_sampling and not _sampling:
                self._spec_idle_active = bool(self._spec_idle_enabled)
                if self._spec_idle_active:
                    self._spec_idle_phase = 0.0; self._spec_idle_scroll = 0
                    self._spec_idle_cycle_done = False
                    if str(self._spec_idle_effect).lower() == "random":
                        self._spec_idle_random_next_ts = _now
                        self._spec_idle_cycle_done = True

            if not _was_sampling and _sampling:
                self._spec_last_audio_ts = _now
                self._spec_idle_active   = False

            _was_sampling = _sampling

            if not _sampling:
                _ri = self._get_spec_render_interval()
                self._spec_idle_active = bool(self._spec_idle_enabled)
                if self._spec_idle_active:
                    if _now - _last_idle_only_render >= _ri:
                        self._schedule_render()
                        _last_idle_only_render = _now
                    self._spec_display_cleared = False
                    time.sleep(_ri)
                else:
                    if not self._spec_display_cleared:
                        try:
                            _loop = self._event_loop
                            if _loop and _loop.is_running():
                                _loop.call_soon_threadsafe(self._sync_clear_display)
                        except Exception:
                            pass
                        self._spec_display_cleared = True
                    time.sleep(0.25)
                continue
            else:
                self._spec_display_cleared = False

            try:
                import importlib
                _np = importlib.import_module("numpy")
                if not self._spec_np_patch_applied and hasattr(_np, "frombuffer"):
                    _orig = _np.fromstring
                    def _compat(string, dtype=float, count=-1, sep=''):
                        if sep == '' and not isinstance(string, str):
                            try: return _np.frombuffer(memoryview(string), dtype=dtype, count=count)
                            except: pass
                        return _orig(string, dtype=dtype, count=count, sep=sep)
                    _np.fromstring = _compat
                    self._spec_np_patch_applied = True
                _sc = importlib.import_module("soundcard")
            except Exception:
                if not self._spec_log_once:
                    self._spec_log_once = True
                    self._status("Install 'numpy' and 'soundcard' for live audio", "orange400")
                time.sleep(2.0)
                continue

            try:
                if not self._spec_audio_sources:
                    try:
                        self._refresh_spectrum_sources()
                        if self._spec_audio_sources:
                            self._status(f"Found {len(self._spec_audio_sources)} audio source(s)")
                    except Exception:
                        self._spec_audio_sources = []

                if self._spec_source_changed or _current_device is None:
                    _switched = self._spec_source_changed
                    self._spec_source_changed   = False
                    self._spec_capture_channels = 2
                    _current_device             = None
                    if self._spec_selected_source and self._spec_audio_sources:
                        for name, idx in self._spec_audio_sources:
                            if name == self._spec_selected_source:
                                try:
                                    _all = list(_sc.all_microphones(include_loopback=True))
                                    if idx < len(_all):
                                        _current_device = _all[idx]
                                        self._status(f"Source: {self._spec_selected_source}")
                                        break
                                except Exception:
                                    pass
                    if _current_device is None:
                        _current_device, _kind = self._pick_default_spectrum_source(_sc)
                        self._spec_selected_source = None
                        if _current_device:
                            _tag = "output" if _kind == "output-loopback" else "input"
                            self._status(f"Default {_tag}: {_current_device.name}")
                    if _current_device is not None and (_switched or self._spec_gain != 1.0):
                        self._spec_gain = 0.05
                        self._reset_spec_analysis_state()
                        self._spec_vu_gain = 0.18
                        self._spec_vu_left = self._spec_vu_right = 0.0
                        self._spec_vu_peak_left = self._spec_vu_peak_right = 0.0
                        self._spec_vu_peak_hold_left = self._spec_vu_peak_hold_right = 0
                        self._spec_idle_active   = False
                        self._spec_last_audio_ts = time.monotonic()

                if _current_device is None:
                    if not self._spec_no_audio_warned:
                        self._spec_no_audio_warned = True
                        self._status("No audio device found. Enable Stereo Mix.", "orange400")
                    time.sleep(2.0)
                    continue

                _sr = int(self._spec_sample_rate or 48000)
                if _sr not in (16000, 22050, 32000, 44100, 48000): _sr = 48000
                _ab = max(6, min(int(self._spec_bands), int(self._spec_analysis_bands or self._spec_bands)))
                _n  = 1024 if _sr >= 32000 else 512
                _fps_target = max(8, min(60, int(self._spec_target_fps or 24)))
                _fn = max(128, int(_sr / _fps_target))
                _freqs = _np.fft.rfftfreq(_n, d=1.0 / _sr)
                _edges = _np.geomspace(40.0, 15000.0, _ab + 1)
                _bins  = []
                for i in range(_ab):
                    lo = int(_np.searchsorted(_freqs, _edges[i],     side="left"))
                    hi = int(_np.searchsorted(_freqs, _edges[i + 1], side="left"))
                    if hi <= lo: hi = min(len(_freqs), lo + 1)
                    _bins.append((lo, hi))
                _bcenters     = _np.sqrt(_edges[:-1] * _edges[1:])
                _bcenters_log = _np.log10(_bcenters)
                _eq_log       = _np.log10(_np.asarray(self._spec_eq_freqs, dtype=float))
                # precompute per-session constants so the hot inner loop is GIL-free numpy
                _blackman_w  = _np.blackman(_n)
                _bin_starts  = _np.array([lo for lo, hi in _bins], dtype=int)
                _bin_sizes   = _np.array([hi - lo for lo, hi in _bins], dtype=float)

                import warnings as _w
                _w.filterwarnings("ignore", message="data discontinuity", category=Warning)
                with _current_device.recorder(samplerate=_sr,
                                            channels=int(self._spec_capture_channels),
                                            blocksize=_fn) as _rec:
                    _roll_mono    = _np.zeros(_n, dtype=float)
                    _render_stop  = threading.Event()
                    def _render_timer(_stop=_render_stop):
                        try: ctypes.windll.winmm.timeBeginPeriod(1)
                        except Exception: pass
                        while not _stop.is_set():
                            _stop.wait(self._get_spec_render_interval())
                            if not _stop.is_set():
                                self._schedule_render()
                        try: ctypes.windll.winmm.timeEndPeriod(1)
                        except Exception: pass
                    threading.Thread(target=_render_timer, daemon=True,
                                     name="SA_RenderTimer").start()
                    self._status(f"Audio loop: {_fps_target} fps target, {_fn} frames/block (~{_fn*1000//_sr} ms)", debug_only=True)
                    while self.running and not self._spec_source_changed and not self._spec_disabled:
                        _t0  = time.monotonic()
                        _buf = _rec.record(numframes=_fn)
                        # use actual block duration for smoothing normalization so physics
                        # stay consistent regardless of what rate the hardware delivers
                        _tscale = max(_fn / _sr, time.monotonic() - _t0) * 24.0
                        _raw = _np.asarray(_buf)
                        if _raw.size == 0: time.sleep(0.01); continue

                        if _raw.ndim == 2 and _raw.shape[1] >= 2:
                            _left  = _raw[:, 0].reshape(-1)
                            _right = _raw[:, 1].reshape(-1)
                            _arr   = ((_left + _right) * 0.5).reshape(-1)
                        else:
                            _arr = _raw.reshape(-1)
                            _left = _right = _arr

                        # slide rolling window forward with the new mono samples
                        _nc = min(len(_arr), _n)
                        _roll_mono[:_n - _nc] = _roll_mono[_nc:]
                        _roll_mono[_n - _nc:] = _arr[-_nc:]

                        _vu_n = min(_n, len(_left), len(_right))
                        if _vu_n > 0:
                            _l_lvl = float(_np.sqrt(_np.mean(_left[-_vu_n:]  ** 2)))
                            _r_lvl = float(_np.sqrt(_np.mean(_right[-_vu_n:] ** 2)))
                        else:
                            _l_lvl = _r_lvl = 0.0

                        _arr  = _roll_mono * _blackman_w
                        _spec = _np.abs(_np.fft.rfft(_arr))
                        _sums = _np.add.reduceat(_spec ** 2, _bin_starts)[:_ab]
                        _vals = _np.log1p(_np.sqrt(_sums / _bin_sizes) * 30.0)

                        _avg_arr = _np.asarray(self._spec_band_avg, dtype=float)
                        if _avg_arr.size != _vals.size:
                            self._spec_source_changed = True; continue
                        _rising = _vals > _avg_arr
                        _sm_r   = 1.0 - 0.85  ** _tscale
                        _sm_f   = 1.0 - 0.995 ** _tscale
                        self._spec_band_avg = list(_np.where(
                            _rising,
                            _avg_arr * (1.0 - _sm_r) + _vals * _sm_r,
                            _avg_arr * (1.0 - _sm_f) + _vals * _sm_f,
                        ))
                        _vals = _np.maximum(0.0, _vals - _avg_arr * 0.85)
                        _mx   = float(_vals.max()) if _vals.size else 0.0

                        if _mx > 0:
                            _gf = 1.0 - 0.993 ** _tscale
                            if _mx > self._spec_gain:
                                self._spec_gain = self._spec_gain * (1.0 - _sm_r) + _mx * _sm_r
                            else:
                                self._spec_gain = max(0.02, self._spec_gain * (1.0 - _gf) + _mx * _gf)
                            _vals = _vals / max(self._spec_gain, 1e-6)

                        _eq_curve = _np.interp(_bcenters_log, _eq_log,
                                            _np.asarray(self._spec_eq_gains, dtype=float))
                        _vals = _vals * self._spec_sensitivity * _eq_curve

                        _now = time.monotonic()
                        if _mx > float(self._spec_idle_threshold):
                            self._spec_last_audio_ts = _now
                            if _mx > float(self._spec_idle_threshold) * 1.25:
                                self._spec_mode_song_debounce += 1
                                if self._spec_mode_song_debounce >= 4:
                                    self._spec_mode_song_switch_armed = True
                            else:
                                self._spec_mode_song_debounce = 0
                        else:
                            self._spec_mode_song_debounce = 0

                        _idle_on = (bool(self._spec_idle_enabled) and
                                    (_now - self._spec_last_audio_ts) >= float(self._spec_idle_timeout))
                        if _idle_on and not self._spec_idle_active:
                            self._spec_idle_phase = 0.0; self._spec_idle_scroll = 0
                            self._spec_idle_cycle_done = False
                            if str(self._spec_idle_effect).lower() == "random":
                                self._spec_idle_random_next_ts = _now
                                self._spec_idle_cycle_done     = True
                        self._spec_idle_active = _idle_on

                        if _idle_on:
                            if _now - _last_render >= _ri:
                                self._schedule_render(); _last_render = _now
                            continue

                        _react    = max(0.25, min(3.0, float(self._spec_reactivity)))
                        _bar_dec  = max(0.1,  min(5.0, float(self._spec_bar_decay)))
                        _peak_dec = max(0.1,  min(5.0, float(self._spec_peak_decay)))
                        _rise     = 1.0 - (1.0 - min(0.98, 0.72 * _react)) ** _tscale
                        _fall     = 0.04 * _bar_dec  * _tscale
                        _ph_frames= max(2, int(round(8.0 / _react / _tscale)))
                        _pdrop    = 0.02 * _peak_dec * _tscale

                        # vectorized bar + peak physics — numpy ops release the GIL
                        # so the render thread can run PIL work concurrently
                        _bars_a  = _np.asarray(self._spec_bars,      dtype=float)
                        _peaks_a = _np.asarray(self._spec_peaks,     dtype=float)
                        _holds_a = _np.asarray(self._spec_peak_hold, dtype=int)
                        _tgt     = _np.clip(_vals, 0.0, 1.0)

                        _rising_b = _tgt >= _bars_a
                        _bars_a   = _np.where(_rising_b,
                                              _bars_a + (_tgt - _bars_a) * _rise,
                                              _np.maximum(0.0, _bars_a - _fall))

                        _new_peak  = _bars_a >= _peaks_a
                        _peaks_a   = _np.where(_new_peak, _bars_a, _peaks_a)
                        _holds_a   = _np.where(_new_peak, _ph_frames, _holds_a)
                        _hold_done = ~_new_peak & (_holds_a <= 0)
                        _peaks_a   = _np.where(_hold_done,
                                               _np.maximum(0.0, _peaks_a - _pdrop), _peaks_a)
                        _holds_a   = _np.where(~_new_peak & ~_hold_done, _holds_a - 1, _holds_a)

                        self._spec_bars      = _bars_a.tolist()
                        self._spec_peaks     = _peaks_a.tolist()
                        self._spec_peak_hold = _holds_a.tolist()

                        _l_env    = float(_np.log1p(_l_lvl * 18.0))
                        _r_env    = float(_np.log1p(_r_lvl * 18.0))
                        _vu_max   = max(_l_env, _r_env)
                        if _vu_max > 0.0:
                            _vgr = 1.0 - 0.86  ** _tscale
                            _vgf = 1.0 - 0.994 ** _tscale
                            if _vu_max > self._spec_vu_gain:
                                self._spec_vu_gain = self._spec_vu_gain * (1.0 - _vgr) + _vu_max * _vgr
                            else:
                                self._spec_vu_gain = max(0.06, self._spec_vu_gain * (1.0 - _vgf) + _vu_max * _vgf)
                        _vs  = 0.65 * (max(0.1, min(1.5, float(self._spec_sensitivity))) / 0.7)
                        _vn  = max(self._spec_vu_gain, 1e-6)
                        _lt  = float(max(0.0, min(1.0, (_l_env / _vn) * _vs)))
                        _rt  = float(max(0.0, min(1.0, (_r_env / _vn) * _vs)))

                        self._spec_vu_left  = (self._spec_vu_left  + (_lt - self._spec_vu_left)  * _rise
                                            if _lt >= self._spec_vu_left
                                            else max(0.0, self._spec_vu_left  - _fall))
                        self._spec_vu_right = (self._spec_vu_right + (_rt - self._spec_vu_right) * _rise
                                            if _rt >= self._spec_vu_right
                                            else max(0.0, self._spec_vu_right - _fall))

                        if self._spec_vu_left >= self._spec_vu_peak_left:
                            self._spec_vu_peak_left      = self._spec_vu_left
                            self._spec_vu_peak_hold_left = _ph_frames
                        elif self._spec_vu_peak_hold_left > 0:
                            self._spec_vu_peak_hold_left -= 1
                        else:
                            self._spec_vu_peak_left = max(0.0, self._spec_vu_peak_left - _pdrop)

                        if self._spec_vu_right >= self._spec_vu_peak_right:
                            self._spec_vu_peak_right      = self._spec_vu_right
                            self._spec_vu_peak_hold_right = _ph_frames
                        elif self._spec_vu_peak_hold_right > 0:
                            self._spec_vu_peak_hold_right -= 1
                        else:
                            self._spec_vu_peak_right = max(0.0, self._spec_vu_peak_right - _pdrop)

                    _render_stop.set()

            except Exception as ex:
                _es = str(ex).lower()
                if ("channel" in _es or "channels" in _es) and self._spec_capture_channels > 1:
                    self._spec_capture_channels = 1
                    self._status("Stereo unavailable, using mono", "grey500")
                    time.sleep(0.4); continue
                if "binary mode of fromstring is removed" in _es:
                    self._spec_disabled = True
                    self._status("Disabled: soundcard incompatible with NumPy 2.x", "orange400")
                    return
                if self.running:
                    self._status(f"Audio error: {ex}", "orange400")
                _current_device = None
                time.sleep(1.0)


# ── Standalone wrapper ────────────────────────────────────────────────────────

class SpectrumApp:
    """Thin wrapper that runs SpectrumController as a standalone window.

    Handles window sizing, position save/restore, and always-on-top — none of
    which belong in the reusable SpectrumController.
    """

    def __init__(self, page: ft.Page):
        self.page = page

        # ── Window setup ──────────────────────────────────────────────────
        page.title            = "WLEDCC Spectrum Analyzer"
        page.bgcolor          = "#0a0a0a"
        page.theme_mode       = ft.ThemeMode.DARK
        page.padding          = 0
        page.window.width     = _SA_COMPACT_W
        page.window.height    = _SA_COMPACT_H
        page.window.resizable = True
        page.window.min_width  = 200
        page.window.always_on_top = True
        page.window.bgcolor   = "#0a0a0a"
        # ── Debug mode state (for standalone mode) ──
        _argv = sys.argv
        self._debug_mode = "--debug-mode" in _argv

        def _on_screen(x, y):
            """Return True if (x, y) is within the virtual desktop (handles multi-monitor)."""
            try:
                import ctypes
                u = ctypes.windll.user32
                vx = u.GetSystemMetrics(76)   # SM_XVIRTUALSCREEN
                vy = u.GetSystemMetrics(77)   # SM_YVIRTUALSCREEN
                vw = u.GetSystemMetrics(78)   # SM_CXVIRTUALSCREEN
                vh = u.GetSystemMetrics(79)   # SM_CYVIRTUALSCREEN
                return vx <= int(x) < vx + vw and vy <= int(y) < vy + vh
            except Exception:
                return True

        # ── Restore saved window position + aspect-lock preference ──────────
        self._aspect_lock = True   # default: snap height to correct AR
        try:
            with open(SA_CONFIG_FILE, "r", encoding="utf-8") as _f:
                _c = json.load(_f)
            _x = _c.get("win_x")
            _y = _c.get("win_y")
            if _x is not None and _y is not None and _on_screen(_x, _y):
                page.window.left = _x
                page.window.top  = _y
            self._aspect_lock = bool(_c.get("aspect_lock", True))
        except Exception:
            pass

        # ── Spawn-below position + size (passed by parent SA via --spawn-* args) ─
        try:
            _argv = sys.argv
            _sx = int(_argv[_argv.index("--spawn-x") + 1]) if "--spawn-x" in _argv else None
            _sy = int(_argv[_argv.index("--spawn-y") + 1]) if "--spawn-y" in _argv else None
            _sw = int(_argv[_argv.index("--spawn-w") + 1]) if "--spawn-w" in _argv else None
            _sh = int(_argv[_argv.index("--spawn-h") + 1]) if "--spawn-h" in _argv else None
            if _sx is not None or _sy is not None:
                async def _apply_spawn_pos():
                    import asyncio
                    await asyncio.sleep(0.25)
                    self._skip_resize_events = True
                    try:
                        _cx = _sx if _sx is not None else int(page.window.left or 0)
                        _cy = _sy if _sy is not None else int(page.window.top  or 0)
                        try:
                            import ctypes.wintypes as _wt2
                            _wa2 = _wt2.RECT()
                            ctypes.windll.user32.SystemParametersInfoW(48, 0, ctypes.byref(_wa2), 0)
                            _nw = _sw if _sw is not None else _SA_COMPACT_W
                            _nh = _sh if _sh is not None else _SA_COMPACT_H
                            # Use tracker HWND — FindWindowW matches first window with
                            # this title, which is wrong when multiple SA instances exist.
                            try:
                                _hs = getattr(self._sc, "_own_hwnd", None)
                                _dp = ctypes.windll.user32.GetDpiForWindow(_hs) if _hs else 0
                            except Exception:
                                _dp = 0
                            _sc2 = (_dp or 96) / 96
                            _cx = max(round(_wa2.left   / _sc2),
                                    min(_cx, round(_wa2.right  / _sc2) - _nw))
                            _cy = max(round(_wa2.top    / _sc2),
                                    min(_cy, round(_wa2.bottom / _sc2) - _nh))
                        except Exception:
                            pass
                        if _sx is not None: page.window.left = _cx
                        if _sy is not None: page.window.top  = _cy
                        if _sw is not None: page.window.width  = _sw
                        if _sh is not None: page.window.height = _sh
                        page.update()
                        await asyncio.sleep(0.2)
                        # Refresh tracker rect now that the OS has moved the window.
                        # The background thread polls every 200 ms, so without this
                        # the tracker could hold a stale initial-open position when
                        # the user clicks detach immediately after a spawn.
                        try:
                            _hwnd = getattr(self._sc, "_own_hwnd", None)
                            if _hwnd:
                                _rr = ctypes.wintypes.RECT()
                                if ctypes.windll.user32.GetWindowRect(_hwnd, ctypes.byref(_rr)):
                                    if _rr.right - _rr.left > 50:
                                        self._sc._own_rect = _rr
                        except Exception:
                            pass
                    finally:
                        self._skip_resize_events = False
                    self._recompute_scale()
                page.run_task(_apply_spawn_pos)
        except Exception:
            pass

        self._skip_resize_events = False
        self._pre_menu_top    = None
        self._pre_menu_left   = None
        self._pre_menu_width  = None
        self._pre_menu_height = None
        self._menu_open       = False
        self._menu_extra_h    = 0
        self._sa_root         = None
        self._root            = None
        self._event_loop      = None
        self._hook_installed  = False
        self._wndproc_cb      = None   # keep WndProc callback alive
        self._wndproc_orig    = None

        # ── Create the controller ─────────────────────────────────────────
        self._sc = SpectrumController(
            page             = page,
            version_dir      = _VERSION_DIR,
            menu_expand_fn   = self._expand_for_menu,
            menu_collapse_fn = self._restore_compact,
            debug_mode_fn    = lambda: self._debug_mode,
        )
        self._sc._aspect_lock = self._aspect_lock   # keep mirror in sync from the start

        # ── Apply --start-mode override (set by parent when detaching) ────
        try:
            _argv = sys.argv
            if "--start-mode" in _argv:
                _sm = _argv[_argv.index("--start-mode") + 1]
                _sc = self._sc
                if _sm in ("neon_drift", "retro_tech", "custom_vu", "hud_reactor",
                        "beat_saber", "neon_cascade", "rock_stage"):
                    _sc._neon_vu_theme = _sm
                if _sm in _sc._spec_color_mode_per_mode:
                    _sc._spec_bs_color_mode = _sc._spec_color_mode_per_mode[_sm]
                if _sm == "hallucination" and "--hallu-sub" in _argv:
                    _sc._spec_hallu_submode   = _argv[_argv.index("--hallu-sub")  + 1]
                    _sc._spec_hallu_base_kind = _argv[_argv.index("--hallu-base") + 1]
                    _sc._spec_hallu_aux        = {}
                    _sc._spec_hallu_prev_frame = None
                _sc._spec_mode = _sm
                _sc._spec_mode_random_current = _sm
                _sc._apply_per_mode_settings(_sm, restart_audio=False)
        except Exception:
            pass

        # ── Wire page layout ──────────────────────────────────────────────
        # _sa_root is the scalable SA display (scale applied here only).
        # status_text overlays it at bottom-left — temporary debug info.
        # menu_host sits below the scale so the settings panel always renders
        # at native (1:1) size regardless of SA zoom level.
        self._sa_root = ft.Container(content=self._sc.widget, padding=0)
        self._status_overlay = ft.Container(
            content=self._sc.status_text,
            left=4, bottom=2,
            visible=self._debug_mode,
        )
        _ar_locked = self._aspect_lock
        _ar_style  = ft.ButtonStyle(
            padding=ft.Padding.all(2),
            bgcolor=ft.Colors.with_opacity(0.0, "#000000"),
            overlay_color=ft.Colors.with_opacity(0.18, "#ffffff"),
            shape=ft.RoundedRectangleBorder(radius=3),
        )
        self._aspect_btn = ft.Container(
            content=ft.IconButton(
                icon=ft.Icons.LOCK if _ar_locked else ft.Icons.LOCK_OPEN,
                icon_size=11,
                icon_color="#00c8ff" if _ar_locked else "#555555",
                tooltip=ft.Tooltip(
                    message=("Auto aspect ratio ON — click to allow free resize"
                            if _ar_locked else
                            "Free resize ON — click to lock aspect ratio"),
                    prefer_below=False,
                ),
                style=_ar_style,
                on_click=self._toggle_aspect_lock,
            ),
            right=3, bottom=3,
            opacity=0.0,
        )
        # Wrapping Container captures hover for the whole SA area. Moving from
        # the display onto a button stays inside the container, so on_hover
        # only fires False when the mouse actually leaves the SA area entirely.
        _sa_area = ft.Container(
            content=ft.Stack(
                [self._sa_root, self._sc.btn_overlay, self._status_overlay,
                self._aspect_btn],
                expand=True,
            ),
            on_hover=self._on_sa_area_hover,
            expand=True,
        )
        self._root = ft.Column([
            _sa_area,
            ft.Container(
                content=self._sc.menu_host,
                padding=ft.Padding.only(left=8, right=8, bottom=6),
            ),
        ], spacing=0, tight=True, expand=True)
        page.add(self._root)

        # ── Start audio ───────────────────────────────────────────────────
        self._sc.start()
        self._sc.sync_status_visibility()  # Sync initial debug mode state
        self._status_overlay.visible = self._debug_mode
        self._status_overlay.update()
        # ── Window event handler (close) + resize hook ────────────────────
        page.window.on_event = self._on_window_event
        page.on_resize        = lambda e: self._recompute_scale()



    # ── Window management ─────────────────────────────────────────────────────

    def _expand_for_menu(self, w=_SA_MENU_W, h=_SA_MENU_H):
        if self._menu_open:
            return
        try:
            self._menu_open = True
            self._pre_menu_top    = self.page.window.top
            self._pre_menu_left   = self.page.window.left
            self._pre_menu_width  = self.page.window.width
            self._pre_menu_height = self.page.window.height
            # Menu panel height at native (1:1) scale — SA visual height is separate
            self._menu_extra_h = h - _SA_COMPACT_H
            try:
                wa = ctypes.wintypes.RECT()
                ctypes.windll.user32.SystemParametersInfoW(48, 0, ctypes.byref(wa), 0)
                usable_h = wa.bottom
            except Exception:
                usable_h = 1080
            # Expand height by the menu panel only; SA keeps its current visual height
            cur_h = self._pre_menu_height if self._pre_menu_height is not None else _SA_COMPACT_H
            new_h = cur_h + self._menu_extra_h
            # Only shift top if the expanded window would go off the bottom of the screen
            new_top = self._pre_menu_top if self._pre_menu_top is not None else 0
            if new_top + new_h > usable_h:
                new_top = max(0, usable_h - new_h)
            # Preserve user's width; only grow if narrower than minimum menu width
            new_w = max(int(self._pre_menu_width or w), w)
            self.page.window.top    = new_top
            self.page.window.width  = new_w
            self.page.window.height = new_h
            self.page.update()
        except Exception:
            pass

    def _restore_compact(self):
        try:
            self._menu_open    = False
            self._menu_extra_h = 0
            _left   = self._pre_menu_left
            _top    = self._pre_menu_top
            _width  = self._pre_menu_width
            _height = self._pre_menu_height
            self._pre_menu_top = self._pre_menu_left = None
            self._pre_menu_width = self._pre_menu_height = None
            if _width  is not None: self.page.window.width  = _width
            if _height is not None: self.page.window.height = _height
            if _left   is not None: self.page.window.left   = _left
            if _top    is not None: self.page.window.top    = _top
            self.page.update()
            self._recompute_scale()
        except Exception:
            pass

    def _recompute_scale(self):
        if self._sa_root is None:
            return
        if getattr(self, "_skip_resize_events", False):
            return
        # Capture event loop on first call and lazily install WM_EXITSIZEMOVE hook.
        if self._event_loop is None:
            try:
                import asyncio as _asyncio
                self._event_loop = _asyncio.get_running_loop()
            except RuntimeError:
                pass
        if not self._hook_installed:
            self._install_sizemove_hook()
        try:
            cw     = self.page.width  or _SA_COMPACT_W
            page_h = self.page.height or 0
            ch     = max(0, page_h - self._menu_extra_h)
            sx = round(cw / _SA_NATIVE_W, 4)
            sy = round(ch / _SA_NATIVE_H, 4) if ch > 10 else round(cw * _SA_COMPACT_H / (_SA_COMPACT_W * _SA_NATIVE_H), 4)
            self._sa_root.scale = ft.Scale(scale_x=sx, scale_y=sy,
                                        alignment=ft.Alignment.TOP_LEFT)
            # Cache chrome height whenever page.window.height is fresh
            # (i.e. right after a programmatic set by _snap_to_aspect).
            _win_h = self.page.window.height or 0
            _meas  = int(_win_h - page_h - self._menu_extra_h)
            if 0 < _meas <= 100:
                self._chrome_h = _meas
            # Debounce snap: schedule for 400 ms after the last resize event.
            # The WM_EXITSIZEMOVE hook fires _on_resize_complete sooner (on exact
            # mouse release), cancels this timer, and snaps immediately instead.
            # If the hook is not installed, this debounce is the fallback.
            if getattr(self, "_aspect_lock", True) and self._event_loop:
                _old = getattr(self, "_snap_handle", None)
                if _old is not None:
                    _old.cancel()
                self._snap_handle = self._event_loop.call_later(
                    0.4, self._snap_to_aspect)
            self.page.update()
        except Exception:
            pass

    def _install_sizemove_hook(self):
        """Subclass the Flutter window's WndProc to catch WM_EXITSIZEMOVE.

        WM_EXITSIZEMOVE fires exactly once when the user releases the mouse
        after a drag-resize or drag-move.  We use it to snap the window height
        to the correct aspect ratio after the user has finished resizing.
        """
        hwnd = getattr(self._sc, "_own_hwnd", None)
        if not hwnd:
            return
        try:
            _u = ctypes.windll.user32
            # On 64-bit Windows LONG_PTR / LRESULT are 64-bit — set restype
            # explicitly or GetWindowLongPtrW silently truncates the pointer.
            _u.GetWindowLongPtrW.restype  = ctypes.c_ssize_t
            _u.SetWindowLongPtrW.restype  = ctypes.c_ssize_t
            _u.SetWindowLongPtrW.argtypes = [
                ctypes.c_void_p, ctypes.c_int, ctypes.c_ssize_t]
            _u.CallWindowProcW.restype    = ctypes.c_ssize_t
            _u.CallWindowProcW.argtypes   = [
                ctypes.c_ssize_t,   # lpPrevWndFunc (WNDPROC as integer)
                ctypes.c_void_p,    # hWnd
                ctypes.c_uint,      # Msg
                ctypes.c_size_t,    # wParam  (UINT_PTR, unsigned)
                ctypes.c_ssize_t,   # lParam  (LONG_PTR, signed)
            ]
            _WNDPROC = ctypes.WINFUNCTYPE(
                ctypes.c_ssize_t,   # LRESULT (LONG_PTR, signed)
                ctypes.c_void_p,    # HWND
                ctypes.c_uint,      # UINT msg
                ctypes.c_size_t,    # WPARAM
                ctypes.c_ssize_t,   # LPARAM
            )
            _orig = _u.GetWindowLongPtrW(hwnd, -4)   # GWLP_WNDPROC = -4
            _loop = self._event_loop

            def _wndproc(h, msg, wp, lp):
                try:
                    if msg == 0x0232:   # WM_EXITSIZEMOVE
                        if _loop and _loop.is_running():
                            _loop.call_soon_threadsafe(self._on_resize_complete)
                except Exception:
                    pass
                return _u.CallWindowProcW(_orig, h, msg, wp, lp)

            _cb = _WNDPROC(_wndproc)
            self._wndproc_cb   = _cb     # MUST keep reference — GC would free it
            self._wndproc_orig = _orig
            _u.SetWindowLongPtrW(hwnd, -4, _cb)
            self._hook_installed = True
        except Exception:
            pass

    def _on_resize_complete(self):
        """Called on the asyncio thread immediately after WM_EXITSIZEMOVE.
        Cancels the debounce timer and snaps immediately."""
        _old = getattr(self, "_snap_handle", None)
        if _old is not None:
            _old.cancel()
        self._snap_handle = None
        if getattr(self, "_aspect_lock", True):
            self._snap_to_aspect()

    def _snap_to_aspect(self):
        """Snap window height to the correct aspect ratio once."""
        if not getattr(self, "_aspect_lock", True):
            return
        try:
            cw     = self.page.width  or _SA_COMPACT_W
            ph     = self.page.height or 0
            ch     = max(0, ph - self._menu_extra_h)
            snap_h = round(cw * _SA_NATIVE_H / _SA_NATIVE_W)
            if abs(ch - snap_h) > 1:
                chrome_h = getattr(self, "_chrome_h", 30)
                self.page.window.height = snap_h + chrome_h + self._menu_extra_h
                self.page.update()
        except Exception:
            pass

    def _on_sa_area_hover(self, e):
        self._sc._on_sa_hover(e)
        try:
            self._aspect_btn.opacity = 1.0 if e.data else 0.0
            self._aspect_btn.update()
        except Exception:
            pass

    def _toggle_aspect_lock(self, _=None):
        self._aspect_lock = not self._aspect_lock
        self._sc._aspect_lock = self._aspect_lock
        btn = self._aspect_btn.content
        if self._aspect_lock:
            btn.icon       = ft.Icons.LOCK
            btn.icon_color = "#00c8ff"
            btn.tooltip    = ft.Tooltip(message="Auto aspect ratio ON — click to allow free resize", prefer_below=False)
        else:
            btn.icon       = ft.Icons.LOCK_OPEN
            btn.icon_color = "#555555"
            btn.tooltip    = ft.Tooltip(message="Free resize ON — click to lock aspect ratio", prefer_below=False)
        try:   self._aspect_btn.update()
        except Exception: pass
        if self._aspect_lock:
            self._snap_to_aspect()
        try:
            self._sc.save_config(win_pos={"aspect_lock": self._aspect_lock})
        except Exception:
            pass

    def _on_window_event(self, e):
        if getattr(e, "data", None) == "close":
            if self._hook_installed:
                try:
                    hwnd = getattr(self._sc, "_own_hwnd", None)
                    orig = self._wndproc_orig
                    if hwnd and orig:
                        ctypes.windll.user32.SetWindowLongPtrW(hwnd, -4, orig)
                except Exception:
                    pass
            self._sc.stop()


# ── Entry point ───────────────────────────────────────────────────────────────

def main(page: ft.Page):
    SpectrumApp(page)

if __name__ == "__main__":
    ft.run(main)
