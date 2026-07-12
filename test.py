# pip install pymupdf pillow numpy opencv-python

#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
doc_compare.py
==============
Single-file document comparison tool with a
Tkinter UI.
Supported comparisons
---------------------
  * PDF  vs PDF
  * PDF  vs AFP   (cross-format)
  * AFP  vs AFP
What is compared
----------------
  1. Text          -> per-page extraction +
similarity ratio + unified diff
  2. Images        -> every embedded image
object is extracted from both files and
                      matched with SCALE /
SIZE / ASPECT-RATIO INVARIANT matching
                      (pHash + dHash +
aHash + normalized SSIM + ORB homography).
                      Matched pairs are
then checked for geometry differences:
                          - resized       
(same content, different pixel size)
                          - aspect changed
(content stretched / squashed)
                          - rescaled on
page (different physical/placed size)
                          - content differs
(same slot, different pixels)
                      Unmatched images are
reported as ONLY_IN_A / ONLY_IN_B.
  3. Page raster   -> if both documents can
be rasterized (PDF natively; AFP only if
                      you supply an
external AFP->PDF converter command) each
page is
                      rendered, aligned and
compared with SSIM + a red diff heatmap.
Outputs (written to the chosen result
folder)
-------------------------------------------
--
  report.json   full machine-readable
result
  report.html   self-contained visual
report (thumbnails embedded as base64)
  assets/       extracted images + page
diff heatmaps
Install
-------
  pip install pymupdf pillow numpy opencvpython
  (opencv is optional but strongly
recommended - it enables ORB feature
matching,
   which is what makes matching robust to
heavy rescaling / cropping.)
AFP support
-----------
AFP (MO:DCA) is parsed natively: structured
fields are walked, and
  - PTX  (Presentation Text) -> text 
(EBCDIC cp500 by default, configurable)
  - IOCA (BIM/IID/IPD)       -> images
(JPEG / PNG / TIFF / G3 / G4 /
uncompressed)
  - OC   (BOC/OCD)           -> images
(JPEG / PNG / TIFF / GIF embedded objects)
  - IM1  (legacy image)      -> 1-bit
raster images
No external tool is required for text +
image comparison of AFP.
Full-page raster comparison of AFP
additionally needs a converter; put a
command
in the UI field, using {in} and {out}
placeholders, e.g.:
      afp2pdf.exe -i "{in}" -o "{out}"
Author: generated for Mr. Stark
"""
import base64
import datetime
import difflib
import hashlib
import html
import io
import json
import os
import queue
import struct
import subprocess
import sys
import tempfile
import threading
import traceback
from dataclasses import dataclass, field
from typing import Dict, List, Optional,
Tuple
import numpy as np
from PIL import Image, ImageFilter,
ImageOps
# ---- optional / required third-party ----
-------------------------------------------
--
try:
    import fitz  # PyMuPDF
    HAVE_FITZ = True
except Exception:
    HAVE_FITZ = False
try:
    import cv2
    HAVE_CV2 = True
except Exception:
    HAVE_CV2 = False
import tkinter as tk
from tkinter import filedialog, messagebox,
ttk
from tkinter.scrolledtext import
ScrolledText
#
===========================================
==========================================
# Data model
#
===========================================
==========================================
@dataclass
class ImgObj:
    """One embedded image object taken from
a document."""
    doc: str                       # "A" or
"B"
    idx: int
    page: int                      # 1-
based, 0 = unknown / document level
    source: str                    # pdfxobject | afp-ioca | afp-oc | afp-im1
    fmt: str                       # jpeg /
png / raw / ...
    width: int                     #
intrinsic pixels
    height: int
    sha1: str
    placed_w_in: Optional[float] = None   #
physical width on page, inches
    placed_h_in: Optional[float] = None
    pil: Optional[Image.Image] = None
    asset: Optional[str] = None           #
relative path written into result folder
    @property
    def aspect(self) -> float:
        return (self.width / self.height)
if self.height else 0.0
    def meta(self) -> dict:
        return {
            "doc": self.doc, "index":
self.idx, "page": self.page,
            "source": self.source,
"format": self.fmt,
            "width_px": self.width,
"height_px": self.height,
            "aspect_ratio":
round(self.aspect, 5),
            "megapixels": round(self.width
* self.height / 1e6, 4),
            "placed_width_in":
round(self.placed_w_in, 4) if
self.placed_w_in else None,
            "placed_height_in":
round(self.placed_h_in, 4) if
self.placed_h_in else None,
            "sha1": self.sha1,
            "asset": self.asset,
        }
@dataclass
class PageObj:
    number: int
    text: str = ""
    raster: Optional[Image.Image] = None
@dataclass
class Doc:
    path: str
    kind: str                       # "pdf"
| "afp"
    pages: List[PageObj] =
field(default_factory=list)
    images: List[ImgObj] =
field(default_factory=list)
    rasterizable: bool = False
    notes: List[str] =
field(default_factory=list)
    def meta(self) -> dict:
        return {
            "path": self.path,
            "file_name":
os.path.basename(self.path),
            "kind": self.kind,
            "size_bytes":
os.path.getsize(self.path) if
os.path.exists(self.path) else None,
            "pages": len(self.pages),
            "images": len(self.images),
            "rasterizable":
self.rasterizable,
            "notes": self.notes,
        }
#
===========================================
==========================================
# Small utilities
#
===========================================
==========================================
def sha1_bytes(b: bytes) -> str:
    return hashlib.sha1(b).hexdigest()
def sniff_image_format(b: bytes) ->
Optional[str]:
    if len(b) < 8:
        return None
    if b[:3] == b"\xff\xd8\xff":
        return "jpeg"
    if b[:8] == b"\x89PNG\r\n\x1a\n":
        return "png"
    if b[:2] in (b"II", b"MM") and b[2:4]
in (b"\x2a\x00", b"\x00\x2a"):
        return "tiff"
    if b[:6] in (b"GIF87a", b"GIF89a"):
        return "gif"
    if b[:4] == b"\x00\x00\x00\x0c" and
b[4:8] == b"jP  ":
        return "jp2"
    if b[:2] == b"BM":
        return "bmp"
    if b[:4] == b"%PDF":
        return "pdf"
    return None
def safe_open_image(b: bytes) ->
Optional[Image.Image]:
    try:
        im = Image.open(io.BytesIO(b))
        im.load()
        if im.mode not in ("RGB", "L"):
            im = im.convert("RGB")
        return im
    except Exception:
        return None
def wrap_ccitt_tiff(data: bytes, w: int, h:
int, compression: int = 4) -> bytes:
    """Wrap raw CCITT G3/G4 (MMR) bitstream
in a minimal TIFF container so PIL can
decode."""
    tags = [
        (256, 4, 1, w),               #
ImageWidth
        (257, 4, 1, h),               #
ImageLength
        (258, 3, 1, 1),               #
BitsPerSample
        (259, 3, 1, compression),     #
Compression (3=G3, 4=G4)
        (262, 3, 1, 0),               #
Photometric: WhiteIsZero
        (273, 4, 1, 0),               #
StripOffsets (patched below)
        (277, 3, 1, 1),               #
SamplesPerPixel
        (278, 4, 1, h),               #
RowsPerStrip
        (279, 4, 1, len(data)),       #
StripByteCounts
        (293, 4, 1, 0),               #
T6Options
    ]
    n = len(tags)
    ifd_off = 8
    data_off = ifd_off + 2 + n * 12 + 4
    out = bytearray()
    out += b"II\x2a\x00" + struct.pack("
<I", ifd_off)
    out += struct.pack("<H", n)
    for tag, typ, cnt, val in tags:
        if tag == 273:
            val = data_off
        out += struct.pack("<HHI", tag,
typ, cnt)
        if typ == 3:                      #
SHORT -> left justified
            out += struct.pack("<HH", val,
0)
        else:
            out += struct.pack("<I", val)
    out += struct.pack("<I", 0)
    out += data
    return bytes(out)
def raw_bitmap_to_image(data: bytes, w:
int, h: int, bpp: int) ->
Optional[Image.Image]:
    """Reconstruct an uncompressed IOCA /
IM1 raster."""
    try:
        if bpp == 1:
            stride = (w + 7) // 8
            need = stride * h
            if len(data) < need:
                data = data + b"\x00" *
(need - len(data))
            arr =
np.frombuffer(data[:need],
dtype=np.uint8).reshape(h, stride)
            bits = np.unpackbits(arr,
axis=1)[:, :w]
            # In AFP 1 = ink (black)
            return Image.fromarray(((1 -
bits) * 255).astype(np.uint8), mode="L")
        if bpp == 8:
            need = w * h
            if len(data) < need:
                return None
            return Image.fromarray(
                np.frombuffer(data[:need],
dtype=np.uint8).reshape(h, w), mode="L")
        if bpp == 24:
            need = w * h * 3
            if len(data) < need:
                return None
            return Image.fromarray(
                np.frombuffer(data[:need],
dtype=np.uint8).reshape(h, w, 3),
mode="RGB")
    except Exception:
        return None
    return None
#
===========================================
==========================================
# AFP (MO:DCA) parser
#
===========================================
==========================================
SF = {
    "BPG": b"\xd3\xa8\xaf", "EPG":
b"\xd3\xa9\xaf",
    "PTX": b"\xd3\xee\x9b",
    "BIM_IOCA": b"\xd3\xa8\x7b",
"EIM_IOCA": b"\xd3\xa9\x7b",
    "IID_IOCA": b"\xd3\xa6\x7b", "IPD":
b"\xd3\xee\x7b",
    "BOC": b"\xd3\xa8\x92", "OCD":
b"\xd3\xee\x92", "EOC": b"\xd3\xa9\x92",
    "BIM_IM1": b"\xd3\xa8\xfb", "EIM_IM1":
b"\xd3\xa9\xfb",
    "IID_IM1": b"\xd3\xa6\xfb", "IRD":
b"\xd3\xee\xfb",
    "BPS": b"\xd3\xa8\x5f", "EPS":
b"\xd3\xa9\x5f",
}
def iter_structured_fields(blob: bytes):
    """Yield (sfid_bytes, payload_bytes).
Tolerates junk between records."""
    i, n = 0, len(blob)
    while i < n:
        if blob[i] != 0x5A:
            i += 1
            continue
        if i + 9 > n:
            break
        length = int.from_bytes(blob[i +
1:i + 3], "big")
        if length < 8 or i + 1 + length >
n:
            i += 1
            continue
        sfid = blob[i + 3:i + 6]
        payload = blob[i + 9:i + 1 +
length]
        yield sfid, payload
        i = i + 1 + length
def decode_ptx(payload: bytes, codepage:
str) -> str:
    """Extract TRN (transparent data) text
from a PTX structured field."""
    out = []
    i, n = 0, len(payload)
    while i < n:
        if payload[i] == 0x2B and i + 1 < n
and payload[i + 1] == 0xD3:
            i += 2
            # chained control sequences
            while i + 1 < n:
                ln = payload[i]
                if ln < 2 or i + ln > n:
                    i = n
                    break
                typ = payload[i + 1]
                params = payload[i + 2:i +
ln]
                if typ in (0xDA,
0xDB):        # TRN - transparent data
                    try:
                       
out.append(params.decode(codepage,
errors="replace"))
                    except Exception:
                       
out.append(params.decode("latin-1",
errors="replace"))
                i += ln
                if i + 1 < n and payload[i]
== 0x2B and payload[i + 1] == 0xD3:
                    break
        else:
            i += 1
    return "".join(out)
def parse_ioca(data: bytes) -> List[dict]:
    """
    Parse concatenated IPD payloads (IOCA
image content).
    Returns a list of image dicts: {bytes,
width, height, bpp, comprid, res}
    """
    images: List[dict] = []
    cur = {"w": None, "h": None, "bpp": 1,
"comp": None,
           "xres": None, "yres": None,
"unitbase": 0, "chunks": []}
    i, n = 0, len(data)
    def flush():
        if cur["chunks"]:
            images.append({
                "bytes":
b"".join(cur["chunks"]),
                "width": cur["w"],
"height": cur["h"], "bpp": cur["bpp"],
                "comp": cur["comp"],
"xres": cur["xres"], "yres": cur["yres"],
                "unitbase":
cur["unitbase"],
            })
        cur["chunks"] = []
    while i < n:
        code = data[i]
        if code == 0xFE:
            if i + 4 > n:
                break
            code2 = data[i + 1]
            ln = int.from_bytes(data[i +
2:i + 4], "big")
            params = data[i + 4:i + 4 + ln]
            i += 4 + ln
            code = code2
            long_form = True
        else:
            if i + 2 > n:
                break
            ln = data[i + 1]
            params = data[i + 2:i + 2 + ln]
            i += 2 + ln
            long_form = False
        if code ==
0x91:                       # Begin Image
Content
            flush()
        elif code == 0x94 and len(params)
>= 9:  # Image Size
            cur["unitbase"] = params[0]
            cur["xres"] =
int.from_bytes(params[1:3], "big")
            cur["yres"] =
int.from_bytes(params[3:5], "big")
            cur["h"] =
int.from_bytes(params[5:7], "big")
            cur["w"] =
int.from_bytes(params[7:9], "big")
        elif code == 0x95 and
params:          # Image Encoding
            cur["comp"] = params[0]
        elif code == 0x96 and
params:          # IDE size (bits per
pixel)
            cur["bpp"] = params[0] or 1
        elif code ==
0x92:                     # Image Data
            cur["chunks"].append(params)
        elif code ==
0x93:                     # End Image
Content
            flush()
        # everything else (LUT, IDE
structure, external algorithms) is skipped
    flush()
    return images
def ioca_to_pil(rec: dict) ->
Tuple[Optional[Image.Image], str, bytes]:
    """Turn an IOCA image record into a PIL
image. Returns (image, format,
raw_bytes)."""
    raw = rec["bytes"]
    w, h, bpp = rec.get("width"),
rec.get("height"), rec.get("bpp") or 1
    fmt = sniff_image_format(raw)
    if
fmt:                                     #
JPEG / PNG / TIFF / JP2 embedded directly
        im = safe_open_image(raw)
        if im:
            return im, fmt, raw
    # try uncompressed
    if w and h:
        stride = (w + 7) // 8 if bpp == 1
else w * (bpp // 8)
        if len(raw) >= stride * h:
            im = raw_bitmap_to_image(raw,
w, h, bpp)
            if im:
                return im, "raw", raw
        # try CCITT G4 then G3
        for comp in (4, 3):
            try:
                tif = wrap_ccitt_tiff(raw,
w, h, comp)
                im = safe_open_image(tif)
                if im:
                    return im, "ccitt-g%d"
% (4 if comp == 4 else 3), raw
            except Exception:
                pass
        im = raw_bitmap_to_image(raw, w, h,
bpp)
        if im:
            return im, "raw-padded", raw
    return None, fmt or "unknown", raw
def units_to_inches(size: Optional[int],
res: Optional[int], unitbase: int) ->
Optional[float]:
    if not size or not res:
        return None
    inches = size / res
    if unitbase == 1:          # units per
centimetre
        inches = inches / 2.54 * 1.0 * 2.54
/ 2.54  # size/res is cm -> convert
        inches = (size / res) / 2.54
    return round(inches, 4)
def load_afp(path: str, codepage: str, log)
-> Doc:
    doc = Doc(path=path, kind="afp")
    with open(path, "rb") as f:
        blob = f.read()
    page_no = 0
    in_ioca = False
    ipd_buf: List[bytes] = []
    iid_ioca: Optional[bytes] = None
    in_im1 = False
    ird_buf: List[bytes] = []
    im1_dims: Optional[Tuple[int, int]] =
None
    in_oc = False
    ocd_buf: List[bytes] = []
    cur_text: List[str] = []
    idx = 0
    sf_count = 0
    def new_page():
       
doc.pages.append(PageObj(number=len(doc.pag
es) + 1))
    def add_image(im, fmt, raw, source,
pw=None, ph=None):
        nonlocal idx
        if im is None:
            return
        idx += 1
        doc.images.append(ImgObj(
            doc="?", idx=idx,
page=max(page_no, 0), source=source,
fmt=fmt,
            width=im.width,
height=im.height, sha1=sha1_bytes(raw),
            placed_w_in=pw, placed_h_in=ph,
pil=im))
    for sfid, payload in
iter_structured_fields(blob):
        sf_count += 1
        if sfid == SF["BPG"]:
            new_page()
            page_no = len(doc.pages)
            cur_text = []
        elif sfid == SF["EPG"]:
            if doc.pages:
                doc.pages[-1].text =
"".join(cur_text)
            cur_text = []
        elif sfid == SF["PTX"]:
           
cur_text.append(decode_ptx(payload,
codepage))
            cur_text.append("\n")
        # ---- IOCA ----
        elif sfid == SF["BIM_IOCA"]:
            in_ioca, ipd_buf, iid_ioca =
True, [], None
        elif sfid == SF["IID_IOCA"] and
in_ioca:
            iid_ioca = payload
        elif sfid == SF["IPD"] and in_ioca:
            ipd_buf.append(payload)
        elif sfid == SF["EIM_IOCA"] and
in_ioca:
            try:
                for rec in
parse_ioca(b"".join(ipd_buf)):
                    im, fmt, raw =
ioca_to_pil(rec)
                    pw =
units_to_inches(rec.get("width"),
rec.get("xres"), rec.get("unitbase", 0))
                    ph =
units_to_inches(rec.get("height"),
rec.get("yres"), rec.get("unitbase", 0))
                    add_image(im, fmt, raw,
"afp-ioca", pw, ph)
            except Exception as e:
                doc.notes.append("IOCA
parse issue: %s" % e)
            in_ioca, ipd_buf = False, []
        # ---- Object Container
(JPEG/PNG/TIFF wrapped as OC) ----
        elif sfid == SF["BOC"]:
            in_oc, ocd_buf = True, []
        elif sfid == SF["OCD"] and in_oc:
            ocd_buf.append(payload)
        elif sfid == SF["EOC"] and in_oc:
            raw = b"".join(ocd_buf)
            fmt = sniff_image_format(raw)
            if fmt and fmt != "pdf":
                im = safe_open_image(raw)
                add_image(im, fmt, raw,
"afp-oc")
            elif fmt == "pdf":
                doc.notes.append("Object
container holds an embedded PDF (not
expanded).")
            in_oc, ocd_buf = False, []
        # ---- legacy IM1 image ----
        elif sfid == SF["BIM_IM1"]:
            in_im1, ird_buf, im1_dims =
True, [], None
        elif sfid == SF["IID_IM1"] and
in_im1:
            try:
                if len(payload) >= 8:
                    xs =
int.from_bytes(payload[4:6], "big")
                    ys =
int.from_bytes(payload[6:8], "big")
                    im1_dims = (xs, ys)
            except Exception:
                pass
        elif sfid == SF["IRD"] and in_im1:
            ird_buf.append(payload)
        elif sfid == SF["EIM_IM1"] and
in_im1:
            raw = b"".join(ird_buf)
            if im1_dims and raw:
                im =
raw_bitmap_to_image(raw, im1_dims[0],
im1_dims[1], 1)
                add_image(im, "im1-raw",
raw, "afp-im1")
            in_im1, ird_buf = False, []
    if not doc.pages:
        doc.pages.append(PageObj(number=1,
text=""))
        doc.notes.append("No BPG (Begin
Page) structured fields found - treated as
one page.")
    if sf_count == 0:
        doc.notes.append("No AFP structured
fields (0x5A) found - is this really an AFP
file?")
    doc.rasterizable = False
    log("AFP: %d structured fields, %d
pages, %d images"
        % (sf_count, len(doc.pages),
len(doc.images)))
    return doc
#
===========================================
==========================================
# PDF loader
#
===========================================
==========================================
def load_pdf(path: str, dpi: int,
want_raster: bool, log) -> Doc:
    if not HAVE_FITZ:
        raise RuntimeError("PyMuPDF is not
installed. Run:  pip install pymupdf")
    doc = Doc(path=path, kind="pdf",
rasterizable=True)
    pdf = fitz.open(path)
    idx = 0
    for pno in range(pdf.page_count):
        page = pdf.load_page(pno)
        p = PageObj(number=pno + 1,
text=page.get_text("text") or "")
        if want_raster:
            pix = page.get_pixmap(dpi=dpi,
alpha=False)
            p.raster =
Image.frombytes("RGB", (pix.width,
pix.height), pix.samples)
        doc.pages.append(p)
        seen = set()
        for info in
page.get_images(full=True):
            xref = info[0]
            if xref in seen:
                continue
            seen.add(xref)
            try:
                d = pdf.extract_image(xref)
            except Exception:
                continue
            raw, fmt = d["image"],
d.get("ext", "bin")
            im = safe_open_image(raw)
            if im is None:
                continue
            pw = ph = None
            try:
                rects =
page.get_image_rects(xref)
                if rects:
                    r = rects[0]
                    pw, ph = round(r.width
/ 72.0, 4), round(r.height / 72.0, 4)
            except Exception:
                pass
            idx += 1
            doc.images.append(ImgObj(
                doc="?", idx=idx, page=pno
+ 1, source="pdf-xobject", fmt=fmt,
                width=im.width,
height=im.height, sha1=sha1_bytes(raw),
                placed_w_in=pw,
placed_h_in=ph, pil=im))
    pdf.close()
    log("PDF: %d pages, %d images" %
(len(doc.pages), len(doc.images)))
    return doc
def convert_afp_to_pdf(afp_path: str,
cmd_tpl: str, log) -> Optional[str]:
    """Run the user-supplied external
converter. Template uses {in} and {out}."""
    out_pdf =
os.path.join(tempfile.mkdtemp(prefix="afp2p
df_"),
                          
os.path.basename(afp_path) + ".pdf")
    cmd = cmd_tpl.replace("{in}",
afp_path).replace("{out}", out_pdf)
    log("Running converter: %s" % cmd)
    try:
        r = subprocess.run(cmd, shell=True,
capture_output=True, timeout=600)
        if r.returncode != 0:
            log("Converter failed (rc=%d):
%s" % (r.returncode,
r.stderr.decode(errors="replace")[:400]))
            return None
        if os.path.exists(out_pdf) and
os.path.getsize(out_pdf) > 0:
            return out_pdf
        log("Converter produced no output
file.")
    except Exception as e:
        log("Converter error: %s" % e)
    return None
def load_document(path: str, dpi: int,
codepage: str, afp_cmd: str, log) -> Doc:
    ext = os.path.splitext(path)[1].lower()
    if ext == ".pdf":
        return load_pdf(path, dpi, True,
log)
    # AFP family
    doc = load_afp(path, codepage, log)
    if afp_cmd.strip():
        pdf_path = convert_afp_to_pdf(path,
afp_cmd.strip(), log)
        if pdf_path:
            try:
                rendered =
load_pdf(pdf_path, dpi, True, log)
                # keep AFP-extracted images
(they are the true objects),
                # but take page rasters +
text from the converted PDF
                doc.pages = rendered.pages
                doc.rasterizable = True
                doc.notes.append("Page
rasters/text taken from external AFP->PDF
conversion.")
                if not doc.images:
                    doc.images =
rendered.images
            except Exception as e:
                log("Could not load
converted PDF: %s" % e)
    return doc
#
===========================================
==========================================
# Image similarity - scale / size / aspectratio invariant
#
===========================================
==========================================
def _gray_np(im: Image.Image, size:
Tuple[int, int]) -> np.ndarray:
    g =
ImageOps.autocontrast(im.convert("L")).resi
ze(size, Image.LANCZOS)
    return np.asarray(g, dtype=np.float32)
def _dct2(a: np.ndarray) -> np.ndarray:
    n = a.shape[0]
    k = np.arange(n)
    m = np.cos(np.pi * (2 * k[:, None] + 1)
* k[None, :] / (2 * n))
    m[:, 0] *= 1 / np.sqrt(2)
    return m.T @ a @ m
def phash(im: Image.Image) -> int:
    a = _gray_np(im, (32, 32))
    d = _dct2(a)[:8, :8].flatten()
    med = np.median(d[1:])
    bits = (d > med).astype(np.uint8)
    v = 0
    for b in bits:
        v = (v << 1) | int(b)
    return v
def dhash(im: Image.Image) -> int:
    a = _gray_np(im, (9, 8))
    bits = (a[:, 1:] > a[:, :-1]).flatten()
    v = 0
    for b in bits:
        v = (v << 1) | int(b)
    return v
def ahash(im: Image.Image) -> int:
    a = _gray_np(im, (8, 8))
    bits = (a > a.mean()).flatten()
    v = 0
    for b in bits:
        v = (v << 1) | int(b)
    return v
def hash_sim(h1: int, h2: int, bits: int =
64) -> float:
    return 1.0 - (bin(h1 ^ h2).count("1") /
bits)
def _blur(a: np.ndarray, radius: float =
2.0) -> np.ndarray:
    if HAVE_CV2:
        return cv2.GaussianBlur(a, (11,
11), 1.5)
    im =
Image.fromarray(a.astype(np.uint8)).filter(
ImageFilter.GaussianBlur(radius))
    return np.asarray(im, dtype=np.float32)
def ssim(a: np.ndarray, b: np.ndarray) ->
float:
    C1, C2 = (0.01 * 255) ** 2, (0.03 *
255) ** 2
    mu1, mu2 = _blur(a), _blur(b)
    s1 = _blur(a * a) - mu1 * mu1
    s2 = _blur(b * b) - mu2 * mu2
    s12 = _blur(a * b) - mu1 * mu2
    num = (2 * mu1 * mu2 + C1) * (2 * s12 +
C2)
    den = (mu1 ** 2 + mu2 ** 2 + C1) * (s1
+ s2 + C2)
    m = num / np.maximum(den, 1e-9)
    return float(np.clip(m.mean(), -1, 1))
def orb_score(a: Image.Image, b:
Image.Image) -> Optional[float]:
    """Scale / rotation robust similarity
via ORB + RANSAC homography inliers."""
    if not HAVE_CV2:
        return None
    try:
        def prep(im):
            g = np.asarray(im.convert("L"))
            h, w = g.shape[:2]
            s = 640.0 / max(h, w)
            if s < 1.0:
                g = cv2.resize(g, (int(w *
s), int(h * s)),
interpolation=cv2.INTER_AREA)
            return g
        g1, g2 = prep(a), prep(b)
        orb =
cv2.ORB_create(nfeatures=1500)
        k1, d1 = orb.detectAndCompute(g1,
None)
        k2, d2 = orb.detectAndCompute(g2,
None)
        if d1 is None or d2 is None or
len(k1) < 8 or len(k2) < 8:
            return None
        bf =
cv2.BFMatcher(cv2.NORM_HAMMING)
        raw = bf.knnMatch(d1, d2, k=2)
        good = [m for m, n in (p for p in
raw if len(p) == 2) if m.distance < 0.75 *
n.distance]
        if len(good) < 8:
            return len(good) / 20.0
        src = np.float32([k1[m.queryIdx].pt
for m in good]).reshape(-1, 1, 2)
        dst = np.float32([k2[m.trainIdx].pt
for m in good]).reshape(-1, 1, 2)
        H, mask = cv2.findHomography(src,
dst, cv2.RANSAC, 5.0)
        if mask is None:
            return len(good) / 40.0
        inl = int(mask.sum())
        denom = max(12, min(len(k1),
len(k2), 300) * 0.25)
        return float(min(1.0, inl / denom))
    except Exception:
        return None
class ImgFeat:
    """Cached, scale-normalised features
for one image."""
    def __init__(self, obj: ImgObj):
        self.obj = obj
        im = obj.pil
        self.ph = phash(im)
        self.dh = dhash(im)
        self.ah = ahash(im)
        # aspect-ignoring square
normalisation -> makes SSIM ratio-invariant
        self.norm = _gray_np(im, (256,
256))
def compare_images(fa: ImgFeat, fb:
ImgFeat) -> dict:
    s_hash = (hash_sim(fa.ph, fb.ph) * 0.5
+
              hash_sim(fa.dh, fb.dh) * 0.3
+
              hash_sim(fa.ah, fb.ah) * 0.2)
    s_ssim = max(0.0, ssim(fa.norm,
fb.norm))
    s_orb = orb_score(fa.obj.pil,
fb.obj.pil)
    if s_orb is None:
        score = 0.5 * s_hash + 0.5 * s_ssim
    else:
        score = 0.35 * s_hash + 0.35 *
s_ssim + 0.30 * s_orb
    return {
        "hash_similarity": round(s_hash,
4),
        "normalized_ssim": round(s_ssim,
4),
        "orb_inlier_score": None if s_orb
is None else round(s_orb, 4),
        "combined_score":
round(float(score), 4),
    }
def geometry_report(a: ImgObj, b: ImgObj,
ar_tol: float, sc_tol: float) ->
Tuple[List[str], dict]:
    flags: List[str] = []
    sx = b.width / a.width if a.width else
0
    sy = b.height / a.height if a.height
else 0
    ar_a, ar_b = a.aspect, b.aspect
    ar_delta = abs(ar_b - ar_a) / ar_a if
ar_a else 0
    if a.width == b.width and a.height ==
b.height:
        flags.append("same_pixel_size")
    else:
       
flags.append("different_pixel_size")
    if abs(sx - 1) > sc_tol or abs(sy - 1)
> sc_tol:
        flags.append("resized")
    if ar_delta > ar_tol:
       
flags.append("aspect_ratio_changed")
    if abs(sx - sy) > sc_tol:
        flags.append("non_uniform_scale")
    placed = {}
    if a.placed_w_in and b.placed_w_in and
a.placed_h_in and b.placed_h_in:
        psx = b.placed_w_in / a.placed_w_in
        psy = b.placed_h_in / a.placed_h_in
        placed = {"placed_scale_x":
round(psx, 4), "placed_scale_y": round(psy,
4)}
        if abs(psx - 1) > sc_tol or abs(psy
- 1) > sc_tol:
           
flags.append("placed_size_changed")
        if abs(psx - psy) > sc_tol:
           
flags.append("placed_aspect_changed")
    geo = {
        "scale_x": round(sx, 4), "scale_y":
round(sy, 4),
        "aspect_a": round(ar_a, 5),
"aspect_b": round(ar_b, 5),
        "aspect_delta_pct": round(ar_delta
* 100, 2),
        "pixels_a": f"
{a.width}x{a.height}", "pixels_b": f"
{b.width}x{b.height}",
    }
    geo.update(placed)
    return flags, geo
#
===========================================
==========================================
# Page raster diff
#
===========================================
==========================================
def page_raster_diff(a: Image.Image, b:
Image.Image) -> Tuple[float, Image.Image,
float]:
    """Return (ssim, heatmap overlay image,
changed_pixel_pct)."""
    w = min(a.width, b.width, 1400)
    ha = int(a.height * (w / a.width))
    hb = int(b.height * (w / b.width))
    h = min(ha, hb)
    A = a.convert("RGB").resize((w, h),
Image.LANCZOS)
    B = b.convert("RGB").resize((w, h),
Image.LANCZOS)
    ga = np.asarray(A.convert("L"),
dtype=np.float32)
    gb = np.asarray(B.convert("L"),
dtype=np.float32)
    s = ssim(ga, gb)
    d = np.abs(ga - gb)
    mask = d > 32
    pct = float(mask.mean() * 100)
    over = np.asarray(A).copy()
    over[mask] = (255, 0, 0)
    heat = Image.fromarray(over)
    return s, heat, pct
#
===========================================
==========================================
# Text diff
#
===========================================
==========================================
def text_compare(ta: str, tb: str,
max_lines: int = 200) -> dict:
    na = [l.rstrip() for l in
ta.splitlines() if l.strip()]
    nb = [l.rstrip() for l in
tb.splitlines() if l.strip()]
    ratio = difflib.SequenceMatcher(None,
"\n".join(na), "\n".join(nb)).ratio()
    diff = list(difflib.unified_diff(na,
nb, "A", "B", lineterm="", n=1))
[:max_lines]
    return {
        "similarity": round(ratio, 4),
        "lines_a": len(na), "lines_b":
len(nb),
        "diff": diff,
        "identical": ratio >= 0.9999,
    }
#
===========================================
==========================================
# Comparison engine
#
===========================================
==========================================
def thumb_b64(im: Image.Image, box: int =
260) -> str:
    t = im.copy()
    t.thumbnail((box, box), Image.LANCZOS)
    if t.mode not in ("RGB", "L"):
        t = t.convert("RGB")
    buf = io.BytesIO()
    t.convert("RGB").save(buf, "PNG",
optimize=True)
    return "data:image/png;base64," +
base64.b64encode(buf.getvalue()).decode()
def run_comparison(path_a: str, path_b:
str, out_dir: str, opts: dict, log) ->
dict:
    os.makedirs(out_dir, exist_ok=True)
    assets = os.path.join(out_dir,
"assets")
    os.makedirs(assets, exist_ok=True)
    dpi = int(opts["dpi"])
    thr = float(opts["threshold"])
    ar_tol = float(opts["aspect_tol"])
    sc_tol = float(opts["scale_tol"])
    log("Loading A: %s" % path_a)
    A = load_document(path_a, dpi,
opts["codepage"], opts["afp_cmd"], log)
    log("Loading B: %s" % path_b)
    B = load_document(path_b, dpi,
opts["codepage"], opts["afp_cmd"], log)
    for o in A.images:
        o.doc = "A"
    for o in B.images:
        o.doc = "B"
    mode = "%s-vs-%s" % (A.kind.upper(),
B.kind.upper())
    log("Mode: %s" % mode)
    # ---------- save image assets --------
--
    for d, tag in ((A, "a"), (B, "b")):
        for o in d.images:
            rel =
"assets/%s_p%03d_i%03d.png" % (tag, o.page,
o.idx)
            try:
               
o.pil.convert("RGB").save(os.path.join(out_
dir, rel))
                o.asset = rel
            except Exception:
                pass
    # ---------- image matching (scale /
ratio invariant) ----------
    log("Extracting image features: A=%d
B=%d" % (len(A.images), len(B.images)))
    FA = [ImgFeat(o) for o in A.images]
    FB = [ImgFeat(o) for o in B.images]
    pairs = []
    if FA and FB:
        log("Scoring %d x %d image
pairs..." % (len(FA), len(FB)))
        score_rows = []
        for i, fa in enumerate(FA):
            row = []
            for j, fb in enumerate(FB):
                if fa.obj.sha1 ==
fb.obj.sha1:
                   
row.append(({"hash_similarity": 1.0,
"normalized_ssim": 1.0,
                                
"orb_inlier_score": 1.0, "combined_score":
1.0}, 1.0))
                else:
                    r = compare_images(fa,
fb)
                    row.append((r,
r["combined_score"]))
            score_rows.append(row)
        used_a, used_b = set(), set()
        flat = []
        for i in range(len(FA)):
            for j in range(len(FB)):
                flat.append((score_rows[i]
[j][1], i, j))
        flat.sort(reverse=True)
        for sc, i, j in flat:
            if sc < thr or i in used_a or j
in used_b:
                continue
            used_a.add(i)
            used_b.add(j)
            pairs.append((i, j,
score_rows[i][j][0]))
    else:
        used_a, used_b = set(), set()
    image_results = []
    for i, j, scores in pairs:
        a, b = FA[i].obj, FB[j].obj
        flags, geo = geometry_report(a, b,
ar_tol, sc_tol)
        identical_bytes = a.sha1 == b.sha1
        if identical_bytes:
            status = "IDENTICAL"
        elif "aspect_ratio_changed" in
flags or "non_uniform_scale" in flags:
            status = "ASPECT_CHANGED"
        elif "resized" in flags or
"placed_size_changed" in flags:
            status = "RESIZED"
        elif scores["combined_score"] >=
0.95:
            status = "MATCH"
        else:
            status = "CONTENT_DIFFERS"
        image_results.append({
            "status": status, "flags":
flags, "scores": scores,
            "identical_bytes":
identical_bytes,
            "geometry": geo, "a": a.meta(),
"b": b.meta(),
            "_thumb_a": thumb_b64(a.pil),
"_thumb_b": thumb_b64(b.pil),
        })
    for i, fa in enumerate(FA):
        if i not in used_a:
            image_results.append({
                "status": "ONLY_IN_A",
"flags": ["missing_in_b"], "scores": {},
                "identical_bytes": False,
"geometry": {},
                "a": fa.obj.meta(), "b":
None,
                "_thumb_a":
thumb_b64(fa.obj.pil), "_thumb_b": None})
    for j, fb in enumerate(FB):
        if j not in used_b:
            image_results.append({
                "status": "ONLY_IN_B",
"flags": ["missing_in_a"], "scores": {},
                "identical_bytes": False,
"geometry": {},
                "a": None, "b":
fb.obj.meta(),
                "_thumb_a": None,
"_thumb_b": thumb_b64(fb.obj.pil)})
    # ---------- page comparison ----------
    page_results = []
    npages = max(len(A.pages),
len(B.pages))
    can_raster = A.rasterizable and
B.rasterizable
    for k in range(npages):
        pa = A.pages[k] if k < len(A.pages)
else None
        pb = B.pages[k] if k < len(B.pages)
else None
        entry = {"page": k + 1,
                 "present_in_a": pa is not
None, "present_in_b": pb is not None}
        if pa and pb:
            entry["text"] =
text_compare(pa.text, pb.text)
            if can_raster and pa.raster is
not None and pb.raster is not None:
                try:
                    s, heat, pct =
page_raster_diff(pa.raster, pb.raster)
                    rel =
"assets/page_%03d_diff.png" % (k + 1)
                   
heat.save(os.path.join(out_dir, rel))
                    entry["raster"] = {
                        "ssim": round(s,
4),
                       
"changed_pixels_pct": round(pct, 3),
                        "diff_image": rel,
                    }
                    entry["_thumb_a"] =
thumb_b64(pa.raster, 380)
                    entry["_thumb_b"] =
thumb_b64(pb.raster, 380)
                    entry["_thumb_d"] =
thumb_b64(heat, 380)
                except Exception as e:
                    entry["raster_error"] =
str(e)
            log("Page %d: text=%.3f%s" % (
                k + 1, entry["text"]
["similarity"],
                (" ssim=%.3f" %
entry["raster"]["ssim"]) if "raster" in
entry else ""))
        page_results.append(entry)
    # ---------- summary ----------
    sims = [p["text"]["similarity"] for p
in page_results if "text" in p]
    ssims = [p["raster"]["ssim"] for p in
page_results if "raster" in p]
    counts: Dict[str, int] = {}
    for r in image_results:
        counts[r["status"]] =
counts.get(r["status"], 0) + 1
    problem = (counts.get("ONLY_IN_A", 0) +
counts.get("ONLY_IN_B", 0) +
              
counts.get("CONTENT_DIFFERS", 0) +
counts.get("ASPECT_CHANGED", 0) +
               counts.get("RESIZED", 0))
    text_ok = (not sims) or min(sims) >=
0.999
    pages_ok = len(A.pages) == len(B.pages)
    if problem == 0 and text_ok and
pages_ok:
        verdict = "IDENTICAL"
    elif problem == 0 and (not sims or
min(sims) >= 0.95) and pages_ok:
        verdict = "EQUIVALENT (minor
differences)"
    else:
        verdict = "DIFFERENT"
    summary = {
        "mode": mode,
        "verdict": verdict,
        "pages_a": len(A.pages), "pages_b":
len(B.pages),
        "page_count_match": pages_ok,
        "avg_text_similarity":
round(sum(sims) / len(sims), 4) if sims
else None,
        "min_text_similarity":
round(min(sims), 4) if sims else None,
        "avg_page_ssim": round(sum(ssims) /
len(ssims), 4) if ssims else None,
        "raster_compared": bool(ssims),
        "images_a": len(A.images),
"images_b": len(B.images),
        "image_status_counts": counts,
        "orb_enabled": HAVE_CV2,
        "match_threshold": thr,
        "aspect_tolerance": ar_tol,
        "scale_tolerance": sc_tol,
    }
    report = {
        "tool": "doc_compare.py",
        "generated_utc":
datetime.datetime.utcnow().isoformat() +
"Z",
        "file_a": A.meta(),
        "file_b": B.meta(),
        "summary": summary,
        "pages": page_results,
        "images": image_results,
    }
    # ---------- write outputs ----------
    json_path = os.path.join(out_dir,
"report.json")
    clean = json.loads(json.dumps(report,
default=str))
    strip_thumbs(clean)
    with open(json_path, "w",
encoding="utf-8") as f:
        json.dump(clean, f, indent=2,
ensure_ascii=False)
    html_path = os.path.join(out_dir,
"report.html")
    with open(html_path, "w",
encoding="utf-8") as f:
        f.write(build_html(report))
    log("JSON written: %s" % json_path)
    log("HTML written: %s" % html_path)
    report["_json_path"] = json_path
    report["_html_path"] = html_path
    return report
def strip_thumbs(node):
    if isinstance(node, dict):
        for k in [k for k in node if
k.startswith("_thumb")]:
            node.pop(k)
        for v in node.values():
            strip_thumbs(v)
    elif isinstance(node, list):
        for v in node:
            strip_thumbs(v)
#
===========================================
==========================================
# HTML report
#
===========================================
==========================================
CSS = """
:root{--bg:#0f1115;--card:#171a21;--
line:#262b36;--txt:#e6e9ef;--dim:#98a2b3;
--ok:#22c55e;--warn:#f59e0b;--bad:#ef4444;-
-info:#3b82f6;}
*{box-sizing:border-box}
body{margin:0;background:var(--
bg);color:var(--txt);
font:14px/1.5 -apple-system,Segoe
UI,Roboto,Helvetica,Arial,sans-serif}
.wrap{max-width:1200px;margin:0
auto;padding:28px 20px 80px}
h1{font-size:22px;margin:0 0 4px} h2{fontsize:17px;margin:34px 0 12px;
padding-bottom:8px;border-bottom:1px solid
var(--line)}
.sub{color:var(--dim);fontsize:13px;margin-bottom:22px}
.card{background:var(--card);border:1px
solid var(--line);border-radius:10px;
padding:14px 16px;margin-bottom:12px}
.grid{display:grid;grid-templatecolumns:repeat(autofit,minmax(180px,1fr));gap:10px}
.kv{font-size:12px;color:var(--dim)} .kv
b{display:block;color:var(--txt);
font-size:18px;font-weight:600;margintop:2px}
.badge{display:inline-block;padding:2px
9px;border-radius:20px;font-size:11px;
font-weight:600;letter-spacing:.03em}
.b-IDENTICAL,.bMATCH{background:rgba(34,197,94,.15);color:
var(--ok)}
.bRESIZED{background:rgba(59,130,246,.15);col
or:var(--info)}
.bASPECT_CHANGED{background:rgba(245,158,11,.
15);color:var(--warn)}
.b-CONTENT_DIFFERS,.b-ONLY_IN_A,.bONLY_IN_B{background:rgba(239,68,68,.15);co
lor:var(--bad)}
.v-IDENTICAL{color:var(--ok)} .vDIFFERENT{color:var(--bad)}
table{width:100%;bordercollapse:collapse;font-size:13px}
th,td{text-align:left;padding:8px
10px;border-bottom:1px solid var(--
line);vertical-align:top}
th{color:var(--dim);font-weight:600;fontsize:12px;text-transform:uppercase;letterspacing:.04em}
img.t{max-width:170px;max-
height:170px;border-radius:6px;border:1px
solid var(--line);
background:#fff}
img.p{max-width:100%;borderradius:6px;border:1px solid var(--
line);background:#fff}
.trio{display:grid;grid-templatecolumns:1fr 1fr 1fr;gap:10px}
.trio div{font-size:11px;color:var(--
dim);text-align:center}
pre{background:#0b0d11;border:1px solid
var(--line);border-radius:8px;padding:10px;
overflow:auto;font-size:12px;maxheight:280px}
.add{color:var(--ok)} .del{color:var(--
bad)} .hdr{color:var(--info)}
.flag{display:inlineblock;background:#20242e;color:var(--
dim);border-radius:4px;
padding:1px 6px;margin:1px 3px 1px 0;fontsize:11px}
.muted{color:var(--dim);font-size:12px}
"""
def _img_tag(src: Optional[str], cls: str =
"t") -> str:
    return '<img class="%s" src="%s">' %
(cls, src) if src else '<span
class="muted">-</span>'
def build_html(rep: dict) -> str:
    s = rep["summary"]
    A, B = rep["file_a"], rep["file_b"]
    o: List[str] = []
    o.append("<!doctype html><html><head>
<meta charset='utf-8'>")
    o.append("<meta name='viewport'
content='width=device-width,initialscale=1'>")
    o.append("<title>Document comparison
report</title><style>%s</style></head>
<body><div class='wrap'>" % CSS)
    vclass = "v-IDENTICAL" if s["verdict"]
== "IDENTICAL" else (
        "v-DIFFERENT" if s["verdict"] ==
"DIFFERENT" else "")
    o.append("<h1>Document Comparison
&mdash; <span class='%s'>%s</span></h1>" %
             (vclass,
html.escape(s["verdict"])))
    o.append("<div class='sub'>%s
&nbsp;|&nbsp; generated %s &nbsp;|&nbsp;
ORB feature matching: %s</div>"
             % (html.escape(s["mode"]),
rep["generated_utc"], "on" if
s["orb_enabled"] else "off (install opencvpython)"))
    # files
    o.append("<div class='card'><table><tr>
<th></th><th>File A</th><th>File B</th>
</tr>")
    for label, key in (("Name",
"file_name"), ("Type", "kind"), ("Pages",
"pages"),
                       ("Images",
"images"), ("Size (bytes)", "size_bytes")):
        o.append("<tr><td
class='muted'>%s</td><td>%s</td><td>%s</td>
</tr>"
                 % (label,
html.escape(str(A.get(key))),
html.escape(str(B.get(key)))))
    o.append("</table></div>")
    notes = (A.get("notes") or []) +
(B.get("notes") or [])
    if notes:
        o.append("<div class='card
muted'>Notes: " +
                 " &middot;
".join(html.escape(str(n)) for n in notes)
+ "</div>")
    # summary tiles
    o.append("<div class='card'><div
class='grid'>")
    tiles = [
        ("Avg text similarity", "-" if
s["avg_text_similarity"] is None else
"%.1f%%" % (s["avg_text_similarity"] *
100)),
        ("Min text similarity", "-" if
s["min_text_similarity"] is None else
"%.1f%%" % (s["min_text_similarity"] *
100)),
        ("Avg page SSIM", "-" if
s["avg_page_ssim"] is None else "%.3f" %
s["avg_page_ssim"]),
        ("Pages A / B", "%d / %d" %
(s["pages_a"], s["pages_b"])),
        ("Images A / B", "%d / %d" %
(s["images_a"], s["images_b"])),
    ]
    for st, cnt in
sorted(s["image_status_counts"].items()):
        tiles.append(("Images " +
st.replace("_", " ").title(), str(cnt)))
    for k, v in tiles:
        o.append("<div
class='kv'>%s<b>%s</b></div>" %
(html.escape(k), html.escape(v)))
    o.append("</div></div>")
    # images
    o.append("<h2>Image objects (scale /
size / aspect-ratio aware)</h2>")
    if not rep["images"]:
        o.append("<div class='card
muted'>No embedded images found in either
document.</div>")
    else:
        o.append("<div class='card'><table>
<tr><th>Status</th><th>A</th><th>B</th>"
                 "<th>Geometry</th>
<th>Scores</th></tr>")
        order = {"CONTENT_DIFFERS": 0,
"ASPECT_CHANGED": 1, "ONLY_IN_A": 2,
"ONLY_IN_B": 3,
                 "RESIZED": 4, "MATCH": 5,
"IDENTICAL": 6}
        for r in sorted(rep["images"],
key=lambda x: order.get(x["status"], 9)):
            a, b, g, sc = r["a"], r["b"],
r["geometry"], r["scores"]
            o.append("<tr>")
            o.append("<td><span
class='badge b-%s'>%s</span><div
style='margin-top:6px'>%s</div></td>"
                     % (r["status"],
r["status"].replace("_", " "),
                        "".join("<span
class='flag'>%s</span>" % html.escape(f)
for f in r["flags"])))
            for side, meta in (("a", a),
("b", b)):
                if meta:
                    o.append("<td>%s<div
class='muted'>p%s &middot; %sx%s &middot;
%s%s</div></td>" % (
                       
_img_tag(r.get("_thumb_" + side)),
meta["page"],
                        meta["width_px"],
meta["height_px"], meta["format"],
                        (" &middot;
%.2f&times;%.2f in" %
(meta["placed_width_in"],
meta["placed_height_in"]))
                        if
meta.get("placed_width_in") and
meta.get("placed_height_in") else ""))
                else:
                    o.append("<td
class='muted'>&mdash;</td>")
            if g:
                o.append("<td
class='muted'>scale %.3f&times; /
%.3f&times;<br>aspect %.3f &rarr; %.3f "
                         "(&Delta;
%.1f%%)%s</td>" % (
                             g["scale_x"],
g["scale_y"], g["aspect_a"], g["aspect_b"],
                            
g["aspect_delta_pct"],
                             "<br>placed
%.3f&times; / %.3f&times;" %
(g["placed_scale_x"], g["placed_scale_y"])
                             if
"placed_scale_x" in g else ""))
            else:
                o.append("<td
class='muted'>&mdash;</td>")
            if sc:
                o.append("<td
class='muted'>combined <b
style='color:var(--txt)'>%.3f</b><br>"
                         "hash %.3f
&middot; ssim %.3f &middot; orb %s</td>" %
(
                            
sc["combined_score"],
sc["hash_similarity"],
sc["normalized_ssim"],
                             "-" if
sc["orb_inlier_score"] is None else "%.3f"
% sc["orb_inlier_score"]))
            else:
                o.append("<td
class='muted'>&mdash;</td>")
            o.append("</tr>")
        o.append("</table></div>")
    # pages
    o.append("<h2>Pages</h2>")
    for p in rep["pages"]:
        o.append("<div class='card'>")
        head = "Page %d" % p["page"]
        if not p["present_in_a"]:
            head += " &mdash; <span
class='badge b-ONLY_IN_B'>only in B</span>"
        elif not p["present_in_b"]:
            head += " &mdash; <span
class='badge b-ONLY_IN_A'>only in A</span>"
        o.append("<div style='fontweight:600;margin-bottom:8px'>%s</div>" %
head)
        t = p.get("text")
        if t:
            o.append("<div
class='muted'>text similarity <b
style='color:var(--txt)'>%.2f%%</b> "
                     "&middot; lines %d
&rarr; %d%s</div>" % (
                         t["similarity"] *
100, t["lines_a"], t["lines_b"],
                         " &middot; raster
SSIM <b style='color:var(--txt)'>%.3f</b> "
                         "&middot; %.2f%%
pixels changed" % (
                             p["raster"]
["ssim"], p["raster"]
["changed_pixels_pct"])
                         if "raster" in p
else ""))
        if "_thumb_d" in p:
            o.append("<div class='trio'
style='margin-top:10px'>"
                     "<div>%s<div>A</div>
</div><div>%s<div>B</div></div>"
                     "<div>%s<div>diff (red
= changed)</div></div></div>" % (
                        
_img_tag(p["_thumb_a"], "p"),
_img_tag(p["_thumb_b"], "p"),
                        
_img_tag(p["_thumb_d"], "p")))
        if t and t["diff"]:
            lines = []
            for ln in t["diff"]:
                cls = "add" if
ln.startswith("+") else ("del" if
ln.startswith("-") else
                                           
             ("hdr" if ln.startswith("@")
else ""))
                lines.append("<span
class='%s'>%s</span>" % (cls,
html.escape(ln)))
            o.append("<pre>%s</pre>" %
"\n".join(lines))
        elif t and t["identical"]:
            o.append("<div class='muted'
style='margin-top:8px'>Text is identical.
</div>")
        o.append("</div>")
    o.append("</div></body></html>")
    return "".join(o)
#
===========================================
==========================================
# Tkinter UI
#
===========================================
==========================================
class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("PDF / AFP Comparison
Tool")
        self.geometry("880x680")
        self.minsize(760, 600)
        self.q: "queue.Queue[tuple]" =
queue.Queue()
        self.file_a = tk.StringVar()
        self.file_b = tk.StringVar()
        self.out_dir = tk.StringVar()
        self.dpi = tk.IntVar(value=150)
        self.threshold =
tk.DoubleVar(value=0.65)
        self.aspect_tol =
tk.DoubleVar(value=0.02)
        self.scale_tol =
tk.DoubleVar(value=0.02)
        self.codepage =
tk.StringVar(value="cp500")
        self.afp_cmd =
tk.StringVar(value="")
        self.last_html: Optional[str] =
None
        self._build()
        self.after(100, self._pump)
        self._check_deps()
    # ---------- layout ----------
    def _build(self):
        pad = dict(padx=10, pady=6)
        f = ttk.LabelFrame(self,
text="Files")
        f.pack(fill="x", **pad)
        self._row(f, 0, "File A (.pdf /
.afp)", self.file_a, self._pick_a)
        self._row(f, 1, "File B (.pdf /
.afp)", self.file_b, self._pick_b)
        self._row(f, 2, "Result folder",
self.out_dir, self._pick_out, folder=True)
        f.columnconfigure(1, weight=1)
        g = ttk.LabelFrame(self,
text="Options")
        g.pack(fill="x", **pad)
        ttk.Label(g, text="Render
DPI").grid(row=0, column=0, sticky="w",
padx=8, pady=4)
        ttk.Spinbox(g, from_=72, to=400,
increment=25, textvariable=self.dpi,
width=7)\
            .grid(row=0, column=1,
sticky="w")
        ttk.Label(g, text="Image match
threshold").grid(row=0, column=2,
sticky="w", padx=8)
        ttk.Spinbox(g, from_=0.3, to=0.99,
increment=0.05,
textvariable=self.threshold,
                    width=7,
format="%.2f").grid(row=0, column=3,
sticky="w")
        ttk.Label(g, text="Aspect
tol").grid(row=0, column=4, sticky="w",
padx=8)
        ttk.Spinbox(g, from_=0.0, to=0.5,
increment=0.01,
textvariable=self.aspect_tol,
                    width=7,
format="%.2f").grid(row=0, column=5,
sticky="w")
        ttk.Label(g, text="Scale
tol").grid(row=0, column=6, sticky="w",
padx=8)
        ttk.Spinbox(g, from_=0.0, to=0.5,
increment=0.01,
textvariable=self.scale_tol,
                    width=7,
format="%.2f").grid(row=0, column=7,
sticky="w", padx=(0, 8))
        ttk.Label(g, text="AFP code
page").grid(row=1, column=0, sticky="w",
padx=8, pady=4)
        ttk.Combobox(g,
textvariable=self.codepage, width=10,
values=[
            "cp500", "cp037", "cp1140",
"cp1141", "cp273", "cp875", "latin-1",
"utf-8"
        ]).grid(row=1, column=1,
sticky="w")
        ttk.Label(g, text="AFP→PDF
converter (optional, for page raster
diff)")\
            .grid(row=2, column=0,
columnspan=3, sticky="w", padx=8)
        ttk.Entry(g,
textvariable=self.afp_cmd).grid(
            row=3, column=0, columnspan=8,
sticky="ew", padx=8, pady=(0, 8))
        ttk.Label(g, text='use {in} and
{out} placeholders, e.g.  afp2pdf.exe -i "
{in}" -o "{out}"',
                 
foreground="#777").grid(row=4, column=0,
columnspan=8, sticky="w", padx=8, pady=(0,
6))
        g.columnconfigure(7, weight=1)
        b = ttk.Frame(self)
        b.pack(fill="x", **pad)
        self.run_btn = ttk.Button(b,
text="Compare", command=self._run)
        self.run_btn.pack(side="left")
        self.open_btn = ttk.Button(b,
text="Open HTML report",
command=self._open, state="disabled")
        self.open_btn.pack(side="left",
padx=6)
        self.folder_btn = ttk.Button(b,
text="Open result folder",
command=self._open_folder,
                                    
state="disabled")
        self.folder_btn.pack(side="left")
        self.prog = ttk.Progressbar(b,
mode="indeterminate", length=180)
        self.prog.pack(side="right")
        lf = ttk.LabelFrame(self,
text="Log")
        lf.pack(fill="both", expand=True,
**pad)
        self.log_box = ScrolledText(lf,
height=16, font=("Consolas", 9),
wrap="word")
        self.log_box.pack(fill="both",
expand=True, padx=6, pady=6)
    def _row(self, parent, r, label, var,
cmd, folder=False):
        ttk.Label(parent,
text=label).grid(row=r, column=0,
sticky="w", padx=8, pady=5)
        ttk.Entry(parent,
textvariable=var).grid(row=r, column=1,
sticky="ew", padx=6)
        ttk.Button(parent, text="Browse…"
if not folder else "Choose…", command=cmd)\
            .grid(row=r, column=2, padx=8)
    # ---------- actions ----------
    def _check_deps(self):
        self.log("PDF engine (PyMuPDF): %s"
% ("OK" if HAVE_FITZ else "MISSING -> pip
install pymupdf"))
        self.log("OpenCV (ORB matching):
%s" % ("OK" if HAVE_CV2 else "missing ->
pip install opencv-python (recommended)"))
        self.log("AFP parsing: built-in (no
external tool needed for text/image
compare)")
        self.log("-" * 70)
    def _ask(self, var):
        p =
filedialog.askopenfilename(filetypes=[
            ("PDF / AFP", "*.pdf *.afp
*.afpds *.lst *.prn *.ovl *.pseg *.mda
*.out"),
            ("PDF", "*.pdf"), ("AFP",
"*.afp *.afpds"), ("All files", "*.*")])
        if p:
            var.set(p)
            if not self.out_dir.get():
               
self.out_dir.set(os.path.join(os.path.dirna
me(p), "compare_result"))
    def _pick_a(self):
        self._ask(self.file_a)
    def _pick_b(self):
        self._ask(self.file_b)
    def _pick_out(self):
        p = filedialog.askdirectory()
        if p:
            self.out_dir.set(p)
    def log(self, msg):
        self.log_box.insert("end", str(msg)
+ "\n")
        self.log_box.see("end")
    def _run(self):
        a, b, o =
self.file_a.get().strip(),
self.file_b.get().strip(),
self.out_dir.get().strip()
        if not (a and b and o):
            messagebox.showwarning("Missing
input", "Choose both files and a result
folder.")
            return
        for p in (a, b):
            if not os.path.exists(p):
                messagebox.showerror("Not
found", p)
                return
        if not HAVE_FITZ and
(a.lower().endswith(".pdf") or
b.lower().endswith(".pdf")):
            messagebox.showerror("Missing
dependency", "PyMuPDF is required for
PDF.\n\npip install pymupdf")
            return
        opts = {
            "dpi": self.dpi.get(),
"threshold": self.threshold.get(),
            "aspect_tol":
self.aspect_tol.get(), "scale_tol":
self.scale_tol.get(),
            "codepage":
self.codepage.get(), "afp_cmd":
self.afp_cmd.get(),
        }
       
self.run_btn.config(state="disabled")
       
self.open_btn.config(state="disabled")
       
self.folder_btn.config(state="disabled")
        self.prog.start(12)
        self.log_box.delete("1.0", "end")
       
threading.Thread(target=self._worker, args=
(a, b, o, opts), daemon=True).start()
    def _worker(self, a, b, o, opts):
        try:
            rep = run_comparison(a, b, o,
opts, lambda m: self.q.put(("log", m)))
            self.q.put(("done", rep))
        except Exception:
            self.q.put(("error",
traceback.format_exc()))
    def _pump(self):
        try:
            while True:
                kind, payload =
self.q.get_nowait()
                if kind == "log":
                    self.log(payload)
                elif kind == "done":
                    self.prog.stop()
                   
self.run_btn.config(state="normal")
                    s = payload["summary"]
                    self.last_html =
payload["_html_path"]
                   
self.open_btn.config(state="normal")
                   
self.folder_btn.config(state="normal")
                    self.log("-" * 70)
                    self.log("VERDICT: %s  
(%s)" % (s["verdict"], s["mode"]))
                    self.log("Images: %s" %
json.dumps(s["image_status_counts"]))
                    if
s["avg_text_similarity"] is not None:
                        self.log("Text
similarity avg %.2f%% / min %.2f%%"
                                 %
(s["avg_text_similarity"] * 100,
s["min_text_similarity"] * 100))
                    if s["avg_page_ssim"]
is not None:
                        self.log("Page
raster SSIM avg %.4f" % s["avg_page_ssim"])
                elif kind == "error":
                    self.prog.stop()
                   
self.run_btn.config(state="normal")
                    self.log(payload)
                   
messagebox.showerror("Comparison failed",
payload.strip().splitlines()[-1])
        except queue.Empty:
            pass
        self.after(120, self._pump)
    def _open(self):
        if self.last_html:
            self._launch(self.last_html)
    def _open_folder(self):
        if self.out_dir.get():
           
self._launch(self.out_dir.get())
    @staticmethod
    def _launch(path):
        try:
            if
sys.platform.startswith("win"):
                os.startfile(path)  # noqa
            elif sys.platform == "darwin":
                subprocess.Popen(["open",
path])
            else:
                subprocess.Popen(["xdgopen", path])
        except Exception as e:
            messagebox.showerror("Cannot
open", str(e))
if __name__ == "__main__":
    App().mainloop()
    
