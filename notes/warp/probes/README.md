# Text-warp probes

Scripts behind `../TEXT-WARP-THEORY.md`. Run with `py <script>` (not `py -I`: win32com
lives in user site-packages) from this folder. Each script opens its **own** new
presentation and closes it without saving; other open presentations are not touched.

**COM is for observation only.** Setting `WarpFormat`, or injecting a preset or handle value
into the saved XML, reproduces a state for measurement. Whether that state is reachable by UI
clicks is a separate question:
- every `WarpFormat` value is a Transform-gallery item;
- the Follow Path presets are the gallery's "Follow Path" row;
- handle values other than the default need a drag (`probe_handle.py`).

Merge Shapes needs a document window, so presentations open with a (background) window.
`probe_handle.py` is the only script that moves the mouse. It needs PowerPoint in the
foreground; do not run it while someone else is using the screen.

| Script | Question |
|---|---|
| `enum_probe.py` | COM `WarpFormat` ↔ spec preset names |
| `probe_maplaw.py TEXT PRESET…` | corner/edge error under each guide parametrization |
| `probe_sweep.py [TEXT]` | all 36 presets: ruled arc-length law, fill factor k |
| `probe_slaw.py TEXT PRESET…` | the guide fraction `s(u)` actually used |
| `probe_pinned.py PRESET ADJ TEXT` | images of idealized circle glyphs at a handle value |
| `probe_followpath.py`, `probe_follow_render.py` | Follow Path presets: rigid or bent |
| `probe_handle.py PRESET HX HY DX DY` | UI drag of a handle past its stop |
| `plotcase.py TEXT PRESET [MODE]` | plot model vs PowerPoint |
| `probe_textbox_model.py [CASE…]` | `Pptc/TextBox.lean`'s `TextBox.outline`, evaluated literally, vs PowerPoint |
| `probe_ctrlpts.py`, `probe_fitbox.py` | exact image vs control-point warp; fitted normalizing box (box-size anomaly) |
| `probe_layout.py`, `probe_layout2.py` | pen advance, 0.75 pt snapping, drawn-size quantization |
| `probe_ui_inputs.py [STEP…]` | UI Automation: size list, grow/shrink closure, spacing presets, dialog and size spinners (takes the screen) |
| `probe_offset.py`, `probe_offset2.py SIZE [TOP]` | baseline offset: 2/3 size, rise and pixel snapping (exact rule in `Pptc/TextBox.lean`, `RowGlyph.rise`) |
| `probe_equalize.py`, `probe_equalize2.py` | Equalize Character Height and baseline offset: per-glyph maps, band, 2/3 size, warp of equalized rows (`../EQUALIZE-AND-OFFSET.md`) |
| `probe_equalize3.py` … `probe_equalize6.py` | Equalize band across fonts, sizes, offsets, glyphs and rows |
| `probe_equalize_table.py [FONT] [NMAX]` | the full band table per font (`equalize_table_*.json`); rule in `Pptc/TextBox.lean`, `equalizeBand` |
| `make_nohint.py SRC DST FAMILY` | unhinted renamed font copy, to test whether a metric comes from hinting |
| `gdi_metrics.py` | Windows' integer font metrics per pixel size |
| `probe_kern.py` | kerning threshold and pair adjustment |
| `probe_row_model.py LEAN_EVAL` | end-to-end: Lean row model (`#eval`) vs PowerPoint, sizes/offsets/spacing/Equalize |
| `probe_presets_model.py [PRESET ...]` | probe 32: Lean `WarpPreset.map` of every modelled preset at every reachable handle stop vs PowerPoint (`presets_model.json`: first 23 presets; `presets_model2.json`: the 7 further Bézier presets; `presets_model3.json`: the 6 quadratic presets; set `PRESETS_OUT` to name a new run's file) |
| `probe_presets_fill.py PRESET H1 H2 W H ...` | probe 33: per-guide fill fraction for the misses of probe 32; all fit 48/49 (`presets_fill.json`, `presets_fill2.json`) |
| `probe_row_block.py rowcheck_block_out.txt` | probe 34: Full Block in a mixed row (size, spacing, offset, Equalize) vs `RowCheckBlock.lean` predictions |
| `probe_block_warp.py` | probe 35: a lone Full Block's corners through 18 presets in two boxes, plus the two-block overlap (`block_warp.json`) |
| `probe_row_triangle.py rowcheck_triangle_out.txt` | probe 36: Lower Right Triangle in a mixed row vs `RowCheckTriangle.lean` predictions |
| `probe_triangle_warp.py` | probe 37: a lone triangle's corners and slanted edge through 19 presets in two boxes (`triangle_warp.json`) |
| `probe_triangle_row.py [N] [size]` | probe 38: a row of N triangles (short slanted edges) through 11 presets (`triangle_row.json`) |

Results of the UI-input probe are in `ui_inputs.json`.

The spec XML is downloaded once from the LibreOffice repository into `%TEMP%`.
