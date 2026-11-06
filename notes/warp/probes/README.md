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
| `probe_equalize.py`, `probe_equalize2.py` | Equalize Character Height and baseline offset: per-glyph maps, band, 2/3 size, warp of equalized rows (`../EQUALIZE-AND-OFFSET.md`) |

Results of the UI-input probe are in `ui_inputs.json`.

The spec XML is downloaded once from the LibreOffice repository into `%TEMP%`.
