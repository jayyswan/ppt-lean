# WP: PowerPoint probe of the warped sine glyph 〰 (Warped Circle, Arch: Warped, Arch: Warped Down)

Stream WP of `pptc/PLAN-warp-sine.md`. Desktop PowerPoint 16.0, my own new presentation
`...\scratchpad\warp_WP\wp.pptx` (closed at the end with `Saved = True`; the user's `pptD501` was not touched).
Labels: [Measured] = PowerPoint observation (Python: win32com, SaveCopyAs XML, PNG export), [Wolfram] = fit or
check in the Wolfram MCP on pasted-in sample data, [Proof], [Heuristic], [Open].

Scratch (scripts, pickles `circ_n/up_n/down_n.pkl`, screenshots):
`C:\Users\jason\AppData\Local\Temp\claude\C--dev-Powerpoint-lean\c222b849-70f5-4b01-ad09-a19ea61d2b9d\scratchpad\warp_WP\`
(`lib.py` driver, `an.py` map model and accuracy, `row.py`, `polar_edges.py`, `d_meas.py`).

How it was driven (UI only, as in F1): Insert ▸ Text Box and Unicode keystrokes for 〰; Home font **dropdown list**
click for Yu Mincho; Home size list (72 pt); Format Shape pane (Do not Autofit, Wrap off); ribbon Size spinners
(square, F1's both-guides-full sizes: 4.0 in = 40 for Circle and Arch: Warped, 3.6 in = 36 for Arch: Warped Down);
Shape Format ▸ Text Effects ▸ Transform gallery; Text Outline colour and weight menus; Text Fill ▸ No Fill; Insert
Shapes ▸ Rectangle (dummy), Merge Shapes ▸ Fragment; Ctrl+D, Ctrl+C, Paste Special ▸ Picture (Enhanced Metafile),
Ctrl+Shift+G. COM was used only to observe (geometry via bake = duplicate + Merge Combine + `SaveCopyAs` + parse
`custGeom`; flat reference = same bake with `WarpFormat = 0`; Nodes counts; EMF export; `Select()` of my own shapes).
No numbers were typed into any dialog. The yellow handle was never touched.

## Findings summary

1. **No exact limaçon or rose route found. [Measured + Wolfram + Heuristic]** What exists:
   - The warp itself is exactly the F1 polar map (whole-row ink box), to 0.04 to 0.08 pt at nodes and 0.30 to 0.87 pt
     (0.30 to 0.61 % of R) between nodes. So the *exact* image of any flat curve is `P(curve)`.
   - The **image of the spine** is an exact rose: `r = R(3/4 + 0.2022 cos mθ)` for Circle (`m = 2n` for n glyphs,
     `a = 108.07, b = 29.12` pt at R = 144), `m = 4n` for the arch presets. [Proof, from G's spine
     `v = 1/2 − 0.404 cos(4πnu)` and `r = R(1 − v/2)`; checked numerically in Wolfram, section 3.] **But nothing in
     the UI yields `P(spine)`**: the spine is not text, the band cannot be thinned, and no operation averages the
     two warped edges (section 4, 5).
   - The **warped edges** are `P(normal-offset edges of a sine)`, not roses. Best pure rose `a + b cos(mθ)` fitted to
     an edge: max residual 1.8 pt (1.26 % of R) Circle, 1.8 pt Arch Up, 2.3 pt (1.78 % of R) Arch Down. Adding the
     2nd harmonic cuts it to 0.8 / 0.6 pt, i.e. to the baking noise. Per the user's 2026-11-03 decision, an
     approximate edge does not count; it is a by-product.
   - Never `m = 1`: 〰 carries 2 periods per glyph, so a Circle row gives `m = 2n` and an arch row `m = 4n`. A true
     limaçon (`m = 1`) cannot come from 〰 in any row. Roses with even `m` only.
2. **Text Outline on warped text is applied after the warp, at constant width in the plane. [Measured]** A 6 pt
   outline (no fill) on the warped circle: inscribed half-width at the outline median 2.97 pt (range 2.78 to
   3.84), stroke area 8689 pt² vs 8883 expected for 6 pt × outline length 1480.5 pt. A pre-warp stroke would be
   about 5× wider radially than tangentially. Merge Shapes ignores outline and fill (Hausdorff 0.0 between the
   stroked and unstroked bakes). So the stroke offsets the warped outline by ±w/2 in the plane; it cannot recover
   `P(spine)`.
3. **No UI path warps a freeform. [Measured]** The Transform gallery is enabled on a freeform produced by Merge
   Fragment, and choosing Warped Circle sets `WarpFormat = 10`, but all 73 nodes are unchanged (the freeform has no
   text). There is no shape-to-text conversion. The warp acts only on text runs.
4. **Band ends. [Measured]** The two end cuts of a row (vertical at crest height, ink v from 0 to 0.1858) map to
   radial segments. Circle: both land on the **same segment** at θ = 180° (9 o'clock), r = 130.63 to 144.00 pt
   (R = 144), so the band closes into a seamless ring with no pinch and no gap (the baked path carries that segment
   twice). Arch Up: left end at 9 o'clock and right end at 3 o'clock, each r = 130.63 to 144. Arch Down: r = 32.40
   to 50.45 (R = 129.6, ink top → R/4). The ●-pinch is the zero-width analogue of this seam.
5. **The font really is Yu Mincho. [Measured]** Flat ink box 72.000 × 13.816 pt at 72 pt (advance 72 = ink width,
   zero side bearings), equal to the cached `Yu Mincho Regular` cloud font's glyph bbox (0..2048 × 582..975 em
   units = 72 × 13.816 pt, fontTools). The Home font box did not accept typed "Yu Mincho"; choosing it from the
   dropdown list set `latin` and `ea` to Yu Mincho (XML checked). Selecting "Yu Mincho Light" (select to download)
   gave a byte-identical outline (not installed here, same as G's finding).

## Rows and accuracy (a, c)

Flat 〰 at 72 pt: ink x 91.2 to 163.2, y 90.0726 to 103.8890. Adjacent glyphs touch (advance = ink width), so a row
of n is one continuous band of 2n periods; the baked outline is one closed subpath. Map model per F1:
`F(u,v)` with `u = (x − x₀)/(x₁ − x₀)`, `v = (y − y₀)/(y₁ − y₀)` from the **whole row's** ink box; Circle
`θ = π + 2πu`, `r = R(1 − v/2)`; Arch Up `θ = π + πu`, same r; Arch Down `θ = π − πu`, `r = R/4 + (3R/4)v`.

| preset (box) | n | flat nodes | warped nodes | corner max (pt) | between max (pt, % R) | between rms (pt, % R) |
|---|---|---|---|---|---|---|
| Circle (R=144) | 1 | 33 | 35 | 0.055 | 0.874, 0.61 | 0.215, 0.15 |
| Circle | 2 | 64 | 66 | 0.071 | 0.538, 0.37 | 0.136, 0.09 |
| Circle | 3 | 95 | 98 | 0.073 | 0.486, 0.34 | 0.109, 0.08 |
| Circle | 4 | 126 | 128 | 0.078 | 0.447, 0.31 | 0.100, 0.07 |
| Arch: Warped (R=144) | 1 | 33 | 34 | 0.065 | 0.550, 0.38 | 0.133, 0.09 |
| Arch: Warped | 2 | 64 | 66 | 0.071 | 0.440, 0.31 | 0.101, 0.07 |
| Arch: Warped | 4 | 126 | 128 | 0.072 | 0.431, 0.30 | 0.089, 0.06 |
| Arch: Warped Down (R=129.6) | 1 | 33 | 34 | 0.039 | 0.628, 0.48 | 0.134, 0.10 |
| Arch: Warped Down | 2 | 64 | 66 | 0.056 | 0.598, 0.46 | 0.118, 0.09 |
| Arch: Warped Down | 4 | 126 | 128 | 0.064 | 0.590, 0.45 | 0.112, 0.09 |

[Measured, Python.] Crests and troughs are nodes, so the extrema are the "corners": e.g. Circle n = 1 crest
r = 143.995 / 130.434 (outer/inner edge, predicted 144 / 130.43), trough 85.568 / 72.007 (predicted 85.56 /
72.00). Between nodes the error is 0.3 to 0.6 % of R, an order of magnitude better than F1's spiral edges
(2.8 to 5.4 % of R) because the sine edges are smooth and short; F1's baked straight edges were the worst case.
The whole-row law (F1 a) holds for 〰 at n = 1..4 on all three presets. Warped bakes have 1 to 3 more nodes than
the flat glyph (the joins between glyphs merge; the radial end cut is a degenerate cubic, not an `L`).

Screenshots: `circ_1` (`sc14.png`), `circ_2.png`, `circ_3.png`, `circ_4.png`, `up_1.png`, `up_2.png`, `up_4.png`,
`down_1.png`, `down_2.png`, `down_4.png`, all in the scratch folder above (the faint blue wave drawn over the ring
in `circ_4.png` is a repaint artefact; the slide held one shape).

## (b) Fits, [Wolfram] on Python-sampled edges

Flat edges of one glyph (73 samples per edge, 1 pt spacing, Python bake; x measured from 91.2):

- Pure sine to the top edge, period 36 fixed: const 95.400, amp 5.545, max residual 0.343 pt (6.2 % of amp),
  rms 0.180. Bottom edge: const 98.539, amp 5.569, max 0.332 pt (6.0 %). With 3 harmonics: max 0.091 / 0.039. The
  2nd-harmonic coefficients are **+0.244 (top) and −0.250 (bottom)**: opposite signs, mean −0.003, so the spine
  is nearly a pure sine while the edges are not (matches G: edges 5.3 / 5.9 % of a).
- Vertical gap between edges: 2.566 to 3.657 pt (ratio 1.425), so not a vertical shift (agrees with G).
- Normal-offset model (sine spine `c − A cos(2πx/36)` offset ±h along the normal; least squares on both edges):
  c = 96.9671, A = 5.5883, h = 1.3037 (w = 2.607, w/H = 0.1887), max distance 0.093 pt, rms 0.046 pt. G: w/H =
  0.188, spine `v = 0.5 + 0.404 cos`; A/H = 0.4045. Agreement.

Warped Circle n = 1 (R = 144; 71 interior u-samples per edge from the PowerPoint bake; m = 2):

| model | outer edge max / rms (pt) | inner edge max / rms (pt) |
|---|---|---|
| (i) `P(normal-offset edges of the fitted sine spine)` (radial difference at equal θ) | 0.847 / 0.246 | 0.406 / 0.178 |
| (ii) pure rose `r = a + b sin(2θ + φ)` (φ = π/2, i.e. `a + b cos 2θ`), free a, b | 1.817 / 0.942 (a = 116.32, b = 28.93) | 1.654 / 0.924 (a = 99.86, b = 28.92) |

(i) is at the level of the baking noise (0.87 pt); (ii) is 2 to 4 times worse and is the missing 2nd harmonic.
Other cases, pure rose, free a, b: Arch Up n = 1 (m = 4): outer a = 116.33, b = 28.95, max 1.816, rms 0.956; inner
a = 99.87, b = 28.92, max 1.638, rms 0.908; with a 2nd harmonic max 0.806. Arch Down n = 1 (m = 4, R = 129.6):
outer a = 92.06, b = 39.03, max 2.307, rms 1.273; inner a = 69.88, b = 39.10, max 2.305, rms 1.230; with a 2nd
harmonic max 0.574. Circle n = 2 (m = 4), inner edge: a = 99.89, b = 28.93, max 1.709, rms 0.909 (outer edge not
rerun, a Wolfram name clash on `O`) [Open].

**Where `P(spine)` lies** (Circle n = 1, R = 144): `r_s = R(1 − v_s/2)` with the fitted spine gives
`a_s = 108.07`, `b_s = 29.12`. Its position between the measured edges, as a fraction of the way from the outer
edge to the inner edge: min 0.478, max 0.534, mean 0.501. So `P(spine)` sits within about ±3 % of the band
thickness of the midline of the warped band (max |P(spine) − mean of the two edges| = 0.17 pt), but the band
thickness itself swings 13.5 to 19.1 pt, so no fixed offset of an edge reaches it.

## (d) Text-level operations, what they do and do not do

- Text Outline (colour, 6 pt) with Text Fill ▸ No Fill on warped text: stroke after the warp, constant plane width
  (finding 2). Real UI path to a thin ring look, but geometry of the text outline is unchanged.
- Fragment (Merge Shapes ▸ Fragment, rectangle dummy, UI) on the warped, outlined duplicate: 5 freeform pieces
  (40, 73, 13, 22, 23 nodes) of the **band outline**, not of the stroke. So "outline only + no fill, then fragment"
  does not thin the band or isolate an edge: the pieces are regions of the band cut by the dummy.
- Copy ▸ Paste Special ▸ Picture (Enhanced Metafile) ▸ Ctrl+Shift+G ▸ confirm "convert to drawing object":
  result is an empty autoshape plus a freeform with 118 nodes whose **6 pt line is still a line** (Line.Visible,
  Weight 6, no fill); repeating the EMF round trip on that freeform gave the same (118 nodes, 6 pt line). In this
  build the stroke did not become a filled shape (the deck's stroke-to-shape step is not reproduced by this
  route) [Open: other conversion routes].
- Shape.Export to EMF of the stroked warped text: 2592 bytes, one EXTCREATEPEN (width 400 logical units) and EMF+
  comment records; not parsed further.
- Weights: Yu Mincho Light/Demibold selectable but identical outline to Regular (not installed).
- Not found: any text-level setting that thins the glyph, selects one edge, or shifts it normally.

## (e) Freeform and shapes

See finding 3. Also: a Merge-Fragment freeform keeps text capability (Text Effects ▸ Transform enabled, empty text),
so the gallery cannot be used as a test of availability, only of effect: no effect on geometry.

## Other things noticed

- The Home font box will not commit a typed cloud-font name ("Yu Mincho") with Enter; it silently reverts. Pick it
  from the dropdown list (it appears at the top once used). Typing into the Font dialog's Latin box would only set
  `latin`; the Home list set both `latin` and `ea` here.
- The window layout moves: the slide origin was (521, 280) px with no pane and (316, 280) with the Format Shape
  pane open; the Designer pane opened itself after the EMF-to-drawing conversion (harmless, closed with the file).
- Autofit radios and the size dropdown behave as F1 noted; text box needs Do not Autofit and Wrap off before sizing.
- A row of n glyphs (72 pt) is 72n pt wide, wider than the 288 pt box for n = 4; with wrap off the warp still uses
  the ink box, so overflow does not matter.
- Zoom changed between 73 % and 74 % between screenshots (my window only); layout coordinates were re-read from
  screenshots, not assumed.
- Part-2 pointer [Heuristic]: if a glyph with *vertical-shift* sine edges existed, each warped edge would be an exact
  rose `a ± δ' + b cos mθ`. G's sweep found none (best normal-offset glyph: Yu Mincho 〰), so the only exact roses
  here are `P(spine)` curves, unreachable in the UI, and, up to 1 % of R, the edge fits above.
