# P1b: Is the Circle-Pour spiral reachable through the real PowerPoint UI?

**Verdict.** YES. `textCirclePour` is one click away in the gallery under the UI name **"Warped Circle"**. A lone Arial `/` turns into an
Archimedean-spiral ribbon using only UI actions (click path below). The result is exact at the glyph corners (≤ 0.055 pt at
R = 151 pt) when both guide circles span 360°. That holds only for particular box sizes. The rendered or baked curve between the corners is a Bézier
fit with max error **3.07 % of R** (rms 1.5 % of R), i.e. category (b). Reaching a size with both circles at 360° by spinner is easy (n = 10, 20, 21, 23, 29, 33, 35, 37, 40, 42 below).
The yellow handle cannot be set exactly by dragging, but the **default** (untouched) handle is the exact configuration, so no handle drag is needed.

Backends: desktop PowerPoint 16.0 build 20527, driven by **pywinauto/UIA + SendInput mouse and keyboard** (Python). Read-back by COM
(`Shapes`, `SaveCopyAs` + XML parse) and by a COM-only bake of a *duplicate* (observation only; the original box was never built by COM).
Geometry numbers (anchors, spans, chamfer): **Python numpy/scipy** [Measured]. Fits of the wave and of the sine glyphs and the symbolic spiral
identity: **Wolfram MCP** [Wolfram]. Scratch: `...\scratchpad\P1b\` (`u.py`, `si.py`, `g.py`, `bk.py`, `an.py`, `sweep_clean.json`, `gal_table.json`).

## Exact click path to reproduce the spiral (what I did)

0. **Setup quirk [Measured].** In this installation the *Shape Format* contextual tab is **hidden** (File ▸ Options ▸ Customize Ribbon ▸ Tool Tabs ▸ Drawing Tools ▸ Shape Format was unchecked).
   I ticked it for the probe and **restored it (unticked) at the end**; the ribbon is back to the user's configuration. A human reproducing this needs the tab (or the Format Text Effects route).
1. Insert ▸ **Text Box**, drag a box on the slide, type `/` (typing a text character).
2. Home ▸ Font box ▸ drop-down list ▸ **Arial** (list item); Home ▸ Font Size drop-down ▸ **72** (list item). Size does not matter.
3. Shape Format ▸ Size group launcher ▸ Format Shape pane ▸ *Text Box* ▸ **Do not Autofit** (otherwise the height follows the text).
4. Shape Format ▸ Text Effects ▸ Transform ▸ gallery section **Warp** ▸ item **"Warped Circle"**. Readback `prstTxWarp prst="textCirclePour"`, `avLst` empty (defaults), COM `WarpFormat` = 10.
5. Make the box square with the ribbon Size spinners (Height, Width up/down arrows), see the next section. At n = 42 (302.4 pt square) both circles span 360°.

Input note [Measured]: in the Transform gallery a plain synthetic click often only *highlighted* the item. A reliable commit needed hover, mouse-down 0.35 s, mouse-up, and sometimes
Enter. Selecting from the font/size lists committed with a single click. This is an automation artefact, not a UI limitation.

## 1. UI reachability: Transform gallery, full item list [Measured]

The gallery has **41 items** (None, 4 in *Follow Path*, 36 in *Warp*). I clicked each item from the top and read `prstTxWarp` from the saved XML (COM `WarpFormat` returns 0 for Follow Path).
The loop was stopped after "Wave: Up" because each item took 1 to 3 minutes. Rows marked *(order)* were **not clicked**: they follow the gallery order, which
matches the COM enum order, and each was seen for items 0 to 22.

| # | UI name (UIA name = tooltip) | prstTxWarp | COM enum |
|---|---|---|---|
| 0 | None | (no warp) | 0 |
| 1 | Arch | textArchUp | n/a |
| 2 | Arch: Down | textArchDown | n/a |
| 3 | Circle | textCircle | n/a |
| 4 | Button | textButton | n/a |
| 5 | Square | textPlain | 36 (observed; the COM enum puts textPlain last) |
| 6 | Stop | textStop | 1 |
| 7 | Triangle: Up | textTriangle | 2 |
| 8 | Triangle: Down | textTriangleInverted | 3 |
| 9 | Chevron: Up | textChevron | 4 |
| 10 | Chevron: Down | textChevronInverted | 5 |
| 11 | Ring: Inside | textRingInside | 6 |
| 12 | Ring: Outside | textRingOutside | 7 |
| 13 | Arch: Warped | textArchUpPour | 8 |
| 14 | Arch: Warped Down | textArchDownPour | 9 |
| **15** | **Warped Circle** | **textCirclePour** | **10** |
| 16 | Warped Button | textButtonPour | 11 |
| 17 | Curve: Up | textCurveUp | 12 |
| 18 | Curve: Down | textCurveDown | 13 |
| 19 | Warp Up | textCanUp | 14 |
| 20 | Warp Down | textCanDown | 15 |
| 21 | Wave: Down | textWave1 | 16 |
| 22 | Wave: Up | textWave2 | 17 |
| 23 to 40 | Double Wave: Down-Up, Double Wave: Up-Down, Inflate, Deflate, Inflate: Bottom, Deflate: Bottom, Inflate: Top, Deflate: Top, Deflate: Top Inflate: Bottom, Inflate: Middle Deflate: Top and Bottom, Fade: Right/Left/Up/Down, Slant: Up/Down, Cascade: Up/Down | *(order)* textDoubleWave1, textWave4, textInflate, textDeflate, textInflateBottom, textDeflateBottom, textInflateTop, textDeflateTop, textDeflateInflate, textDeflateInflateDeflate, textFadeRight, textFadeLeft, textFadeUp, textFadeDown, textSlantUp, textSlantDown, textCascadeUp, textCascadeDown | 18 to 35 *(order)* |

The UI names are the PowerPoint 365 names; the Follow Path ones are the 4 non-pour presets P1 had to XML-patch. They are all reachable by click.

Other routes [Measured unless noted]:
- **Right-click menu** on the box: Cut, Copy, Paste, Edit Text, Edit Points, Group, order items, Lock, Link, Save as Picture, Translate, Alt Text, Set as Default Text Box Style, Size and Position, Format Shape, New Comment. **No Transform.**
- **Format Shape pane ▸ Text Options ▸ Text Effects**: Shadow, Reflection, Glow, Soft Edges, 3-D Format, 3-D Rotation. **No Transform entry** (the pane has none; only the ribbon Text Effects menu does).
- **WordArt Styles gallery** (Shape Format, 20 styles + Clear WordArt): the style names are all fill/outline/shadow/bevel/glow/reflection combinations ("Fill: White; Outline: ...", "Gradient Fill ...", "Pattern Fill ..."), none mentions a transform. I did not apply each one; **[Open]** that none carries a warp. COM `WordArtStyle` is not usable for a probe.
- **Format Painter / Designer**: not tested. [Open]. They could only copy a warp that was UI-made anyway, so they add no new route.

## 2. Boxes by UI only, which sizes give 360° / 360°

Sizing by UI [Measured]: the ribbon Size spinners (and the pane Size spinners) step in **0.1 inch = 7.2 pt = 91440 EMU**. A first click snaps to the next multiple of 0.1 in
(the drag-created box was 1.31 in high; the first Up gave 1.4 in), then each click adds exactly 91440 EMU (COM reads 7.2 pt multiples to float precision, stored EMU = 91440 n).
So a **square of side n/10 inch** is reachable for every integer n (limited by the slide: height ≤ 450 pt from the box's top margin). Drag-resizing is not needed. Default text insets are 0.1 in / 0.05 in; I left them.
The guide circle uses the **whole box width**, not the inset text rectangle: R = W/2, inner ρ = 0.5 R (default adj2 = 50 %), centre at the box centre [Measured, nodes at radii 79.2 and 39.6 for W = 158.4].

Method [Measured]: for each square W = H = 7.2 n pt I baked a duplicate of the `/` box (Merge Shapes via COM on the duplicate, slide in view) and compared its nodes with the
four corners of the ideal map `Z(u,v)` for the Arial slash (corners (0,−25), (425,1491), (569,1491), (145,−25) in 2048/em) with `u = x/569`, top of ink to the outer circle (clockwise from 9 o'clock).
The spans (outer, inner) were chosen from {360°, 352.64°}. Best-fit corner distance ≤ 0.048 pt for all 33 sizes, so the two-valued model is exact to render precision.

| n (side n/10 in) | outer / inner span |
|---|---|
| 10 | 360 / 360 |
| 11, 13, 15, 22, 26, 27, 30, 39 | 352.64 / 360 |
| 12, 14, 19, 24, 25, 28, 38 | 352.64 / 352.64 |
| 16, 17, 18, 31, 32, 34, 36, 41 | 360 / 352.64 |
| 20, 21, 23, 29, 33, 35, 37, 40, 42 | **360 / 360** |

**Sizes with both circles at 360° reachable by spinner (n = 10 to 42): n = 10, 20, 21, 23, 29, 33, 35, 37, 40, 42.** Examples: 1.0 in, 2.0 in, 2.1 in, 2.3 in, 2.9 in, 3.3 in, 4.2 in squares. Larger n
mostly gives 360° outer (n ≥ 31: outer 360 except n = 38 and 39), the inner circle stays patchy.

The 352.64° rule: **[Open]**. A brute-force search of rules `frac(c·n) < t` with c in (0, 3) found none at ≥ 97 % accuracy for either circle; it is not a function of the radius alone (outer(11) = 352.64 but inner(22) = 360, and ρ = R/2 for n = 22 has the same EMU radius as R at n = 11).
[Heuristic] 352.64 = 360·(1 − 1/49) looks like PowerPoint's own guide-length estimation ending one step short, with a step count that depends on the integer EMU size in a chaotic way.
Because it is chaotic, *a human must check the result*; there is no UI readout of the span. The visible symptom of the bad case is a radial segment becoming a chord.

Fit at n = 42 (302.4 pt square, 360/360) [Measured, Python]: the four glyph corners land within **0.000, 0.019, 0.055, 0.029 pt** of the ideal map (R = 151.2 pt). Between corners the baked outline
(12 nodes, one cubic per piece) differs from the ideal mapped polygon by **max 4.64 pt = 3.07 % of R, rms 2.28 pt / 1.5 % of R** (baked→ideal max 4.16, rms 1.78). This agrees with P1 (2.8 %).
**[Wolfram]** The ideal curve: the left edge `u = (425/569) s`, `v = 1−s` maps to `r = ρ + (R−ρ)(θ−θ₀)/(2π·425/569)`, an exact Archimedean spiral of pitch `dr/dθ = (R−ρ)·569/(850π)` that turns through 360·425/569 = 268.9°.
A naive "one cubic per piece from the mapped control points" model gives a 9 % error, so PowerPoint's real Bézier construction is not that; I only report the measured 3.07 %.

Idealization category: **(b)** (stored/rendered Bézier approximation of an ideal map), exactly as in P1; the interior map is not given by ECMA-376 §20.1.10.76 (only the guide paths). [Spec, as in P1]

## 3. The yellow handle by real mouse drag [Measured]

The handle sits on the inner circle at the start angle. Dragging with real mouse input, `avLst` after each drag (units: adj1 in 1/60000 degree, adj2 in 1/1000 %):

| action | target | result |
|---|---|---|
| drag along inner circle to −90° | 270° | adj1 = 16261648 (271.03°), adj2 = 50364 |
| drag to 0° | 0° | adj1 = 36311 (0.61°), adj2 = 51809 |
| drag to 45° | 45° | adj1 = 2683402 (44.72°), adj2 = 52114 |
| Alt-drag to 100° | 100° | adj1 = 99.37°, adj2 = 51.592 |
| Shift-drag to 200° | 200° | adj1 = 12006606 (200.11°), adj2 = 52533 |
| Ctrl-drag to 250° | 250° | adj1 = 15009110 (250.15°), adj2 = 51790 |
| Alt-drag to 300° | 300° | adj1 = 18016655 (300.28°), adj2 = 51971 |
| drag to the box centre | n/a | adj2 = 0.653 % (not 0; P1 said exactly 0 drops the warp) |
| drag far right | n/a | adj1 = 6 (0.0001°), adj2 = **100000** (clamp, exact) |

Conclusions: **no snapping** (values are pixel-quantised, a few 0.1°), no modifier (Alt/Shift/Ctrl) changed that, and every drag also perturbs the other adjustment (a radial drift of about 1 to 2 %
in adj2 for an angular drag). The only exactly reachable values are the clamps: adj2 = 100000 (inner circle = outer circle, which degenerates the band) and the untouched defaults (adj1 = 180°, adj2 = 50 %).
Keyboard nudging of the handle: arrow keys move the shape; I found no keyboard route to adjust a handle [Heuristic, not exhaustively tested]. **So the exact spiral must use the default handle.** Since a nonzero inner radius only rotates the spiral (P1 finding 5), nothing is lost.

## 4. Precedent measurement

**Correction applied:** the project's `sine` constructor is idealized from a **font glyph**, not the wave preset. The wave number below is an incidental data point; the glyph numbers are the closer precedent, but I do not know which font
the project used, so I measured the three candidates that contain U+223F "∿" (the only Windows fonts with that code point and a sine shape are Cambria Math, Segoe UI Symbol, Lucida Sans Unicode, plus the CJK MS Gothic family; I skipped MS Gothic).

**Wave preset (incidental)** [Measured + Wolfram]. Merge-baked `wave` (msoShapeWave = 103, default adj1 = 12.5 %, adj2 = 0) gives the top edge as ONE cubic over the full width with control points at x = w/3, 2w/3 and y offsets ∓(10/3)·y₁, `y₁ = 0.125 h`
(bottom edge identical, mirrored). The peak is 0.9623 y₁, below the control offset. Against the best sine over one period (Wolfram): least-squares sine amplitude 0.9675 y₁, **rms 0.0901 y₁ = 9.3 % of amplitude, max 0.1532 y₁ = 15.8 % of amplitude**;
minimax sine (amplitude 1.0076 y₁): max 0.1328 y₁ = 13.2 %. Relative to the period w, for a default 2:1 box, y₁ = w/16, so max ≈ 0.96 % of the period.

**Sine glyph U+223F "∿"** [Wolfram, midline of the glyph outline by vertical slicing, `y = c + a sin(ωx+φ)` free ω; Python/fontTools extracted the outline]. Caveats: it is 1 to 1.2 periods, and the ribbon ends add noise, so treat as ±2 %.

| font | fitted amplitude (font units) | rms | max | rms / amp | max / amp |
|---|---|---|---|---|---|
| Cambria Math | 302.9 | 22.1 | 56.4 | 7.3 % | 18.6 % |
| Segoe UI Symbol | 344.2 | 23.7 | 47.1 | 6.9 % | 13.7 % |
| Lucida Sans Unicode | 561.5 | 27.2 | 66.4 | 4.8 % | 11.8 % |

**Circle Pour vs the ideal spiral** [Measured]: max **3.07 % of R**, rms **1.5 % of R** (R is the outer radius, the natural "amplitude"). So, normalised the same way, the spiral is about **4 times closer to its ideal than the wave preset is
to a sine, and 2 to 6 times closer than the sine glyphs** (max 3.1 % vs 12 to 19 %). **Caveat [Heuristic]:** the sine glyph is judged against a *best-fit* sine with free frequency, while the spiral's ideal is fixed by the map, and "relative to R" vs "relative to amplitude" are not the same normalisation. In defence of the spiral, the glyph's deviation is from a curve that was never claimed to be exactly sinusoidal, whereas the spiral
has an explicit ideal map with exact corner anchors. On this evidence idealizing the spiral is on **at least as good a footing** as idealizing the sine glyph. Whether (b) is acceptable remains the user's call.

## Other things noticed

- The Transform gallery needs hover before a click commits (see Input note). A click that only highlights does not apply the warp; `Enter` on the highlighted item does.
- Applying **Wave: Down** (textWave1) to the unfitted default box also showed that the slash turns into a thick wavy ribbon (screenshots in the scratchpad).
- The spiral ribbon has a short **radial bar at the 9 o'clock seam** (the left-bottom slash corner region). It is the slash's slanted edge near u = 0 and does not affect the spiral edge.
- With the default handle the rendered start is at 9 o'clock, clockwise on screen.
- The user's ribbon hides the *Shape Format* tab. Restored.
- PowerPoint did not crash this time (Merge Shapes with the slide in view, `GotoSlide(1)` before every bake). My presentation `p1b.pptx` was closed without saving; the pre-existing `pptD501.pptx - AutoRecovered` window was left alone.
- An earlier loop pass of the gallery (about 25 min) was wasted because clicking only highlighted items; the table above is from the later, verified passes (every row's prst differs from the previous one).
