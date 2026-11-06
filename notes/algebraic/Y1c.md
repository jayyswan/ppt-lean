# Y1c: can PowerPoint draw a Minkowski sum of a curve with a non-elliptical shape?

Stream Y1c of `pptc/PLAN-algebraic.md` (section "Y1"). Written 2026-11-05.

Labels: [Measured], [Wolfram], [Proof], [Heuristic], [Open].

Backends. PowerPoint 16.0, driven by SendInput and UIA, with COM for observation. Python (`py`) was
used for UI driving, EMF parsing and node read-back, and for numpy distance fits. Wolfram was used
for the closed-form checks. Scripts and EMFs are in the session scratchpad `...\scratchpad\Y1c\`
(`sv.py`, `emf.py`, `pathobj.py`, `u*.py`, `an*.py`). Every Python number in the tables is a
distance or an area, not an identity.

Setup that is not a construction step (typed into the Format Shape pane, as in P5):
- the shadow's blur = 0, transparency = 0 and distance.
- the stroke weight, in most of the survey. It was set through COM, which counts as observation:
  COM has no cap or join property, so those two went through the pane combos.

## 1. Findings summary

**1. PowerPoint does have a vector stroke-to-outline route. It is a round pen (disk), plus the
miter-join polygon at corners. It is exact to about 0.03 pt on smooth curves.**
- Route: stroke a curve, give it an opaque unblurred outer shadow, copy, Paste Special as Enhanced
  Metafile, ungroup, accept the conversion prompt, ungroup again.
- Result: a filled **Freeform** (259 nodes for my test) whose outline is the stroked region's boundary.
- UI-driven end to end: copy, paste-as-EMF, ungroup ×2 and the shadow preset.
- The shadow is emitted as an EMF+ `FillPath` of the **widened** outline. The stroke itself is only a pen.
- Pasting the stroked shape as EMF and ungrouping twice, with no shadow, leaves a stroke with weight
  attached and no outline. That is why the earlier WP stream did not reproduce the deck's trick.
  [Measured]

**2. The family is exactly the offset constructor, and nothing wider.** [Measured]
- Smooth Bézier, w = 30: all 258 outline vertices lie at 15.000 ± 0.03 pt from the true cubic. The
  polygon sides stay within 0.029 pt (0.19 % of d, 0.014 % of the 200 pt curve size).
- Ellipse 200 × 120, w = 30, no fill: two loops of 184 vertices, at 15.00 ± 0.06 pt from the exact ellipse.
- Read back from the UI-made Freeform's own nodes: 14.83 to 15.18 pt (node quantisation, 0.18 pt).
- At high curvature (radius < d), the nonzero union of the widened loops equals the exact union of
  disks, except for the flat end caps.
  - The area gap was 2803 pt² against 2 × half-disk = 2827 pt².
- Round caps and joins are cubic Béziers: a 118° join splits into 2 cubics of 59.04°, radial error
  2.2e-5 R [Wolfram]. Flat, square and miter outlines are exact vertices. Smooth parts are polylines.

**3. No non-elliptical *curved* summand exists in any route tested.** Nothing found is a curved
convex pen that is not a disk or an affine image of one.
- Strokes: round pen only.
- Non-uniform scale: either applied after the stroke (pen stays round), or lost on conversion
  (see item 5).
- Effects and 3-D: raster.
- Ink: a rectangular summand only, with a freehand centreline.
- Arrowheads: fixed shapes at the ends, not swept.

**4. The only fixed non-disk summands that appear are polygons, and a polygonal summand is inert for
the engine.** [Proof sketch, §3]
- The highlighter: ink ⊕ axis-aligned rectangle (1:2), exported as vector.
- The miter join on a polygon: offsetting by d is Q ⊕ d·R_Q, where R_Q is the polygon with the same
  edge normals circumscribed about the unit disk.
- A convex polygon summand P with P-constructible vertices only translates arcs of the base curve by
  vertex vectors, plus straight segments. Translation by P-constructible vectors is already the
  `translate_x` / `translate_y` constructors.
- The linear parameters d_j enter as Σ d_j·v_k, which is already available. No square root appears,
  so there is nothing to build an engine on.
- An iterated miter offset collapses: offset by d₁ then d₂ is offset by d₁ + d₂, because a polygon
  is determined by its support values at its fixed normals.

**5. The ellipse pen is already in the theory, and is not obtainable by "scale a stroked object".**
[Measured]
- Resizing a stroked freeform non-uniformly: the stroke weight stays 30 and the pen stays circular.
  The stroke is applied after the affine map.
- Stretching the *EMF picture* of a stroked curve by ×2.07: it renders an elliptical pen.
  - Converting that picture to a drawing object keeps one scalar weight of 62.1 pt (= 30 × 2.07, the
    horizontal factor only). The anisotropy is lost.
- The shadow-outline *polygon* is a fill, so scaling it is a plain affine image. That gives
  Aff(curve ⊕ d·disk) = Aff(curve) ⊕ d·ellipse. This is the known offset∘affine tower element.

**6. Dashes give exact arclength marks**, a by-product that matters for `arc_of_length` (§4).

**7. Candidate-by-candidate status.**

| Candidate | Vector via UI? | Boundary family | Accuracy | Idealisable? |
|---|---|---|---|---|
| Stroke, any weight, smooth curve | yes (shadow route) | exact normal offset (disk pen) | 0.03 pt | yes, = `offset` |
| Round / bevel / miter joins, flat / square / round caps | yes | offset ⊕ disk, chord, miter tip, square corner | vertices exact (miter tip 38.868 vs 38.873) | yes, only as "offset with that join" |
| Compound lines (double, thick-thin, thin-thick, triple) | yes | bands between exact offsets at fixed fractions of w | 0.03 pt | yes, = several offsets at once |
| Dash types | yes | pieces of an offset, flat or round end faces at exact arclength | 0.01 w | arclength marks, §4 |
| Arrowheads (5 styles × sizes) | yes, unioned into the outline | fixed polygon or disk at the end | not swept | no summand |
| Non-uniform scale of a stroked shape | n/a | stroke applied after (circular pen) | 0.03 pt | n/a |
| Stretched EMF picture of a stroke | picture only | elliptical pen, lost on conversion | n/a | no |
| Bevels (all 12 types), contour, extrusion | no (bitmap) | raster | n/a | no |
| Glow, soft edges, reflection | no (bitmap halo; base shape vector) | raster | n/a | no |
| Text Outline / WordArt | pen on glyph path, not converted; text shadow raster | stroke only | n/a | via shape first, see §2.8 |
| Sketched style (Curved / Freehand / Scribble) | yes | wobble up to ±9.9 pt at w = 8, different for two identical copies | not reproducible | no (category (c)) |
| Highlighter ink | yes, vector | path ⊕ axis-aligned 1:2 rectangle; freehand path | tip ratio exact, the rest within about 4 % | polygon summand: inert (item 4) |
| Fountain pen ink | yes, vector | isotropic width, end taper only | ring width constant | no nib |
| Other ink pens (Brush, Pencil, Text, Galaxy) | not tested | n/a | n/a | [Open] |

## 2. Details

### 2.1 The stroke-to-outline route

Steps, all by UI except the three typed numbers:
1. Select the stroked shape.
2. Shape Effects ▸ Shadow ▸ Offset: Right. A pane click on the preset did nothing the first time;
   the ribbon menu worked.
3. Format Shape ▸ Effects ▸ Shadow: Transparency 0, Blur 0, Distance 150. (Typed.)
4. Ctrl+C; Ctrl+Alt+V ▸ Picture (Enhanced Metafile); Ctrl+Shift+G, then Yes at "convert to a Microsoft
   Office drawing object"; Ctrl+Shift+G again.

Result in the slide:
- An `AutoShape` frame rectangle.
- A **Freeform** with 259 nodes, `Fill` solid, no line: the shadow outline.
- A **Freeform** with 4 nodes and a 30 pt line: the stroked centreline.

EMF internals, read from `Shape.Export` (COM, observation):
- The stroke is one `EXTCREATEPEN` plus an EMF+ `DrawPath` with a pen object: width, join, miter limit 8.
- The shadow is an EMF+ `FillPath` of a path object that already holds the widened outline.
- For the smooth cubic the outline has 258 points, line segments only.
- With round caps or joins the path object also contains Bézier segments (type 3).

Without the shadow there is no outline at all. A **translucent or blurred** shadow is raster (P5).

### 2.2 Joins and caps (UI pane combos, 40 pt polyline, apex angle 61.93°) [Measured]

| Cap × Join | Apex vertices | End vertices |
|---|---|---|
| Flat, Miter | 2 vertices, both 38.87 from the apex | at 20.0 (= w/2) |
| Flat, Bevel | 2 vertices at 20.0 from the apex | at 20.0 |
| Flat, Round | arc as cubics, control points at 21.2 (= 1.06 R) | at 20.0 |
| Square, any join | as above | 28.27 (= 20√2) |
| Round, any join | as above | quarter-disk cubics, radial reach 22.85 at control points |

- Miter tip prediction d / sin(half apex angle) = 38.873 [Wolfram]; measured 38.868.
- Round-join arc: 118.07° splits into two 59.04° cubics with k = 0.3513. The control distance is
  1.0599 R and the radial error is 2.17e-5 R [Wolfram].
- The Cap-type list does not show the current value; Flat was already set, so the first combo call
  reported "no item Flat". The runs were not affected.

### 2.3 Compound lines (COM `Line.Style`, shadow read-out) [Measured]

All offsets are fixed fractions of the weight w:
- Double (thin-thin): two bands, each bounded by offsets at 5 and 15 (w/6 and w/2).
- Thick-thin and thin-thick: bands at 3 and 9, 9 and 15, etc. (w/10, 3w/10, w/2).
- Triple (thick between thin): three loops, offsets {5, 10, 15}.
- Every boundary is an exact offset to 0.03 pt. The pen is a union of disks at several radii.

### 2.4 Dashes [Measured]

For w = 10, the dash start and end projected to the centreline, in units of w:
- Dash: [0, 4], [7, 11], [14, 18] (dash 4w, gap 3w).
- Long dash: [0, 8], [11, 19].
- Square dot: [0, 1], [4, 5].
- Round dot: [0, 0.5], [3.5, 4.5]. The dots have round caps, so extents are ±w/2.
- The dash-dot variants follow the same grid.
- Each end face is a cut normal to the curve, accurate to 0.01 w.

These are exact arclength marks at k·w. See §4 for what they give.

### 2.5 Arrowheads [Measured]

- The outline includes the arrowhead as a polygon in the same path, with the end shortened.
- Arrow types 2 to 6 at sizes 1, 2, 3 (COM `EndArrowheadLength/Width`):
  - Triangle: half-width 0.99, 1.46, 2.38 w; tip at the endpoint.
  - Diamond and oval: protrude past the end by 1.0, 1.5, 2.5 w, with half-width 1.0, 1.5, 2.5 w.
  - Open-arrow and oval include Bézier segments.
- The arrowhead is a **fixed shape in local frame (end, tangent)**, not swept along the curve.
  It reads (endpoint, tangent direction).

### 2.6 Stroke and scale: before or after? [Measured]

- Freeform resized to ×3 horizontally (COM, observation of a rule only): weight unchanged at 30,
  pen distance 14.98 to 15.02 on the stretched curve. A rotation gave nodes rotated and the pen unchanged.
  The stroke is applied after the geometry, with constant plane width. This matches the Text Outline
  finding of the warp stream [WP].
- EMF picture of a stroked arch, handle-dragged by the UI to width ×2.07, renders an elliptical pen
  (screenshot confirms). Ungroup ×2 gives a Freeform with 4 nodes and `Line.Weight` = 62.125 pt.
  That scales by the horizontal factor only. A round pen of 62 pt then replaces the elliptical one.

### 2.7 Effects and 3-D (`Shape.Export` EMF record counts, COM-set effects) [Measured]

| Effect | EMF content |
|---|---|
| Plain shape | EMF+ `FillPath` + `DrawPath` |
| Glow | 1 image object (raster halo) + the vector base shape |
| Soft edges | all image objects, 8 |
| Reflection | 3 image objects + vector base |
| Bevel, circle (depth 20, inset 20) | 9 image objects, no `FillPath`, no `DrawPath` |
| All 12 bevel types (relaxed inset to art deco) | 4 to 13 image objects each, **no** `FillPath` or `DrawPath` |
| Contour 20 pt | 1 image object |
| Extrusion depth 30 | 2 image objects |

- No bevel profile or contour yields vector geometry. This is the Export path; paste-as-EMF of 3-D was
  already shown raster in R1 to R3.
- Glow and reflection keep a vector base shape plus a bitmap. The bitmap is not geometry.

### 2.8 Text [Measured, partial]

- Outline-only 200 pt "S", 20 pt outline: EMF has one `DrawPath` with a pen (join = 2, 102 points
  with Béziers). It is a stroke on the glyph path, not an outline polygon. A text shadow is bitmap.
- The route to an offset of a glyph: convert the glyph to a shape first (Merge Shapes ▸ Union, as in
  WP, loses the stroke), then stroke the resulting freeform and shadow it as in §2.1.
  The result is the same disk-pen family.
- Compound text outlines and WordArt transforms: not driven in the UI. [Open]
- Under a warp the stroke is applied after the warp at constant plane width [WP].

### 2.9 Sketched style [Measured]

Format Shape ▸ Line ▸ Sketched style (UI), applied to an 8 pt stroked Bézier:
- Curved, Freehand and Scribble all give a wobbling outline, 0.06 to 13 pt from the centreline where
  the plain stroke is 4 ± 0.1.
- The same shape re-exported is identical. Two identical copies differ by up to 9.9 pt.
- The outline is seeded per shape, so the geometry is not reproducible. Category (c).

### 2.10 Ink [Measured via UI drags; EMF export]

- Highlighter strokes drawn with SendInput drags are Type 23 ink shapes, and they export as **vector**
  `FillPath` polygons.
  - A horizontal stroke is a rectangle 0.0240 × 0.0480 EMF units (the tip, 1:2).
  - A drawn ring has local thickness 0.0251 (horizontal tangent), 0.0477 (vertical tangent) and
    0.0497 to 0.050 (diagonal), against a predicted 0.0516 for a rectangle and 0.0383 for an ellipse.
    So the tip is a rectangle (slightly rounded at the corners at the 4 % level).
  - [Wolfram] 45° half-thickness: rectangle model 0.0258, ellipse model 0.0191, measured 0.0248.
- The highlighter has six discrete thickness presets and a colour palette. The aspect ratio is fixed.
- Fountain pen: ring thickness 1.19 % of R at every angle tested except near the start and end
  (pressure taper). The pen is isotropic, not a calligraphic nib.
- The centreline is the mouse path (a freehand polyline). It is not a P-constructible curve, and
  nothing in the UI binds ink to a shape's edge.
- The Draw tab offers a Ruler, which constrains ink to straight lines. [Open: not driven]. A straight
  line ⊕ rectangle is a rectangle or parallelogram, so it is not an engine.

## 3. Why polygon summands do not help

[Proof sketch.]
- Let C be a curve and P a convex polygon with P-constructible vertices v_k and edge normals n_k.
  The support function of C ⊕ P is h_C + h_P.
- Where h_P is linear (the cone of normals for which vertex v_k is active), the boundary point with
  normal u is x_C(u) + v_k. In the normal-cone between n_{k-1} and n_k the base curve is
  **translated rigidly by v_k**. Between those cones the boundary follows the edge segment.
- So C ⊕ P is a finite union of translates of arcs of C, cut at the points where C's normal equals an
  edge normal, together with straight segments.
- For a sum of several polygons Σ d_j·P_j the translation is Σ d_j·v_{j,k_j}. It is a P-constructible
  number when d_j and v are, so `translate_x` and `translate_y` reach it.
- The only possible new content is the cut points: curve points with a prescribed tangent slope. For
  the parabola base of Y1 these are rational in the slope.
- Contrast the Y1 reformulation, where the new degree growth comes from the √Q_j in the support
  functions of **curved** summands. A polygon has no such term. [Heuristic: for the engine, only a
  curved summand with a non-sqrt algebraic support function would help, and none is drawn.]

## 4. Idealisation under the project's rules

1. **Stroke → outline (disk pen).** This is a real operation: PowerPoint widens the stroke and emits
   it, and the idealisation is exactly the `offset` constructor, with the error shown above.
   - Sign: outside (+d) and inside (−d) are both obtainable. With no fill, one stroke gives both
     boundaries at once.
   - Accuracy: 0.03 pt on the EMF, 0.18 pt on the UI-made freeform's nodes (0.09 % of a 200 pt curve).
   - Radius limit: a stroke wider than the local radius of curvature produces a swallowtail on the
     inner boundary. The nonzero union is still the exact union of disks, so the geometry is a correct
     tube.
2. **Compound lines.** The idealisation is several simultaneous offsets at fixed rational fractions
   of one width, not a new operation.
3. **Dash arclength marks.** A stroke with dash type "dash" and flat caps puts flat cuts at arclength
   k·7w (start) and k·7w + 4w (end), measured from the start of the curve. That is a UI route to
   "points at prescribed arclength from the start", with exact cuts and a fixed arclength-to-weight
   ratio. It is the inverse-arc-length direction of `arc_of_length` and is **outside this stream's
   scope**. It is a rational multiple of the weight, so the arclength is a rational multiple of w.
   Whether it can serve as a constructor is [Open].
4. **Highlighter.** The summand (an axis-aligned 1:2 rectangle) is a fixed shape with exact
   Minkowski semantics, but the centreline is a hand-drawn path and nothing makes it a drawn curve.
   It is not idealisable as an operation on a P-constructible curve. [Heuristic]
5. **Everything else** (Sketched, bevel, glow, soft edge, reflection): raster or random. Not
   idealisable.

None of this concludes anything about the theory's target. Every negative above is scoped to the
operation named.

## 5. Open

- Ink with the Ruler (straight constraint only): not driven. It could not make a curve anyway.
- Brush Pen, Pencil, Text Pen and Galaxy ink: not measured. The Brush Pen might be pressure-varying.
- UI paste-as-EMF of 3-D bevel and contour was not repeated; relies on the COM export and R1 to R3.
- A fully UI-typed weight: the weight was set through COM in most of the survey (Format Shape ▸ Width
  accepts typed numbers). The cap and join changes were UI.
- Whether the shadow-of-stroke route survives a rotated shape (it did for the resize test only).
- Compound lines on text, and WordArt transforms (warps) with a stroke, beyond the WP finding.

## 6. Other things noticed

- Importing a module with top-level code that calls `clear()` deleted my own drawing mid-session; the
  scripts `sv.py` and `u*.py` now keep top-level actions in the UI scripts only.
- `pywinauto` must be imported before any win32com object is created; otherwise the earlier COM
  objects fail with `AttributeError: ...Presentations` (apartment mismatch).
- The Ctrl+1 shortcut did not open the Format pane; right-click ▸ Format Shape... did.
- After clicking a pen twice on the Draw tab, the pen stays active, and a later click on the slide
  draws an ink dot. I removed the dot via COM.
- A stray click on the File tab opened the backstage view; closed with the back arrow.
- Two identical sketched strokes differ, so any use of Sketched style would be seeded by shape identity.
- I left no PPT-UI.lock; the presentation I opened (Presentation52) was closed unsaved. The user's
  six minimised windows and Presentation41 were not touched.
