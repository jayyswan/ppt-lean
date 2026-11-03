# PLAN-3d-rotation: how 3-D rotation works, and what it can construct

Read this first, every task.

**Prior work:**

- `notes/3d-rotation-A-formula.md`: storage and the fitted projection formula.
- `notes/3d-rotation-B-conic.md`: the rendered image is a true homography of the 4-Bézier
  outline.
- `notes/3d-rotation-C-baking.md`: no route gave vector geometry, and EMF/SVG/PDF output is
  raster.

**New input from the user.** Copy a 3-D-rotated shape, then *Paste Special → Picture (Enhanced
Metafile)*. The pasted picture's frame is a **bounding box around the visual edges** of the
rotated shape. That is the box (`box_xmax`/`box_ymax`) of a projective image. Probe C saw this
(the EMF picture was about 206.6 × 130.6 pt against a projected bbox of about 205.8 × 129.6 pt)
but did not pursue it. What determines that frame exactly is the central open question.

## 0. Why it matters: the prize [Proof + Wolfram]

A perspective camera maps a flat shape by a homography. Every projected coordinate is a ratio
`N/D` of affine functions of the shape's own coordinates. The box of a projected curve is
therefore an extreme of a *ratio*, and the critical-point equation of a ratio couples the
parameter with its trig functions in a way no affine box can.

**The sine.** Project the arc `(t, sin t)`. With vanishing line `D = 0` and offset `γ`, each
projected coordinate has the form `(αt + β sin t + γ)/(g t + h sin t + k)`. Its critical points
satisfy

  `(βg − αh)(t cos t − sin t) + (βk − γh) cos t + (αk − γg) = 0`.

That gives:

- **`tan x = x`.** Put the vanishing line through the sine's `t = 0` (`k = 0`, `γ = 0`).
  - The extreme of `sin t / t` on a window around `7.725` is at the root of `tan t = t`
    [Wolfram: 22 digits].
  - The same holds for a simulated camera: rotation `φ = 50°` about the vertical axis, fov
    `120°`, curve positioned so that the vanishing line meets `t = 0` [Wolfram: 22 digits].
  - The box value is `V = (d / sin φ)·cos t*`, so `t* = 2π + arccos(V sin φ / d)` is
    P-constructible once `V` is.
- **The goat-grazing problem,** `sin β − β cos β = π/2`. Same set-up with a vertical offset:
  the extreme of `(sin t − π/2)/t` is at `β = 1.905695729309883894…` [Wolfram: 32 digits].
- More generally, the family `(t + p) cos t − sin t = q`, for example `tan x = x + p`.

**What this does not give.** `tan x = λx` with `λ ≠ 1` (the combination always has slope 1),
and the cantilever beam (it needs exp and trig together). Stream B1 must confirm both.

**This is conditional on four things the probes must establish:**

1. some UI route reads off the projected box (the EMF trick, or another);
2. its precision can be idealized as exact, which is the user's decision;
3. the needed camera is UI-reachable;
4. the sine (and other drawable curves) exists as an object that accepts 3-D rotation and whose
   visual edges are the curve itself.

## 1. Ground rules

- **UI-only constructions** (memory `ui-only-constructions`):
  - clicks, menu items, galleries and spinner arrows count;
  - typing numbers into boxes or into a chart's data sheet does not;
  - fill-handle data from existing cells is fine.
- COM, VBA, XML and scripts are for **observation only**: reading frames back, exporting,
  measuring. A capability that needs COM or XML is "not UI-reachable".
- **Idealization categories,** reported for every channel:
  - (a) defined exactly by spec or documented algorithm, and matched by the render;
  - (b) an approximation of an ideal (pixel-quantized, unit-quantized, Bézier-fitted), with
    the error measured *and its scaling* (does it shrink with zoom, DPI or shape size?);
  - (c) neither.

  The user decides what to accept. Precedent: trendlines are idealized as exact.
- **Nothing goes into `Defs.lean`.** The B5 deliverable is only a *draft* constructor for the
  user.
- Probes work in fresh scratch `.pptx` files under the session scratchpad. Close only the
  presentations they opened. Never kill python/node/uvx processes. Do not modify `ppt-sim`.
- Use Wolfram for every mathematical identity, in one call per computation. Python (numpy) is
  fine for image and contour fitting, as in probes A–C. Say which backend produced each number.
- One agent, one deliverable.
  - Progress log: `HANDOFF-3d-<id>.md` at the repo root.
  - Output: `notes/3d/<id>.md`, starting with a verdict line.
  - Label every claim [Measured], [Spec], [Proof], [Wolfram], [Heuristic] or [Open].

## 2. Streams

| id | wave | kind | question |
|---|---|---|---|
| A1 | 1 | probe | The exact UI parameter space of 3-D rotation |
| A2 | 1 | probe + spec | The exact projection formula, the constant `k`, clipping |
| A3 | 1 | probe | **The EMF frame:** what bbox it is, and how exact |
| A4 | 1 | probe | Which objects accept 3-D, and what their "visual edges" are |
| B1 | 1 | math | What boxes of projective images solve, for every drawable curve |
| A5 | 2 | probe | Extrusion, bevel, contour, shadow, reflection under 3-D |
| A6 | 2 | probe | Other read-out channels: snapping, align/distribute, groups, selection handles |
| B2 | 2 | math | Reachability of the needed cameras, given A1's discrete parameter set |
| B3 | 2 | math | Intersections and arc lengths of projective images (only if A6 finds vector geometry) |
| B4 | 2 | math | Boxes of extruded/beveled shapes (needs A5) |
| B5 | 3 | math + Lean sketch | Draft constructor(s) and a proof outline for `tan x = x` and the goat problem |
| S | 3 | synthesis | `notes/3d/SUMMARY.md`: the decision packet for the user |

Wave 1 runs in parallel, A3 has top priority. Wave 2 starts as its inputs land.

### A1: UI parameter space

Map exactly what clicks can produce in **Format Shape → Effects → 3-D Rotation** and
**3-D Format**:

- **Preset galleries:** Parallel, Perspective, Oblique. For each preset, give its stored camera
  `prst`, `lat/lon/rev` and `fov`. Read the XML of a saved copy. For example, is the
  isometric angle `35.264°` or `35°`?
- **Spinners:** X, Y, Z rotation and Perspective. Give the step size, the range, wrap-around,
  whether the step depends on the current value, and whether shift/ctrl-click changes it.
- **Combinations.** Can a preset followed by spinner clicks reach angles off the spinner
  lattice? Does the gallery's starting angle plus `n` steps give a lattice like
  `35.264° + n°`?
- **Other controls:** "Keep text flat", "Distance from ground", depth, bevel, contour,
  material, lighting.
- **Camera type.** Which camera does the UI create: legacy perspective (ignores `rev`, per
  probe A) or `perspectiveFront`?

Deliverable: the exact set of reachable `(prst, lat, lon, rev, fov, z)`, and whether each value
is algebraic (whole degrees give algebraic sines and cosines).

### A2: the projection formula, exactly

Start from probe A's formula. Pin down:

1. **The constant `k ≈ 453.5 pt`** (`d = k / tan(fov/2)`).
   - Search the spec and Microsoft docs.
   - Test whether `k` is exactly `5,760,000 EMU` (16 cm) or depends on anything: zoom, slide
     size (A says no), the shape's z-distance.
   - Fit at high resolution with exactly computable test shapes (polygons with known
     vertices).
2. **The projection centre.** Probe A found it is the bbox centre. The bbox of *what*:
   geometry with or without line width? For open paths (arcs, freeform curves), the bbox of
   the path or of its control points? Test an asymmetric open curve.
3. **Interactions:** 2-D `Rotation`, flips, groups (whose centre?), text, "Distance from
   ground".
4. **Near the vanishing plane** (`Z → d`). The prize needs the vanishing line close to the
   curve. Is anything clipped, distorted or refused? How close can the curve get?
5. Quote ECMA-376 Part 1 §20.1.5 (`camera`, `rot`, `fov`) and [MS-ODRAWXML] where relevant.

### A3: the EMF frame (the user's lead)

Route: select the 3-D shape → Copy → Paste Special → *Picture (Enhanced Metafile)*. Also test
Picture (PNG), Picture (SVG), and *Save as Picture*. Questions:

1. **What box is it?** Compare the pasted frame (`Left/Top/Width/Height`, read by COM) with the
   exact projected bbox from A2's formula, for:
   - polygons with known vertices;
   - ovals (the 4-Bézier outline, per probe B);
   - open strokes.

   Candidate explanations:
   - (i) exact geometric bbox;
   - (ii) bbox of rendered non-transparent pixels at some DPI;
   - (iii) EMF header `rclBounds` (device units) or `rclFrame` (0.01 mm);
   - (iv) any of these padded by line width, anti-aliasing or effect extents.
2. **Quantization and scaling.** Is the frame quantized in pixels, in 0.01 mm, or in EMU? Does
   the error change with zoom, Windows display scaling, the export-resolution registry setting
   (`ExportBitmapResolution`), or shape size? A frame that converges to the exact bbox as
   resolution grows supports idealization (b → exact).
3. **Outline versus fill.**
   - With *no fill* and a thin outline, does the frame hug the stroke? It should be the
     geometric bbox grown by half the stroke width. Measure the dependence on width.
   - With *no line*, does a filled region give the exact geometric bbox?
   - What do round caps and joins do at the extremes?
4. **Repeatability:** is the result the same on repeated pastes, after reopening the file, and
   on a different machine or GPU setting? Record the render backend.
5. **Is the frame usable?** Can other shapes snap to its edges, align to it, or be sized from
   it, so that the box becomes a line in later constructions? Only click and drag with snapping
   counts.

Deliverable: the precise rule for the frame, measured error against the exact bbox, its scaling
behaviour, and a proposed idealization class.

### A4: what can carry 3-D, and what its visual edges are

For each object type, record:

- whether 3-D Rotation is available;
- whether the paste-EMF frame hugs the *drawn curve* or only the object's frame or rectangle;
- whether the projection is a homography of the drawn curve.

Object types:

- preset shapes;
- the **wave preset** (the project's `sine` idealization);
- arcs and lines (open paths);
- freeforms and curves (Béziers);
- text boxes;
- groups;
- **pictures**: a chart pasted as an EMF picture, so that trendline curves such as the
  `exp_two` route can be rotated. For a picture with a transparent background, does the frame
  hug the visible curve, or the picture's rectangle? Does cropping change that?

Find out how each base curve of `Defs.lean` (`exp_two`, `sine`, `power_law`, `poly_graph`,
`cubic_bezier`, `ellipse`) can be realized as a 3-D-rotatable object, if it can.

### A5: extrusion and effects

Depth, bevels (top and bottom), contour, materials, perspective shadows and reflections on 3-D
shapes:

- Does the EMF frame include them?
- Is the silhouette of an extruded curve exactly the union of the front and back projective
  images plus their common tangent segments?
- What does a bevel do geometrically? (It is possibly an offset in 3-D.)

### A6: other read-out channels

Probe C found every *export* of a 3-D shape to be raster. Look for anything else that exposes
the projected geometry:

- selection handles;
- smart-guide snapping to the visual edges;
- Align/Distribute (do they use visual bounds for 3-D shapes?);
- grouping a 3-D shape with a flat one (group frame);
- the Size & Position pane;
- Morph;
- Merge Shapes with the EMF picture: does the picture's vector EMF ever contain path records?
- ink or freeform tracing with snapping.

Any channel that yields **vector** projected geometry would unlock B3.

### B1: what projective boxes solve (Wolfram)

Assume an idealized constructor: the box of `H(C)` for a drawable curve `C` and a homography
`H` from the reachable family, with P-constructible placement. Classify the critical equations
for each curve type:

- sine and sheared sines (the §0 family);
- `exp_two` and its affine images;
- polynomial graphs, power laws, Béziers, ellipses (algebraic: does the degree go up?);
- offsets of each of these.

Specifically:

- confirm the §0 results;
- determine whether any choice gives `tan x = λx` (`λ ≠ 1`), `x tan x = Bi`, the cantilever
  beam, or Bessel zeros;
- check the result against `notes/offset-inversion-tangent-angle.md` §3 and
  `PLAN-ppt-tan-curves.md` §2.

Record which named problems become reachable and which camera each needs.

### B2: reachable cameras

From A1's exact parameter set, determine which homographies `H` are available once P-constructible
translations and scalings of the curve, before rotation, are included. Note that the projection
centre is the shape's bbox centre, so placement controls where the vanishing line falls.

- Show that the §0 constructions need only one fixed reachable camera, for example a whole-degree
  rotation about the vertical axis with a preset fov. If so, the discreteness of the spinners
  does not matter.
- Compute exactly what `d` is in that case (it needs A2's `k`), and whether it is
  P-constructible.

### B3: beyond boxes (only if A6 finds vector output)

Intersections, arc lengths and offsets of projective images of drawable curves. What is new?
Note that `H(C₁) ∩ C₂ = H(C₁ ∩ H⁻¹C₂)`, so intersections reduce to those of projective images.
Classify those images.

### B4: boxes of extruded and beveled shapes (needs A5)

If the silhouette is the union of two projective images, the box is a max over two homographies
with different denominators. Does that add anything beyond B1? What about bevels?

### B5: draft constructor and proof sketch

Write, *for the user to judge*:

1. The minimal constructor that the confirmed channel would justify, for example:

   > the `box_ymax` of `H(A)`, for a compact drawable `A` and `H` in the reachable camera
   > family.

   Include its exact hypotheses: camera set, placement, the requirement that the whole arc
   stays in front of the camera, and how stroke width is handled.
2. A proof outline for:
   - `tan x = x`: the extreme of `sin t / t` on a window, uniqueness, and recovering `t` with
     `arccos`;
   - the goat problem;

   each with an estimated Lean size.
3. What the constructor would *not* give (from B1).

No edits to `Defs.lean`.

### S: synthesis

Write `notes/3d/SUMMARY.md` as the decision packet:

- each read-out channel, with its precision class, the exact UI steps and the evidence;
- the reachable camera set;
- the draft constructor or constructors;
- what each would unlock, ranked;
- the open risks.

Cross-link `PLAN-ppt-tan-curves.md`. A 3-D route to `tan x = x` makes that plan's quartic and
involute probes less urgent, and that plan should be re-prioritised accordingly.
