# PLAN-3d-rotation: a full survey of PowerPoint's 3-D features

Read this first, every task.

**Goal: characterize the 3-D feature set completely.** That means:

- what it does to geometry;
- what geometry or numbers can be read back from it, and how exactly;
- what the readable outputs make constructible.

This is a **survey, not a hunt**. No equation or named constant is the success criterion. A
stream that finds something which fails to reach some favourite target has still found
something: record it in full. Named problems show up only as entries in the catalogue that the
math streams build, never as a filter on which paths to explore.

**Prior work:**

- `notes/3d-rotation-A-formula.md`: storage and the fitted projection formula.
- `notes/3d-rotation-B-conic.md`: the render is a homography of the 4-Bézier outline.
- `notes/3d-rotation-C-baking.md`: no vector geometry came out of any export; EMF/SVG/PDF were
  raster.

C tested exports for *vector paths* and concluded "no snapping". The user has since found that
*Copy → Paste Special → Picture (Enhanced Metafile)* gives a picture whose frame bounds the
**visual edges** of the rotated shape. So at least one numeric read-out exists. The prior
negative verdicts should be read as "not found by those routes", not "impossible".

## 1. Ground rules

- **UI-only constructions** (memory `ui-only-constructions`):
  - clicks, menu items, galleries and spinner arrows count;
  - typing numbers into boxes or into a chart's data sheet does not;
  - fill-handle data from existing cells is fine;
  - **constructions stay inside PowerPoint.** Round trips through Word, Excel, OneNote, Paint,
    Photos or any other app do not count (user rule, 2026-11-03).
- COM, VBA, XML and scripts are for **observation only**: reading frames back, exporting,
  measuring. A capability that needs COM or XML to *set* something is "not UI-reachable".
  Record it anyway, marked as such, because the observation may still be informative.
- **Idealization categories,** reported for every read-out:
  - (a) defined exactly by spec or documented algorithm, and matched by the render;
  - (b) an approximation of an ideal (pixel-quantized, unit-quantized, Bézier-fitted), with
    the error measured *and its scaling*: does it shrink with zoom, export DPI or shape size?
  - (c) neither.

  The user decides what to accept. Precedent: trendlines are idealized as exact.
- **Report everything.** Every stream ends with a section "Other things noticed". Unexpected
  behaviour, dead ends and partial effects all go there. Do not drop a path because it does not
  serve another stream's question.
- **Nothing goes into `Defs.lean`.** Draft constructors are for the user to judge.
- Probes work in fresh scratch `.pptx` files under the session scratchpad. Close only the
  presentations they opened. Never kill python/node/uvx processes. Do not modify `ppt-sim`.
- Math streams use Wolfram (one call per computation; session state does not persist).
  Image and contour fitting may use Python (numpy), as in probes A–C. Say which backend
  produced each number.
- One agent, one deliverable.
  - Progress log: `HANDOFF-3d-<id>.md` at the repo root.
  - Output: `notes/3d/<id>.md`, starting with a summary of findings.
  - Label every claim [Measured], [Spec], [Proof], [Wolfram], [Heuristic] or [Open].

## 2. Streams

Three layers:

- **Mechanics:** what 3-D does.
- **Read-outs:** what numbers or geometry come back out.
- **Mathematics:** what those read-outs make constructible.

The layers run in parallel. The math streams work from the *idealized* model and are refined as
the probes land.

| id | layer | question |
|---|---|---|
| M1 | mechanics | The complete UI parameter space of 3-D Rotation and 3-D Format |
| M2 | mechanics | The exact geometric model of rotation + camera, for every camera type |
| M3 | mechanics | The geometry of depth, bevel, contour, material/lighting and surface effects |
| M4 | mechanics | Which object types accept 3-D, and how 3-D interacts with groups, text, 2-D rotation, flips, effects |
| R1 | read-out | The paste-as-EMF frame (the user's lead), fully characterized |
| R2 | read-out | Every other paste/export/save route and what its output's frame or content records |
| R3 | read-out | Interaction channels: snapping, smart guides, align/distribute, groups, selection handles, Size & Position, Morph, Merge Shapes |
| X1 | math | A geometric catalogue: the images of every drawable curve under every reachable camera |
| X2 | math | Box read-outs: the full class of numbers that boxes of the X1 images produce |
| X3 | math | Further operations on images, *conditional* on R2/R3 finding them: intersections, arc lengths, offsets, nesting |
| X4 | math | Extruded and beveled geometry: silhouettes, and what their boxes produce |
| X5 | math | Composition with the existing constructors: what multi-step constructions gain from one 3-D step |
| D | synthesis | Draft constructors, and the decision packet for the user |

**Ordering:**

- M1–M4, R1–R3 and X1 start at once.
- X2 needs M2 (its idealized form can start immediately).
- X3 needs R2 and R3; X4 needs M3; X5 needs X2.
- D runs last.

### M1: UI parameter space

Map everything that clicks can produce.

- **Format Shape → Effects → 3-D Rotation:**
  - preset galleries (Parallel, Perspective, Oblique): the stored `prst`, `lat/lon/rev` and
    `fov` of each (read from the saved XML);
  - the X/Y/Z rotation and Perspective spinners: step, range, wrap-around, value-dependent
    steps, modifier keys;
  - "Keep text flat" and "Distance from ground";
  - "Reset".
- **3-D Format:** bevel top/bottom (types, width/height spinners), depth, contour, material,
  lighting (rig and angle).
- **Combinations.** Which sets of parameter values are reachable: preset plus spinner lattices,
  the set generated by presets and spinners together? Which values are algebraic? Which camera
  type does the UI create: legacy (ignores `rev`, per probe A) or `perspectiveFront`? Does
  that depend on the route?
- Also the **3-D-model** insertion features and the **Morph** transition, insofar as they move
  3-D objects. Note them and characterize them at a high level.

### M2: the exact geometric model

Refine probe A's formula until every part is either pinned exactly or bounded:

- **The constant `k ≈ 453.5 pt`** (`d = k / tan(fov/2)`). Is it exactly 16 cm (5,760,000 EMU)?
  Search the spec, Microsoft docs and fits on exactly computable test shapes.
- **The projection centre** for closed shapes, open paths, asymmetric curves, groups and pictures:
  the bbox of geometry, of control points, or including stroke?
- **Oblique cameras, isometric presets and orthographic ones:** are they all affine?
- **Behaviour near and beyond the vanishing plane,** and for points behind the camera: clipping,
  refusal, wrap-around.
- **Extrusion (`z`, depth):** the full 3-D-to-2-D map for points off the shape plane.
- Quote ECMA-376 Part 1 §20.1.5 (`scene3d`, `camera`, `rot`, `lightRig`), §20.1.5.12
  (`sp3d`), and [MS-ODRAWXML].

### M3: depth, bevels, contour, surface

What geometry does each produce?

- Extrusion of curves: closed and open, filled and unfilled.
- Bevel profiles (circle, relaxed inset, cross, angle, soft round, convex, slope, …) at given
  width and height. Is a bevel an offset in 3-D, a sweep of a profile curve, or something else?
- Contour lines.
- Interaction with perspective.
- Silhouettes and visible-edge rendering.

Also: does lighting or material change the *visual edges* that read-outs see (for example,
dark edges against a white background)?

### M4: objects and interactions

For each object type:

- preset shapes, including the **wave** preset (the project's `sine` idealization) and the arcs;
- lines and open paths;
- freeforms and curves;
- text boxes and WordArt;
- groups;
- **pictures**, including charts pasted as EMF, so that trendline curves can be rotated;
- SVG icons;
- tables;
- charts themselves.

record:

- whether 3-D Rotation and 3-D Format are available;
- whether the render is a homography of the drawn geometry or of the frame;
- how 3-D interacts with 2-D rotation, flips, crop, transparency, shadows, glow, soft edges,
  reflections and text effects.

### R1: the paste-as-EMF frame

Route: select → Copy → Paste Special → *Picture (Enhanced Metafile)*. Characterize the frame
completely:

1. **What it bounds.** Compare `Left/Top/Width/Height` (read by COM) with exact projected
   bounding boxes computed from M2, for:
   - polygons;
   - ovals (4-Bézier outlines);
   - open strokes;
   - filled and unfilled shapes;
   - thick and thin lines, round and square caps;
   - shapes with effects (shadow, glow, soft edges, reflection, bevel, depth).

   Candidate explanations:
   - exact geometric bbox;
   - bbox of rendered non-transparent pixels at some DPI;
   - EMF header `rclBounds` (device units) or `rclFrame` (0.01 mm);
   - any of these padded by stroke, anti-aliasing or effect extents.
2. **Quantization and scaling.** How does the error depend on zoom, Windows display scaling, the
   `ExportBitmapResolution` registry setting and shape size? Does it converge?
3. **Repeatability** across pastes, reopening the file, machines and GPU settings.
4. **Content.** Look inside the pasted EMF (inspection only): raster, vector, or both?
   Ungrouping behaviour.
5. **Usability.** Can other shapes snap to or align with its edges, so that the read-out
   becomes a line usable in later constructions, by UI actions alone?
6. **Unrotated shapes.** Does the frame also give visual-edge boxes of *non*-3-D shapes with
   effects, for example the extent of a glow (an offset), a shadow, or a soft edge? Those
   would be new read-outs independent of 3-D. Record them.

### R2: every other output route

For each 3-D object, test:

- Paste Special (PNG, JPEG, GIF, SVG, "Picture", "Microsoft Office Graphic Object");
- Save as Picture (all formats);
- export to PDF/XPS/video;
- Copy into Word or Excel and back;
- "Convert to Shape" on SVG;
- picture crop tools ("Crop to fit", "Fill", "Crop to Shape") and "Remove Background";
- picture compression and reset.

For each, record the frame rule and whether any vector projected geometry appears. Record
every route that gives *any* bound, edge or point read-out, not only those matching R1.

### R3: interaction channels

Do any of these respond to the *projected* geometry rather than the flat outline?

- smart guides and snapping (to objects, to grid);
- Align/Distribute;
- group bounding boxes when a 3-D shape is grouped with a flat one;
- selection handles;
- the Size & Position pane;
- Merge Shapes with EMF or PNG pictures of 3-D shapes;
- ink-to-shape and freeform drawing with snapping;
- Morph between 3-D states;
- the Selection Pane.

Any channel that yields **vector** projected geometry or **points** (not just boxes) widens X3.

### X1: geometric catalogue (Wolfram)

For each drawable curve type:

- line, ellipse, rectangle;
- polynomial graph ≤ 6;
- power law;
- cubic Bézier (as PowerPoint stores it);
- `exp_two`;
- `sine` (and the wave preset's actual geometry);
- offsets of each;
- multi-Bézier outlines such as the oval;

and for each camera class from M1/M2 (orthographic/oblique: affine; perspective: homography;
any others found), describe the image:

- parametrization, implicit degree, singularities;
- asymptotes and the vanishing line;
- which images are new curves relative to the existing constructors, and which reduce to
  existing ones (a conic to a conic, for instance).

Include the dependence on placement. The projection centre is the shape's bbox centre, so
translations and scalings before rotation move the vanishing line relative to the curve.

### X2: what box read-outs produce

Model: the box (`max`/`min` of a slide coordinate) of `H(A)` for a compact arc `A` of a
drawable curve and a reachable `H`. A projected coordinate is a ratio `N/D` of affine
functions, so its extremes solve `N'D − ND' = 0`.

For every row of X1, give:

- the critical equation, in normal form;
- its classification (algebraic of what degree; transcendental, and which kind);
- whether it is already reachable by existing constructors;
- the *full family* of new equations, with the parameters that the reachable cameras and
  placements control.

Also handle extremes at arc endpoints, at cusps of offsets, and at the vanishing line.

For orientation only: an example row is the sine arc `(t, sin t)`, whose critical equations
form the family `(t + p) cos t − sin t = q` [Wolfram]. Treat it as one entry, not as the
purpose of the stream. Report families in full, including those that give nothing named.

### X3: other operations on images (conditional)

If R2 or R3 finds vector geometry, points or snapping on projected images, work out what
intersections, arc lengths, `arc_of_length` inversions and offsets of images produce. Use
`H(C₁) ∩ C₂ = H(C₁ ∩ H⁻¹C₂)` to reduce to pre-images where that helps.

If nothing is found, write down in full what *would* follow, so that a later probe hit can be
evaluated at once.

### X4: extruded and beveled geometry

From M3's model, describe:

- the silhouette of an extruded curve: front and back images plus tangent segments?
- the geometry of bevel profiles;
- what boxes of these produce: maxima over several homographies, envelopes, common tangents.

### X5: composition

How does one 3-D read-out combine with the existing constructors across several steps?

- Read-outs used as later parameters.
- Several 3-D steps in a row: camera then box, then the box value used to place the next
  curve.
- 3-D read-outs combined with `arc_of_length`, offsets and intersections.

Where does the composite class sit relative to the structure of
`notes/offset-inversion-tangent-angle.md` §2 (equations in `(u, eᵘ)`, `(t, sin t)` and
`(u, gd u)`)? Does 3-D add new *kinds* of equations, or only new members of known kinds?

### D: decision packet

Write `notes/3d/SUMMARY.md`:

- every read-out channel found, with its exact UI steps, precision class, and evidence;
- the reachable camera set;
- the geometric catalogue (X1) and the capability catalogue (X2–X5) as tables;
- draft constructor statements for each plausible channel, with exact hypotheses (camera set,
  placement, in-front-of-camera condition, stroke handling);
- what each draft would add, listed broadly;
- the risks and the open items.

Cross-link `PLAN-ppt-tan-curves.md` and `PLAN-offset-inversion.md`.
