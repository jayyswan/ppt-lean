# PLAN-ppt-tan-curves: can the PowerPoint UI draw a "tan-carrying" curve?

Several famous equations are blocked by the lack of one curve each. Examples are `tan x = x`,
the cantilever beam, the goat problem, and the inverse involute function (see
`notes/offset-inversion-tangent-angle.md` and `notes/sheared-sine-intersections.md`).

**No such curve may be assumed.** A curve becomes eligible for `Defs.lean` only if a
**UI-only** PowerPoint route draws it *exactly, under an idealization the user accepts*.
Adding it to `Defs.lean` is the user's decision, never a probe's.

This plan finds the candidate routes and collects the evidence for that decision.

## 1. Rules for every probe

- **Constructions must be UI actions.**
  - Clicking buttons, menus and spinner arrows counts.
  - Typing numbers into boxes does **not** count, and neither does typing into a chart's data
    sheet.
  - Excel fill-handle series made from existing cells are fine. Clearing cells is fine.
- **Observation only.** COM, VBA, XML and scripts may be used to *observe*: read geometry
  back, export, measure, screenshot. They may never be used to *construct* a capability. If a
  route needs a COM-only property, the verdict is "not UI-reachable".
- **Idealization standard.** Report which of these applies:
  - (a) the spec or documented algorithm defines the exact mathematical curve, and the render
    matches it to render precision; or
  - (b) PowerPoint stores or renders an approximation, for example a Bézier fit, of an ideal
    curve; or
  - (c) neither.

  Quote ECMA-376 / [MS-ODRAWXML] / [MS-OI29500] where they apply. Precedent: trendlines are
  idealized as exact (category a). The user decides whether (b) is acceptable; probes only
  report.
- **Evidence.** For each candidate:
  - the exact click path;
  - read-back geometry (node count, Bézier control points, or sampled outline);
  - the max and rms residual against the ideal curve and against the best Bézier/arc
    explanation;
  - screenshots.

  Earlier probes are the model: `notes/3d-rotation-*.md`, `notes/trendline-origin-*.md`.
- Do not modify `ppt-sim`. Do not kill python/node/uvx processes. Work in a fresh scratch
  `.pptx` under the session scratchpad.
- One probe per agent. Each keeps `HANDOFF-ppt-<id>.md` at the repo root and writes
  `notes/ppt-curves/<id>.md`, which must start with a verdict line.

## 2. The wishlist (stream M confirms and ranks it)

| Curve | Unlocks | Via | Status of the claim |
|---|---|---|---|
| **Archimedean spiral** `r = aθ` (any affine image) | `θ·tan(θ − α) = 1`, so `x tan x = 1` (Robin/Biot at `Bi = 1`) and `tan x = k − x` | box of a rotated spiral | [Wolfram] for `α = π/2` (`tan θ = −θ`); general `α` [Proof, by differentiation] |
| **circle involute** `(cos θ + θ sin θ, sin θ − θ cos θ)` | `tan x = x` (crosses the x-axis); goat problem (crosses `y = π/2`) | intersection with a line | [Wolfram] |
| **catenary** | `tan x = λx`, inverse involute function `tan α − α = c` | offset inversion (Whewell `s = a tan ψ`) | [Proof] |
| **`tanh` / logistic graph** | cantilever beam (`sin x = tanh x`) | intersection with the sine | [Wolfram] |
| **`y = ln sec x`** | beam family `x + gd x = c` | offset inversion | [Proof] |
| **quartic `y = x/√(1+x²)`** | `tan x = ±x` | intersection with the sine | [Wolfram] |
| **cycloid / trochoids** | "sin and cos together" intersections (classify) | intersection | [Open] |
| **logarithmic spiral** `r = e^{kθ}` | products `e^{kθ}·trig θ` | intersection / box | [Open] |

Note: the `tan x = x` claim for the spiral was checked and is **wrong**. The spiral's box
gives `tan x = −x`, not `+x`. Keep that correction.

## 3. Streams

| id | kind | question | priority |
|---|---|---|---|
| M | math (no PowerPoint) | Confirm every wishlist row; add rows for anything else that would unlock a named target; rank by payoff. Merge with `PLAN-offset-inversion` R5/S when they land. | 1 |
| P1 | probe | **Text warps.** Does WordArt *Transform → Follow Path* (Arch, Circle, Button) or a *Warp* preset map glyph geometry by an exact polar map, *θ* linear in the baseline coordinate and *r* linear in the glyph height? | 1 |
| P2 | probe | **Text → shape conversion.** Can warped text be turned into a shape that the other operations accept (Merge Shapes → freeform; or used directly in intersect/fragment), and is the conversion exact or a Bézier fit? | 1 (with P1) |
| P3 | probe | **Charts.** Can any combination draw `cosh`, `tanh`, a logistic curve, or `ln cos` exactly? | 2 |
| P4 | probe | **Preset geometry and motion paths.** Are any presets exact spirals, cycloids or catenaries? | 3 |
| P5 | probe | **Anything else in the UI that maps one curve onto another.** | 3 |

### P1 + P2 detail: the spiral lead

**Why it might work.** A *Follow Path: Circle/Arch* warp should send the text baseline to a
circular arc, with glyph height along the radius. A **straight slanted stroke** in a glyph
would then become an **Archimedean spiral arc**, `r = r₀ + c·θ`. Candidate strokes:

- `/` or `╱`;
- an italic `l`;
- an underline or strikethrough (these give concentric arcs; useful as a control);
- a character rotated by a spinner.

**Determine:**

1. **The exact warp map.**
   - Sample the converted outline of an underline (expect a circle), of a vertical bar (expect
     radial segments), and of a slanted stroke (expect a spiral).
   - Fit each to the polar-map hypothesis; report residuals.
   - Compare with the `prstTxWarp` definitions in ECMA-376 Part 1 §20.1.10.76 and the preset
     geometry XML for `textArchUp`, `textCircle`, `textButton`.
2. **Glyph content.** Is the stroke actually straight in the font's outline? Read the glyph
   outline: TrueType quadratics, CFF cubics. Prefer a font whose `/` is a polygon.
3. **Conversion** (P2). Use Merge Shapes (Union/Fragment/Intersect) with the warped text box
   to obtain a freeform.
   - Is the result's geometry the exact spiral (impossible as Béziers, so the question is
     category (a) versus (b)), or a Bézier fit with what tolerance?
   - Does PowerPoint keep the warp live, so the operations act on ideal geometry, or bake it?
4. **Can the parameters be set without typing numbers?** Check spinners, presets and
   adjustment handles. Note whether the warp's adjustment handle reaches P-constructible
   values only through dragging. Dragging is not exact; say what *is* exact.
5. **Other warps.** Repeat for the *Warp* gallery (Wave, Inflate, Can, …).
   - If a warp maps glyphs along a Bézier guide path with normal displacement, a slanted
     stroke gives a "linearly varying offset" `B(u) + (a u + b)·ν(u)`. That is a new curve
     type even if it is not a spiral. Record its exact form.

### P3 detail: charts

- Enumerate trendline types (linear, exponential, logarithmic, polynomial ≤ 6, power, moving
  average) against axis options:
  - log x base 2/10;
  - reversed order;
  - secondary axes;
  - date axis;
  - display units.
- Also try stacked line/area charts. Does a trendline on a stacked series fit the *stacked*
  values? Does any chart type add or multiply two series as functions rather than as data
  points?
- Targets: `cosh` (that is, `2^x + 2^{−x}`), `tanh`, `1/(1+e^{−x})`, `ln cos x`, `x/√(1+x²)`.
- Known limits (memory): only the x-axis can be logarithmic, bases 2 and 10, so the new curves
  are `y = p(2^x)` and `a·exp(k·2^x)`. Do not re-derive these; look for what they *combine*
  with.
- Data must come from the fill handle.

### P4 detail: presets

- Check the definitions of the motion-path presets "Spiral Left/Right", "Loop de Loop",
  "Sine Wave", "Bounce", and the shape presets (wave, double wave, arc, block arc, chord):
  - DrawingML `arcTo` is an exact elliptical arc;
  - a `cubicBezTo` is only a Bézier.
- A preset counts only if it is defined exactly. Report category (a), (b) or (c) for each.

### P5: open sweep

- Shadows (perspective shadows: vector or raster?), reflections, Morph, SmartArt layouts,
  ink-to-shape, the Draw tab's ruler, equation objects, 3D models.
- Earlier work found that 3-D rotation with perspective is **raster only**
  (`3d-rotation-C-baking.md`). Do not redo that; only note genuinely new routes.

## 4. Order and hand-off

1. **Wave 1:** M, P1+P2 (one agent, or two working closely), P3.
2. **Wave 2:** P4, P5, plus follow-ups on any (a)/(b) hit.

The orchestrator writes `notes/ppt-curves/SUMMARY.md`:

- each wishlist curve: reachable / approximate / not found, with evidence;
- for each hit, the exact proposed constructor statement *as a draft for the user*, plus what
  it would unlock (from M).

Nothing goes into `Defs.lean` without the user's explicit decision.
