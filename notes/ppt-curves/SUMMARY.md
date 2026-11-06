# Tan-carrying curves in PowerPoint: summary

Summary of `pptc/PLAN-ppt-tan-curves.md`, written 2026-11-04. Sources: `M.md`, `P1.md`, `P1b.md`,
`P3.md` (wave 1); `P3b.md`, `P4.md`, `P5.md` (wave 2). Related surveys: `notes/spiral/SUMMARY.md`,
`notes/warp/SUMMARY-part1.md`, `notes/offset-inversion/SUMMARY.md`.

## Verdict

**The Archimedean spiral is the only wishlist curve PowerPoint draws.** It is idealizable,
category (b). Everything else is not found, or reduces to existing constructors. The curves that
would unlock the named problems are the catenary, the log-cosine and the circle involute (for
`tan x = x`, the beams and the goat problem). None has a UI route.

## Wishlist status

| Curve | Status | Evidence |
|---|---|---|
| Archimedean spiral | **reachable, (b)**: Warped Circle and the Arch Pour presets on straight glyph edges | P1, F1; the constructor decision is pending (spiral `D.md`) |
| circle involute | not found | P1, P4, P5 |
| catenary | not found | P3 (no `cosh` from charts), P4, P5 |
| `tanh` / logistic | not found; Gompertz `a·exp(c·2^u)` exists but does not help | P3, P3b |
| `y = ln sec x` | not found | P3, P4, P5 |
| quartic `y = x/√(1+x²)` | not found | P3 |
| cycloid / trochoid | only as Bézier motion paths, and those cannot be read off; Kepler class only anyway (M §3.7) | P4, P5 |
| logarithmic spiral | only radar-chart *polygons* (c) | P3 |
| limaçon / rose (added) | a warped sine glyph gives an exact rose only for the spine, which cannot be recovered [Proof] | warp part 1 |

## Other things catalogued (all negative or already covered)

- **Text warps** (P1, F1, warp part 1). The warps are ruled maps between two guide curves. On
  straight guides a straight stroke becomes a parabola (already reachable). Pour presets give the
  spiral. Follow Path moves each glyph rigidly.
- **Charts** (P3, P3b). Trendlines are exact (a).
  - Exponential trendlines are affine images of `exp_two`.
  - A power trendline with a data-determined irrational exponent (for example log₂3) is a new
    curve, but its crossings with lines, `exp_two` and power laws reduce to existing exponential
    curves. Other crossings give unnamed classes.
  - Every reachable trendline parameter is P-constructible.
- **Shape presets** (P4). All 186 are built from lines, `arcTo` arcs and Béziers. Their guide
  numbers at default handle values are P-constructible. PowerPoint renders them to spec within
  0.12 pt.
- **Motion paths** (P4, P5). They are stored as rounded Bézier strings. No snap or read-out
  channel exists: P5 tried 54 drags.
- **Shadows** (P5, the user's EMF idea).
  - Opaque, unblurred shadows become vector shapes after paste-as-EMF and ungrouping twice.
    Blurred or semi-transparent ones stay raster.
  - Perspective shadows are exactly **affine** (shear plus scale), not projective. Their
    parameters are rational degrees and percentages, so they add nothing.
- **Curve tool / smooth points** (P5). They make Catmull-Rom Bézier chains with natural ends.
  **SmartArt** cycle layouts place nodes exactly on a circle at 360°/n. **Equation glyphs** are
  fixed polygon or quadratic designs. **3-D** output is raster or projected rectangles (notes/3d).

## Open

- Several P5 items were reasoned rather than driven in the UI: ink, typed equations, Morph,
  3-D models, picture tools, and text effects on converted text.
- P3b's fill-handle rules were tested with `Range.AutoFill`, not with a real mouse drag.

## Constructor drafts for the user

Only one: the Archimedean spiral. Its form and the decisions it needs are in
`notes/spiral/D.md` and `notes/spiral/SUMMARY.md` §4.
