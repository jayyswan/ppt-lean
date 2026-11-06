# Warp investigation, part 1: the sine glyph under Warped Circle (summary)

Summary of `pptc/PLAN-warp-sine.md`, written 2026-11-03. Sources are `G.md`, `WP.md` and `M.md` in
this folder.

## Verdict

**No exact route to a limaçon or rose.** Per the user's rule, the idealization applies only to the
glyph's centreline, so the result of part 1 is negative.

## Findings

- **The glyph [G, Measured + Wolfram].** 〰 (U+3030) in Yu Mincho is one contour of quadratic
  Béziers spanning two periods.
  - Its edges are **normal offsets** of a common spine, with normal width w/H = 0.188.
    - The normal-offset model leaves a residual of 2.1 units; a vertical-shift model leaves 13.
    - This confirms the deck's assumption.
  - The spine is a sine to within 1–2 % of its amplitude (0.2–0.6 % at the extrema). This
    replaces P1b's 12–19 %, which was measured on the wrong glyph (U+223F).
  - **Sweep:** 1187 outlines across 16 code points. No installed glyph has edges that are exact
    vertical shifts or exact sines.
- **The warp [WP, Measured].** The whole-row polar map holds on Warped Circle, Arch: Warped and
  Arch: Warped Down, for rows of 1–4 glyphs.
  - Corners are accurate to 0.04–0.08 pt.
  - Between nodes the error is 0.30–0.61 % of R, much tighter than the spiral's figures.
- **Exact images [M, Wolfram].**
  - The spine's image is a rose, `r = 3R/4 + 0.2027R·cos(mφ)`, with m = 2n (Warped Circle) or 4n
    over a half turn (arches).
    - It is algebraic of degree 4n+2; for n = 1 it is an irreducible sextic.
    - m = 1, a limaçon, is impossible from 〰.
  - The two warped edges are transcendental polar graphs.
- **Recovery is impossible** [M, Proof, within the project's operations].
  - An offset of a warped edge cannot be the rose, because the warp is not conformal.
  - Every other available operation on the band (sub-arcs, boundary pieces, affine maps, offsets)
    yields pieces of transcendental curves, never the algebraic rose.
  - Intersections, boxes and arc lengths return only numbers.
  - Text Outline is stroked *after* the warp at constant plane width [WP], so the deck's
    stroke trick cannot be done in glyph space.
  - Merge Shapes ignores outlines. No UI path warps a freeform.
- **Gaps, for the record only** (% of R):
  - best constant offset of an edge: 0.33–1.06;
  - radial midpoint of the two edges: 0.119;
  - best pure rose fitted to an edge: 0.935.
- **By-products.** The ● crescent is a transcendental polar ellipse. Font ● glyphs are
  quadratic-spline approximations, 0.10–0.30 % off a circle, so the crescent is not idealizable
  either.

## Open

- **Part 2 (only if the rose matters):** can roses or limaçons be built from the existing base
  curves *without* a warp? What algebraic numbers would they add beyond `poly_graph` (degree ≤ 6),
  `DegreeSeven.lean` and trisection?
- The only exact warp route would be a glyph whose edges are exact vertical shifts of its spine.
  None is installed.
- WP did not reproduce the deck's paste-as-EMF-twice stroke-to-shape step. This does not affect
  the verdict.
