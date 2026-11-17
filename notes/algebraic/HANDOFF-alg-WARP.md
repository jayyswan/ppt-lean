# HANDOFF: WARP

Status: **research note done** (`WARP.md`); planned as stream **W4** in
`PLAN-algebraic.md`; **W4a done** (`W4-offset.md`, offset route closed); Lean bridge
partial, scratch only.

## Findings

- A single warped glyph is a rational quartic/cubic; line and conic intersections are
  degree ≤ 4/≤ 8 over F, already covered by `root_Pconstructible_le_six_coeffs` and
  `root_Pconstructible_deg8_coeffs`. No new numbers from one warp.
- New engines: egg × quintic graph (degree 10, monic rank F = 9) and egg × sextic graph
  (degree 12, F = 10). The first is one parameter better than the MI-1 sextic engine; the
  second is still below H5's F ≥ 11 for totally real decics.
- Wolfram rank table is in `WARP.md` §4 (stable at four random points).

## Lean scratch

- `Pptc/Scratch/WarpText.lean`: one-`●` bridge. Proves the affine description of
  `RowGlyph.toSet` and `inkNormalize_blackCircle` (single black circle normalizes to
  `glyphCircle (1/2)`).
- `Pptc/Scratch/WarpTwo.lean`: two-`●` row. Proves `two_black_toSet`, `two_black_bbox`,
  `inkNormalize_two_formula`. Missing: normalized left disc = `glyphCircle a`, and the
  `restrict` separation at `x = w/2`.

## Follow-up (offsets, nonsquare, free handle)

- The free yellow handle is already `PConstructible` in `text`; keep the final theorem
  over P handles, not rational ones. It is one parameter (shape of the egg), not a second.
- Nonsquare boxes: no new algebraic modulus. Straight/polyline guides are affine or
  reparameterize the same universal egg family; curved guides are transcendental.
- Offsets: one extra P parameter, but degree/gonality grows. Calibration: parabola offset
  is a sextic exactly; ellipse 8 (N4's X-degree convention). **W4a:** the egg offset has
  geometric degree 16 (N4 convention; elimination polynomial total degree 28, Y-degree
  12), stable across four parameter choices (including the task's `d₀=1,d₁=2`) and
  irreducible over ℚ; the two-sided Groebner elimination factors as `(degree-4
  extraneous)² · (degree-28 elimination polynomial)`. Offset egg × general conic has F = 11
  but crossing degree at least 32 (a naive count on the total degree 28 gives 56) and
  cofactor at least 22 at n = 10, so the route is **closed** scoped to this construction.
  See `W4-offset.md`.

## Next

1. W4b: H3-protocol computation for egg × graph — degree and equations of the condition
   variety `χ_τ | N_m`; check whether its degree is < 9 (Lemma A over F).
2. W4c: test the totally real S₉ nonic `∏_{i=-4}^{4}(x-i)+1` against egg × sextic.
3. W4d: finish the two-disc bridge in a real file (`Pptc/Warp/Text.lean`), import it from
   `Pptc.lean`, and replace `TriangleCircleRule` by a theorem for the `●●` row.
