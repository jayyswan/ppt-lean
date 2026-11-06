# PLAN-jacobi-R1b: arc lengths of polynomial / Bézier / power-law chains

Read `PLAN-jacobi-00-overview.md` first. Research task: **no `.lean` edits**.
Log: `HANDOFF-jacobi-R1b.md`. Deliverable: `NOTES-jacobi-R1b.md` (repo root).

## Question

Bases: `poly_graph` (rational coefficients, degree ≤ 6), `cubic_bezier` (any constructible
control points), `power_law` `y = a x^b` (rational `a, b`). Closure: any constructible linear
map and translation, and `offset` (formula F3 in the overview). Is there a curve in this class
whose arc length is **exactly** `α·F(φ(T), c) + β`, with no boundary term, for some `c ≠ 0`?

Fact F2 shows how close a single cubic graph gets: first kind plus the boundary term
`(1/3)x√(1+9x⁴)`. The task is to find out whether offsets, linear maps or other bases can remove
that boundary term, or to explain why they cannot.

## Steps

1. Power laws: speed `√(1 + a²b² x^{2b−2})` is a binomial differential. Use Chebyshev's
   theorem to list every rational `b` (small numerators and denominators, say |num|, den ≤ 12)
   for which the arc length is elliptic. For each, give the reduction to Legendre form: which
   modulus, which boundary term. Verify numerically.
2. Pythagorean-hodograph cubic Béziers: their offsets are rational. Linear images of those
   offsets are rational curves with `ds = √P(t)·R(t) dt`, `P` quartic. Check the overview's
   degree-count argument that `P·R` can never be constant, or find the flaw. Extend to depth-2
   chains (offset, map, offset, map).
3. General cubic Bézier plus one offset plus one linear map, using (F3): decompose `ds` on the
   elliptic and hyperelliptic curves involved. Is there a parameter choice with no exact part
   and no second-kind part? Use a numerical test: compute `s(T)` and test whether
   `ds/dT · √(quartic)` is constant for a guessed quartic, or better, test for poles of `ds` at
   the points at infinity and at branch points symbolically.
4. Pole-at-infinity argument: state carefully why an unbounded algebraic curve's arc length
   has a pole at infinity, and hence cannot be a pure first-kind integral **as an abelian
   integral on that curve**. Then check whether the argument survives for arcs of the curve
   that stay bounded, and for reparametrisations `φ(T)` that are not algebraic. The argument
   is about differentials, so it should survive, but say so explicitly.
5. Write the notes with a verdict and its assumptions.

## Stop

Stop at a verified breakthrough, or when steps 1–5 are written. Ellipse bases belong to R1a, and
sine and `2^x` bases to R1c.
