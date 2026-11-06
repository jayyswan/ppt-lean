# PLAN-offset-A1: an atlas of single offsets

Read `PLAN-offset-00-overview.md` first, and all of `pptc/Pptc/Offset.lean`.
Log: `HANDOFF-offset-A1.md`. Deliverable: `NOTES-offset-A1.md`. Scripts: prefix `A1-`.

## Why

Every later task needs the same basic facts about "the curve you get by offsetting X". The
programme has so far worked out one case (the cubic pair crossed with a line). This task builds
the reference table that the other tasks, and the synthesis, will cite.

## Base curves to cover

Allow every affine image with parameters in `K`. The offset commutes only with similarities, so
a non-circular ellipse, a sheared Bézier and so on are genuinely different inputs.

1. Line / segment (sanity check: the offset is a line).
2. Circle (sanity check: a concentric circle, or the centre when `d = ±r`).
3. General ellipse and hyperbola (affine images of the circle and of `xy = 1`; the hyperbola
   comes from `power_law 1 (-1)`).
4. Parabola (affine images of `y = x²`).
5. General cubic Bézier / cubic pair. Separate out the special subclasses:
   * Pythagorean-hodograph cubics (Tschirnhausen cubic and its similar images);
   * cuspidal cubics `(t², t³)` and their affine images;
   * nodal and acnodal cubics `(t² + λ, t³ + λt)`;
   * cubic graphs `y = cubic(x)`.
6. Polynomial graphs `y = p(x)` of degree 4, 5, 6 with rational coefficients, then affine maps.
7. Power laws `y = x^{p/q}` for small `p/q` (e.g. `3/2`, `−2`, `1/3`).
8. Brief notes only: `y = 2^x` and `y = sin x` (analytic, not algebraic; B3 covers them in depth).

## Questions, for each base curve

1. **Implicit equation of the offset.** Its degree, both for generic `d` and for special `d`.
   Irreducibility. Do the two sides `±d` form one irreducible curve (they usually do)? Derive
   it by elimination in Wolfram (`GroebnerBasis` with `EliminationOrder`, or `Resultant`), and
   compare with the degree formulas in the literature: Farouki–Neff 1990; San Segundo & Sendra,
   *Total degree formula for the generic offset to a parametric curve* (2012), and their other
   offset-degree papers.
2. **Genus of the offset curve** (for generic `d`), and whether it is rational. If it is
   rational, give an explicit rational parametrization with coefficients in `K`, and say which
   extra square roots it needs (e.g. `√(A²+B²)`).
3. **Singularities.** Cusps (on the evolute), self-crossings (the swallowtail), points at
   infinity and their multiplicities (compare the "one triple point at infinity" argument in
   `archived files/NONIC-notes.md`), and isolated real points (acnodes). For each kind of
   singularity, the degree of the polynomial whose roots are its parameters.
4. **Crossing degree with a line.** After rationalizing (O4), the degree in the base parameter of
   the crossing polynomial against a general line, and against the axes after the right affine
   normalisation. Give the normal form in the style of `offsetCrossPoly_normalForm`: which
   combinations of parameters actually enter.
5. **Recovery.** The degree of the normal equation for the base parameter. Is it ≤ 6? If not,
   which *coordinate* numbers (`X`, `Y`, or combinations of them) are still extracted, and what
   is their degree over `K` generically?
6. **Parameter count versus effective dimension** of the "offset × line" family: the Jacobian
   rank of (curve parameters, `d`, line) ↦ crossing polynomial, taken modulo `PGL₂` acting on
   the root variable wherever the parameter is itself a rational coordinate. Report
   `N − 3 − rank` (the codimension in moduli) and the codimension in monic degree-`N`
   polynomials.
7. **Numbers.** For each base curve, give one rational-parameter instance of "offset × line" that
   produces the highest-degree new number, and run the §4 checklist of the overview on it
   (degree, irreducible factorization, Chebotarev cycle types). A table row may say
   "nothing new" when that is the answer, e.g. when the circle and line give only degree 2.

## Deliverable

1. The summary at the top.
2. One master table: base curve × {implicit degree, genus, rational?, cusp polynomial degree,
   crossing degree with a line, recovery degree, effective dimension of the offset×line family,
   codimension}.
3. Per-curve sections with the derivations and scripts.
4. A ranked list of "most promising offset curves for high-degree engines". Prefer high crossing
   degree, low codimension, cheap recovery, and rational offsets.
5. The Side discoveries and Leads sections required by the overview.
