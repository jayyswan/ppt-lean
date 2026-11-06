# PLAN-offset-A4: chains of offsets and affine maps; rational offsets as new curves

Read `PLAN-offset-00-overview.md` (O3, O6), `pptc/Pptc/Offset.lean`, and the offset-chain
material in `NOTES-jacobi-R1a.md` and `NOTES-jacobi-R1c.md`. Those are about arc length, so
reuse their speed formulas and not their conclusions.
Log: `HANDOFF-offset-A4.md`. Deliverable: `NOTES-offset-A4.md`. Scripts: prefix `A4-`.

## Why

The drawable curves with `K` parameters are few: conics and cubic Béziers, implicit degree ≤ 3.
That is the root of every Bézout ceiling so far (9 for two Béziers). Offsets break it, and there
are two ways they could give **unboundedly rich** curve families:

1. **Chains.** `offset → scale_x (or any non-similar linear map) → offset → …`. By O3 the maps in
   between are what make each new offset non-trivial. Each step adds parameters (`d`, and the
   matrix entries) and raises the implicit degree.
2. **Rational offsets.** Parabola and PH-cubic offsets are rational curves with `K` coefficients,
   with no square root left. Once they are rational, their affine images are **new rational
   curves of higher degree**, drawable with `K` parameters. Crossings between them are exact
   polynomial problems, so there is no norm doubling. Offsetting such a curve again brings the
   square root back, unless the curve happens to be PH again.

## Questions

1. **Rational offsets, precisely.**
   * Parametrize the offset of the parabola `y = x²` by `d` rationally (reparametrization
     `t = (s² − 1)/(4s)` or similar). Give its degree as a rational curve, its implicit degree
     (6), and the square roots of `K` elements the parametrization needs after an affine map.
   * The same for the Tschirnhausen / PH cubic and its similar images.
   * **Which other drawable curves have rational offsets**, possibly after a special choice of
     `K` parameters? Examples: cubic Béziers satisfying the PH condition, and conics. Use
     Pottmann's characterization (rational support function) and Farouki's PH theory. List
     them with their parameter counts.
2. **The curve family `R`** of rational curves reachable as affine images of rational offsets, and
   of curves reachable by iterating "rational offset" whenever PH-ness is preserved. Give degrees
   and parameter counts. Is `R` closed under anything useful? For example, is an affine image of
   an offset PH cubic ever PH again, making a second rational offset possible?
3. **Crossings inside `R`.** Take rational curve × implicit equation of another member, and
   rational curve × cubic Bézier. Compute the crossing degree and the effective dimension modulo
   Möbius, and the **cofactor coverage of degrees 7–12**, as in A2 question 3. **Recovery** of
   the rational parameter: from `(X, Y)`, the parameter of a rational curve is recovered by a
   gcd / linear algebra over `K(X, Y)`, usually of degree 1 when the parametrization is proper.
   Check this; it could be much cheaper than the quintic.
4. **Chains with square roots.** Take `off_{d₂} ∘ L ∘ off_{d₁}` applied to a cubic pair, with
   `L` a linear map. Compute:
   * the implicit degree of the chain curve, its genus, and the tower of square roots involved
     (`w₁`, then `w₂`, which depends on `w₁`);
   * the crossing polynomial with a line, after taking norms down the whole tower: its degree
     and effective dimension;
   * **recovery** through the chain. The last step gives the point on `L(off_{d₁}(γ))` through a
     normal equation of the chain curve. Is that equation still of low degree, and what does
     undoing `off_{d₁}` then cost?
5. **Growth.** Tabulate for chains of length 1, 2 and 3 (numerically, if the symbolic work
   explodes): degree, number of parameters, and effective dimension of the "chain × line"
   family. **Does dimension minus degree stay bounded, or does dimension keep pace?** A family
   whose effective dimension modulo Möbius equals `N − 3` in degree `N` is dimensionally
   dominant. Report the first chain length where that happens, if any.
6. **Legality.** `offset` needs its input arc to be injective, regular and C¹. An offset curve is
   regular except at cusps (`1 − dκ = 0`) and C¹ where the base curve is `C²`. Check that the
   second offset in a chain can always be applied on a sub-arc, and note what that costs.
7. **New numbers.** Give the best rational instance from each of (a) a crossing inside `R` and
   (b) a length-2 chain, with the §4 checklist of the overview.

## Deliverable

1. The summary.
2. A list of the rational-offset curves in the drawable world (with parameter counts).
3. Tables for `R`-crossings and for chains.
4. A verdict on growth: does iterating offsets plausibly reach dimensionally dominant families in
   every degree? That is the key input to B2's theory.
5. Explicit new numbers.
6. The Side discoveries and Leads sections.
