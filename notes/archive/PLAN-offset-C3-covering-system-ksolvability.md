# PLAN-offset-C3: solving a covering system in `K` (B2's sufficiency lemma applied)

Read `PLAN-offset-00-overview.md` §4, `NOTES-offset-A2.md` §3, `NOTES-offset-B2.md` §3.4 and §5.3.
Log: `HANDOFF-offset-C3.md`; deliverable: `NOTES-offset-C3.md`.

## The question

A2 showed every offset×second-curve family is a proper subvariety (the line is `D=7`, conic `D=10`,
cubic Bézier `D=11`, degree-6 graph `D=13`), and B2 proved a **sufficiency lemma** (Lemma 13):
if the covering system `Q = P·g` can be solved in `K` — with a defect function `Ψ` that changes
sign along a rational segment and has degree ≤6 — then the target `P` is covered. B2 also proved
the decic family's `PGL₂`-saturation is codimension 1 (Z-confirmed, `Z-06`), so the line family
cannot cover general degree 10. The strongest remaining candidate is **F4, the degree-6 polynomial
graph** (`D=13`, fibre dim `D−n` for `n=7…13`).

## Questions

1. **Set up `Q = P·g` for F4 for a prescribed totally real septic `P`.** Unknowns: the cubic-pair
   base (8), `d` (1), the degree-6 graph `h` (7) = 16, plus the cofactor `g` (deg `N−n`); the
   condition is `Q ≡ 0 mod (P·g)`. Confirm the fibre has the predicted positive dimension.
2. **Find the free rational choices.** Fix all but a few unknowns rationally and reduce the system
   to a univariate `Ψ` of degree ≤6. Verify `Ψ` changes sign on a rational segment (IVT), so its
   root is in `K` by `root_Pconstructible_le_six_coeffs`.
3. **Real feasibility by root pattern.** For each root pattern (number of real roots) of a septic,
   does the fibre meet the real locus? Use Wolfram `CylindricalDecomposition`/`Reduce` on the
   reduced system.
4. **Obstruction check.** Every proposed `Ψ` must avoid relying on killing ≥2 power sums by a real
   Tschirnhaus map (B2 Lemma 12). Confirm the construction is a cofactor/IVT one, not a Tschirnhaus
   reduction.

## Methods

* sympy for the symbolic setup and the dimension count; Wolfram for `Reduce`/`CylindricalDecomposition`
  real feasibility; mpmath for numerical sign-change certification at 50 digits.
* If F4 fails, fall back to the offset×conic family (A2 F2, `D=10`), which B1 §2 records as having
  genuine slack.

## Deliverable

`NOTES-offset-C3.md`: either an explicit `K`-solvable covering system that covers a degree ≥7
(with the construction tree and a ≥30-digit check), or a documented reason why the reduced systems
have a degree->6 obstruction. Tag every claim. **A count that closes is not a proof.**
