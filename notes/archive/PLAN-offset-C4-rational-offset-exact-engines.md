# PLAN-offset-C4: rational-offset curves as exact high-degree engines

Read `PLAN-offset-00-overview.md` (O5, O6, O7), `NOTES-offset-A4.md`, and `NOTES-offset-Z.md`
§3 (A4 rows). Log: `HANDOFF-offset-C4.md`; deliverable: `NOTES-offset-C4.md`.

## The question

A4 (Z-confirmed) classified the drawable rational-offset curves (line, circle, parabola, PH cubic)
and showed their offsets are again rational, so crossings are **exact polynomial systems** with
degree-1 parameter recovery. A4's length-2 chain already gives a degree-28 irreducible crossing
polynomial. The open question: how far can rational-offset curves be pushed as *exact* engines, and
do they combine with A2's cofactor analysis better than generic curves?

## Questions

1. **Exact crossing degrees.** Tabulate curves from `R` (affine images of rational offsets) crossed
   with lines, conics, cubic Béziers, and each other: exact degree, irreducibility, real-root
   counts, and genus. A4 gives a partial table; fill it and verify each entry in two systems.
2. **Degree-1 recovery as a degree engine.** Does the degree-1 (proper) recovery let a *chain* of
   rational-offset crossings be solved triangularly, giving a genuinely new all-degree mechanism?
   A4 warns chains are not dimensionally dominant; test whether the exactness changes that.
3. **Cofactor coverage.** Run A2's cofactor criterion on the rational-offset crossings: for a
   target degree `n`, is `Q = P·g` solvable in `K`? The degree is lower than the generic case, so
   the system is smaller — decide whether it is `K`-solvable where A2's was not.
4. **Combine with PH classification.** For a PH cubic, the offset is PH; identify the largest
   `(curve, crossing)` that keeps a **polynomial** (not just rational) parametrization, since that
   removes denominators entirely.

## Methods

* sympy resultants for exact degrees; Wolfram `Resultant`/`Factor` cross-checks; mpmath for real
  roots. Keep each resultant bounded (< deg 40) or split into stages.
* For coverage: set up `Q = P·g` symbolically for the smallest rational-offset family and attempt a
  triangular solve, as in PLAN-offset-C3.

## Deliverable

`NOTES-offset-C4.md`: the completed exact-degree table for `R`-crossings, a verdict on the
degree-1-recovery triangular mechanism, and the cofactor-coverage result. Tag evidence; state any
negative as the exact excluded class.
