# PLAN-offset-A2: one-offset crossing families and what degrees they cover

Read `PLAN-offset-00-overview.md` (especially §4) and `pptc/Pptc/Offset.lean`, in particular the
closing section on codimension 3. Also read `archived files/NONIC-notes.md`, which carries out
the same style of analysis for two Béziers.
Log: `HANDOFF-offset-A2.md`. Deliverable: `NOTES-offset-A2.md`. Scripts: prefix `A2-`.

## Why

The line is the weakest second curve. `offsetCubicPair_cross_root_Pconstructible` already accepts
**any** constructible second curve `T` with an implicit equation `F`. For the cubic pair the
recovery stays a quintic whatever `T` is. A richer `T` raises the degree of the equation that is
solved and adds parameters, and may break the degeneracy that left the line family at
codimension 3. This task maps those families and decides which of them cover whole degrees.

## Families to analyse

The first curve is the offset of arc `γ` by `d`; the second curve `T` is given implicitly.
Rationalize with the norm (O4).

| # | offset of | crossed with `T` |
|---|---|---|
| F1 | cubic pair | line (known: degree 10, codim 3; reproduce as calibration) |
| F2 | cubic pair | general conic (5 coefficients; the rationalized degree should be 20, confirm) |
| F3 | cubic pair | implicit cubic Bézier (`F` with cube leading form; ~30, confirm) |
| F4 | cubic pair | degree-≤6 polynomial graph (rational coefficients, then affine maps with `K` parameters) |
| F5 | cubic pair | `y = x^n` for `n = 7, 8, 9` (power law, only `x > 0`) |
| F6 | parabola (rational offset, O6) | line, conic, cubic Bézier, power law: **exact polynomial equations without squaring** |
| F7 | PH cubic (rational offset) | the same list |
| F8 | ellipse / hyperbola arc | line, conic, cubic Bézier |
| F9 | conic | cubic pair (the reverse roles of F2: the Bézier is now the parametrized curve) |

Also consider **reversing roles** so that the offset is the implicit curve and the other curve is
parametrized (e.g. a Bézier `(x(s), y(s))` substituted into the implicit equation of an offset
parabola, which has degree 6: degree 18 in `s`). This changes which parameter comes out and what
recovery costs.

## Questions, for each family

1. **Normal form.** Find the analogue of `offsetCrossPoly_normalForm`: the minimal set of
   parameter combinations the crossing polynomial depends on. Prove it [symbolic].
2. **Effective dimension.** Compute the rank of the Jacobian of the map from parameters to the
   coefficient vector, at several random rational points, exactly or mod a large prime. Report:
   the dimension in the space of degree-`N` polynomials up to scale; the dimension modulo
   `PGL₂` acting on the root variable; and the codimension of each.
3. **Cofactor coverage of low degrees.** For each target degree `n ∈ {7, 8, 9, 10, 11, 12}` and
   each family of degree `N ≥ n`, compute the dimension of
   `{P monic of degree n : P·g ∈ family for some g of degree N − n}`, using Jacobian rank on the
   incidence variety. **Is it all of degree `n`?** Do the same modulo Möbius, and then also
   modulo Tschirnhaus with **real** `φ` (count first; §4 of the overview warns about reality).
4. **For every family that covers some degree `n ≥ 7` dimensionally**, go further:
   * **Real feasibility.** For random *totally real* targets `P`, and for targets with 1 and 2
     conjugate pairs, does the covering system have a real solution? Use numeric homotopy
     (`NSolve`), or Wolfram `FindInstance` / `Reduce` over the reals. Keep separate counts by
     real-root pattern: this is where the Hermite obstruction bit before.
   * **Degree of the covering system.** Count its solutions over ℂ (the elimination or Bézout
     degree) and compute the Galois/monodromy group of the auxiliary unknowns, by cycle types
     mod primes for a rational target. If some ordering of the unknowns makes every step
     degree ≤ 6 (triangular), or uses free rational choices, **write it down**. That would be a
     theorem.
   * If the naive system is too hard, look for special sub-families (a cusp in the Bézier, a
     vertex of the conic, `d` tied to the curvature, symmetric configurations) that trade
     generality for a triangular solve while keeping coverage.
5. **Sign and branch conditions.** Use (O4) to state exactly which real roots of the rationalized
   polynomial are genuine crossings. Say what the regularity (`w ≠ 0`) and injectivity
   requirements cost, and what the `x > 0` limit of the power law costs.
6. **New numbers.** For the best two or three families, give a rational instance with a new
   high-degree number and run the §4 checklist of the overview.

## Deliverable

1. The summary.
2. A table of families × {degree, normal form, dimension, codimension (plain / mod Möbius),
   degrees `n` covered by cofactor, real feasibility by root pattern, covering-system degree}.
3. Derivations and scripts.
4. **An explicit statement of the strongest covering result obtained**, e.g. "every monic octic
   over `K` with at least one real root is covered by F3 via cofactor + Möbius, with the covering
   system solvable in `K` by the following steps …", or the precise reason each family falls
   short.
5. The Side discoveries and Leads sections.
