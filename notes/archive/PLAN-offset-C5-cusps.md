# PLAN-offset-C5: what cusp extraction yields

Read `PLAN-offset-00-overview.md`, `NOTES-offset-A1.md` (cusp rows + "Singularities and cusps"),
`NOTES-offset-A3.md` §5 (the cusp/evolute verdict), `NOTES-offset-B3.md` §"Cusps", and
`NOTES-offset-Z.md` §5 (cusps/evolute). Log: `HANDOFF-offset-C5.md`; deliverable:
`NOTES-offset-C5.md`. Scripts: prefix `C5-`.

## Premise

**Cusp extraction is to be added to `Defs.lean`; that decision is the user's and is not part of this
task.** Assume the capability and map exactly **what it yields**: the new number families and their
degrees, the effective dimension / engine status of each, whether any of them covers a whole degree,
and the downstream consequences (notably the evolute as a rational curve and a possible route to the
totally real septic). Do not assess admissibility, legality, or whether `Defs.lean` should carry it —
those are settled elsewhere. `Defs.lean` and every other library file stay read-only; the
`defs-guard` plugin blocks tool-level edits to `Defs.lean`, so any change to it is the user's, made by
hand outside the task.

## Seed evidence (already computed; extend it, do not redo it)

The cusp parameter solves the curvature/evolute equation. For a cubic pair `γ=(x,y)`,

    (x'y'' − y'x'')² d² = (x'² + y'²)³,     degree 12 in t,

and for a graph `y=p(x)`, `(1+p'²)³ − d² p''²`, degree `6(n−1)` (12, 18, 24, 30, 36 for `n=3..7`).

`archived files/offset-scripts/C5-00-seed-cusp-dim.py` computes the effective dimension of the
cubic-pair cusp family at a random rational point: coefficient Jacobian rank **6** (of 9 parameters),
monic rank **5**, and **7** after `sl2` (`PGL₂`) saturation — versus **9** moduli for a full degree-12
binary form. So the family is **codimension ≥ 2**, not dominant: cusp extraction alone cannot cover
degree 12. A graph has only `n+2` parameters against `6n−9` moduli, so it is far worse. Re-run and
extend this before drawing conclusions.

## Strength of the primitive (affects the yield; the choice is the user's)

The yield depends on what the primitive returns, so report it under each strength and say plainly
which results need which:
* **(V-pt)** the cusp **point** / its coordinate(s);
* **(V-param)** the cusp **parameter** `t₀` as a constructible number;
* **(V-evolute)** the whole **evolute** as a constructible curve (i.e. a variable-distance offset).
This is a yield distinction, not a legality question: `V-evolute` subsumes the other two for
reachability but changes what curves exist to cross.

## Questions

1. **Yield: the number families.** For each strength, list the families produced and their degrees,
   and compute the **effective dimension modulo `PGL₂`** of the resulting polynomial family — both for
   the **parameter** `t₀` and for the **coordinate** `(X,Y)` on the evolute. A family of dimension
   `N−3` in degree `N` is dimensionally dominant; anything less is a proper subvariety. **Does any
   cusp family cover a whole degree `n ≥ 7`?** Extend `C5-00` to graphs and to the coordinate family.
2. **Coordinate vs parameter.** Report both the curvature degree and the minimal-polynomial degree of
   the cusp coordinate. If the coordinate is reachable directly (as `crossing_Pconstructible` returns
   coordinates), the coordinate degree is the relevant one; compute it for the cubic pair and the
   small graphs.
3. **Multiple cusps and selection.** The curvature equation can have several real roots. Determine how
   many real cusps a typical offset has and how the yield changes if the primitive returns *all* of
   them versus a selected one (smallest parameter, the one in a `restrict` window, the first as `d`
   grows past the minimum radius of curvature). Does returning all cusps amount to an engine?
4. **The evolute as a rational curve (`V-evolute`).** The evolute of a cubic pair is **rational**
   (A3 §5). Compute its degree, its crossing degrees with lines / conics / cubic Béziers / other
   rational curves from A4's family `R`, and its recovery cost (`gcd`/linear algebra over `K(X,Y)`,
   expected degree 1). Does the rational evolute give a new **exact** engine, comparable to the PH
   curves of `PLAN-offset-C4`?
5. **Leverage from a cusp point once it is in `K`.** With the cusp coordinates known, what curves and
   numbers follow? At minimum: the tangent and normal there, the osculating circle, circles tangent to
   the curve at the cusp, and any curve through the cusp that can then be crossed with others. Chase
   the best chain and give its degrees and dimension.
6. **Septic bootstrap (high-value).** The totally real septic is blocked by Hermite positivity, which
   fails for an auxiliary polynomial with a **non-real** root. Curvature/cusp equations are generically
   not totally real. Test whether a cusp-derived auxiliary over `K` can have a non-real root whose real
   root determines a real root of a prescribed totally real septic (B1 Q4). This is the one route by
   which cusps could touch the frontier.
7. **Consistency check.** With the primitive assumed, does the largest fully covered degree change?
   Does any previously unreachable number (e.g. a generic degree-12 number) become reachable? Do the
   non-generic coincidences A3 noted (a cusp already lying on a `K`-placed curve) add anything?

## Methods (bounded)

* Start from `C5-00-seed-cusp-dim.py`; extend to graphs and to the coordinate family. Report exact or
  mod-a-large-prime ranks, as in A2 (`[Jacobian rank at k random rational points]`).
* sympy `resultant`/`groebner` for the evolute and crossing degrees (keep each job bounded); Wolfram
  `Resultant`/`Factor`/`GroebnerBasis` cross-checks; mpmath to ≥ 30 digits for real cusp roots and
  the coordinate minimal polynomial (`mpmath.identify`/PSLQ).
* Draft the yield theorems ("assuming cusp extraction, number `X` is `PConstructible`") in **your
  own** private `pptc/Pptc/Scratch/OffsetC5.lean` only; do not edit the library.

## Deliverable

`NOTES-offset-C5.md` containing:

1. the primitive strengths considered and which results depend on which;
2. the yield table: strength × {degree, parameter-family dim/codim, coordinate-family dim/codim,
   covers degree `n`?, new numbers};
3. the multiple-cusp / selection analysis;
4. the evolute-rational-curve analysis (degree, `R`-crossings, recovery);
5. the septic-bootstrap verdict (with a concrete test, positive or negative);
6. construction trees for the best new numbers, clearly labelled as contingent on the primitive, held
   to the §5 evidence standard (≥ 30-digit check, side conditions, "genuinely new" checklist) as far
   as it can be met;
7. a closing statement of **exactly what cusp extraction buys and what stays out of reach** (e.g.
   degree-12 numbers but not degree-12 coverage), with the next best use of the primitive.

Tag every claim `[Lean]`/`[symbolic]`/`[numeric, N digits]`. End with the mandatory
**Side discoveries** and **Leads for other tasks** sections.
