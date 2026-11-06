# PLAN-offset-A3: offset against offset, self-crossings, cusps

Read `PLAN-offset-00-overview.md` and `pptc/Pptc/Offset.lean`.
Log: `HANDOFF-offset-A3.md`. Deliverable: `NOTES-offset-A3.md`. Scripts: prefix `A3-`.

## Why

A2 crosses one offset with an ordinary curve. Here **both** curves carry square roots, which
gives genuinely new extraction mechanisms with a clear geometric meaning:

* **Offset × offset.** The offset of `γ₁` by `d₁` meets the offset of `γ₂` by `d₂` at a point at
  distance `|d₁|` from `γ₁` and `|d₂|` from `γ₂`, measured along normals: the centre of a circle
  of radius `d₁` tangent to `γ₁` and (with `d₂ = d₁`) to `γ₂`. This is the Apollonius problem for
  curves, and it is a two-parameter polynomial system in `(t₁, t₂)` whose resultant can have
  large degree, with many parameters (8 + 8 + 2 for two cubic pairs).
* **Self-crossings of one offset** (the swallowtail). Offsets of two disjoint parameter windows
  of the *same* arc are separate constructible curves, so their crossing is an `inter_x` input.
  It is the centre of a circle of radius `|d|` that touches `γ` twice, a bitangent circle.
* **Cusps.** Where `d = 1/κ(t)` the offset has a cusp lying on the evolute. For a cubic pair,
  `(x′y″ − y′x″)² d² = (x′² + y′²)³` has degree 12 in `t`. **Can a cusp be extracted?** `inter`
  needs a unique crossing, and a cusp point is not a crossing of two curves unless something
  passes through it.

## Questions

1. **Offset × offset, two cubic pairs.** Write the system `γ₁(t₁) + d₁N₁(t₁) = γ₂(t₂) + d₂N₂(t₂)`.
   Rationalize both square roots (norms over both extensions, keeping both sign choices), then
   eliminate `t₂`.
   * The degree in `t₁` of the resultant. Does it factor for structural reasons (sign-branch
     factors, spurious components at `w = 0`)? Do it in Wolfram, and confirm the final degree
     numerically by counting complex solutions with `NSolve` at random rational parameters.
   * The effective dimension of the family of resultant polynomials (Jacobian rank, modulo
     Möbius).
   * **Recovery.** Both `t₁` and `t₂` come out through their normal equations (quintics), since
     the crossing point `(X, Y)` is in `K`. State it carefully.
   * Cofactor coverage of degrees 7–12 (as in A2, question 3). **Real feasibility** for totally
     real targets.
   * Special cases worth separate rows: `γ₂` a line (then the offset of a line is a line: this is
     A2's F1 with `C` shifted, a sanity check); `γ₂` a circle (a circle of radius `r + d₂`);
     `γ₂` a parabola (rational offset); `γ₁ = γ₂` on different windows (the self-crossing).
2. **Self-crossings.** For one cubic pair and `d`: the pairs `(t, s)` with equal offset points.
   The polynomial after removing the diagonal `t = s`: its degree, its dimension, and what it
   buys. Handle the isolation hypothesis explicitly: the two windows must be chosen with
   rational endpoints so that the two offset arcs meet exactly once. Is that always possible
   near a transverse self-crossing?
3. **Cusps and evolutes.** Decide whether a cusp point can be extracted with the moves. Candidates:
   * A line through the cusp needs a cusp coordinate that is already known. Can a *second*
     constructible curve be arranged to pass through the cusp automatically? For instance, the
     offset curves for `d` and `d′` have cusps on the same evolute, but at different points.
   * `inter` accepts a tangential unique crossing. Is there a configuration where the unique
     crossing of two constructible curves is *forced* to be the cusp or the evolute point?
   * The evolute as a **limit** is not a move. Say so if nothing works, and explain why. The
     answer decides whether the degree-12 curvature equation is usable.
4. **Other metric problems** reachable with two offsets and a crossing:
   * points equidistant from two curves (a "medial axis" point with a given distance);
   * circles of given radius tangent to a curve and a line;
   * circles of given radius through a point and tangent to a curve (the offset crossed with a
     circle centred at the point).

   For each one give the polynomial family and its dimension, and note any that reduce to a
   triangular solve.
5. **Parameter growth.** With `k` offset curves and pairwise crossings used as data for later
   curves, does the effective dimension of reachable univariate families grow without bound as
   `k` grows (while the degree grows too)? Even a heuristic answer is useful: the programme's
   hope for all degrees rests on it.
6. **New numbers.** Give rational instances with the §4 checklist of the overview. Aim for the
   first **degree ≥ 20 number with a full-symmetric Galois group** from an offset×offset
   crossing, with the whole construction tree and side conditions.

## Deliverable

1. The summary.
2. A table of mechanisms × {legal extraction? (yes / no / conditional), degree, dimension,
   coverage, real feasibility}.
3. The cusp verdict with its reasoning.
4. Derivations, scripts, and explicit new numbers.
5. The Side discoveries and Leads sections.
