# PLAN-offset-B3: what offsets give beyond algebraic numbers

Read `PLAN-offset-00-overview.md` and `PLAN-jacobi-X0-overview.md`. Skim `NOTES-jacobi-R1a.md`,
`NOTES-jacobi-R1c.md` and `NOTES-jacobi-X5.md` for the offset material already worked out, and
do **not** redo the Jacobi-amplitude analysis. Also skim `CLAUDE.md` for what is known.
Log: `HANDOFF-offset-B3.md`. Deliverable: `NOTES-offset-B3.md`. Scripts: prefix `B3-`.

## Why

The user wants to hear about any new constructible numbers or techniques. `offset` interacts with
the transcendental moves: `arc_length`, `arc_of_length`, `sine` and `exp_two`. This task inventories
what comes out, and separates genuinely new numbers from ones that were already reachable.

## Questions

1. **Lengths of offset arcs.** By (O2), `L_d = L − dΔθ`. Endpoints of an offset at a constructible
   parameter are constructible, since the normal only adds a square root. So check whether
   `arc_length` of an offset ever gives anything beyond `(old length) + d·(arctan-type angle)`.
   Consider cusped offsets, where the formula changes sign past a cusp: is `∫|1 − dκ||v|` then a
   new combination? Check curves whose own length was not reachable, e.g. arcs obtained through
   `arc_of_length`.
2. **`arc_of_length` along offsets.** Laying a string along an offset inverts `s(t) − dθ(t)`. List
   the new *inverse functions* this provides for each base curve: for the ellipse,
   `E(φ) − d·(angle)`; for the parabola, an elementary function; for the sine curve, the
   `√(1 + cos²)` integral minus `d·arctan(cos)`. Which named functions or constants become
   reachable? Can a clever choice of `d` and curve cancel a term that previously blocked an
   inversion? Relate this to the "`s − B` obstruction" in `PLAN-jacobi-00-overview.md` §1, in
   **one short paragraph**, and do not pursue the amplitude itself.
3. **Offsets of `y = sin x` and `y = 2^x`.** Crossings of these offsets with lines, conics and
   other offsets solve equations like `x − d cos x/√(1 + cos²x) = …`. Which classical equations
   are **newly** solvable, and which were already solvable by crossing the bare curves?
   Candidates to test: Kepler's equation, Lambert `W`, the Dottie number, `x = tan x` roots,
   Bessel-type zeros, the catenary parameter, the "goat grazing" angle, and roots of
   `a sin x + b cos x = cx`. Be strict about "already reachable": decide it from the existing
   moves, and cite a lemma or give a construction.
4. **Distances and normals.** Offsets turn "distance from a point to a curve equals `d`" into a
   crossing. What does that give?
   * The foot of the perpendicular (normal equation) for transcendental curves: from a
     constructible point to the sine curve, which solves `(X − x) + (Y − sin x)cos x = 0`.
   * Minimal distance between two curves.
   * Radius of curvature data.

   For each, decide whether it is new relative to what crossings of the bare curves already give.
5. **Envelopes, evolutes, involutes, and curves of constant width.** Can the involute of a circle,
   a cycloid or a trochoid be drawn with the moves? For example, `arc_of_length` on a circle
   together with tangent lines, or an offset of a known curve that coincides with one of them.
   If so, what numbers come from their crossings? Is the evolute or the involute of a Bézier
   reachable as an offset-related set?
6. **Special values.** Look for "nice" numbers that offsets make constructible. Examples: the
   minimal distance from a point to `y = x^7`, the radius of the largest circle inscribed under
   an arch of the sine curve, the perimeter of a parallel curve of an ellipse. Check each with
   `mpmath` to ≥ 30 digits, and identify it with `mpmath.identify`, PSLQ or Wolfram
   (`RootApproximant`, `FindIntegerNullVector`). Flag any that lead to a closed form involving
   known non-elementary constants.
7. **Techniques.** Record any new *technique*: a reusable lemma shape, a trick to make crossings
   unique, or a way to trade a transcendental inversion for an offset. A technique is worth more
   than a single number.

## Deliverable

1. The summary.
2. A table of candidate numbers and functions × {construction, new or already reachable (with
   the reason), numeric check}.
3. Short notes per question, with negative findings stated as precisely as positive ones.
4. The Side discoveries and Leads sections. This whole task is side discoveries, so use "Leads"
   to name the most promising follow-ups.
