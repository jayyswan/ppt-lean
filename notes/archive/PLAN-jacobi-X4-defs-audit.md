# PLAN-jacobi-X4: audit of the formal constructors

Read `PLAN-jacobi-X0-overview.md` first. Log `HANDOFF-jacobi-X4.md`; deliverable
`NOTES-jacobi-X4.md`. Research only; **do not edit `Defs.lean` or any `.lean` file.**

## The idea

Everything proved is about the formal definitions in `pptc/Pptc/Defs.lean`, not the drawing
program. If a constructor is formally more permissive than the geometry it models, there may be
a formal route to `am` that no real drawing could carry out. The user must hear about that kind
of mismatch, as a modelling bug, **not** have it used silently. Mismatches in the other
direction, where a constructor is weaker than intended, matter too.

## What to check (read `Defs.lean` in full first; it is ~25 KB)

1. `arc_of_length` and `arc_length`: what exactly is required of `γ`? Differentiable where:
   everywhere, or only on the interval? "Integrable" in which sense? `speed` uses `deriv`, which
   is `0` at non-differentiable points. Can a tracing that is not the geometric arc (a
   reparametrisation with jumps, or a tracing of a piece that is not an interval of the curve)
   give an `arcLengthOf` that differs from the true length, or a far endpoint that is not where
   the string ends?
2. `inter_x` / `inter_y`: `S ∩ T = {(x, y)}`. Are there degenerate sets that are
   `PConstructibleCurve`s but not curves, such as single points, empty sets or full lines,
   that make this a stronger operation than "read a crossing"? For example, can a restriction to
   a zero-width window, or an arc of length `0`, produce a single point `{p}` for a
   non-constructible `p`? Intersecting `{p}` with a line would then read off `p`.
3. `restrict`, `offset` (cusps, `d` beyond the radius of curvature), `rotate`, `scale` by `0`
   or negative factors, `power_law` at exponent `0`, `cubic_bezier` degenerate cases, and
   `div` by zero: any degenerate case that creates sets or numbers the geometry would not.
4. For each potential mismatch, give: the exact constructor and hypothesis; a concrete degenerate
   example; whether it yields new numbers (and which, e.g. could it make every real number
   P-constructible?); and a suggested tightening of the hypothesis.
5. Separately, list any place where the formal model is **weaker** than the drawing program in a
   way relevant to `am`. For example: can the program lay a string along a *closed* curve past
   its starting point, or along a union of curves, and do the constructors allow that?

## Deliverable

Notes with the plain summary, then a table of findings with severity: harmless / changes what is
constructible / makes everything constructible. Do not attempt a Lean proof of any exploit;
describe it precisely enough that the user can decide.
