# PLAN-jacobi-X2: the amplitude as a crossing

Read `PLAN-jacobi-X0-overview.md` first. Log `HANDOFF-jacobi-X2.md`; deliverable
`NOTES-jacobi-X2.md`.

## The idea

Crossings solve equations. For example, the line `y = x − M` crossing the curve
`y = e sin x` solves Kepler's equation `x − e sin x = M`, whose solution is not an elementary
function of `M`. So crossings of the sine curve with other curves already give some
non-elementary inverse functions for free. Could a crossing of curves built from `u`, perhaps
with arcs from earlier string-layings or other transcendental constructed curves, land exactly on
`am(u)`, `sn(u)` or `(sn u, cn u)`?

## Questions

1. **What equations can crossings solve?** Describe, as precisely as you can, the class of
   equations `G(x, y) = 0, H(x, y) = 0` whose solutions are crossing coordinates, when the curves
   come from the base curves by affine maps and offsets with parameters depending on `u`.
   (Offsets introduce `1/√(x′² + y′²)`; sine and `2^x` introduce exponentials and trig.)
2. **Pfaffian angle (important, and hopeful).** `sn, cn, dn` form a *Pfaffian chain*:
   `sn′ = cn·dn`, `cn′ = −sn·dn`, `dn′ = −c·sn·cn`, polynomial in the chain. So do `sin`, `cos`
   and `exp`. Khovanskii's theory of fewnomials treats such functions uniformly. So "Pfaffian vs.
   not" does **not** separate `am` from what crossings produce. Look for a construction that
   realises a Pfaffian chain geometrically. Is there a known curve-intersection or mechanism
   whose solution traces a solution of an autonomous polynomial ODE system? The pendulum
   (`θ″ = −k sin θ`, solved by `am`) is the physical example: its phase portrait
   `θ′² = 2k(cos θ − cos θ₀)` is a **drawable-looking curve** in the `(θ, θ′)` plane, a
   transformed cosine graph. Work out whether time along that portrait can be read geometrically
   with the available moves.
3. **Kepler-like reformulations.** Find the most "elementary-looking" equation that has
   `am(u)` or `sn(u)` as a solution. Possibilities include a Fourier/nome expansion truncated to
   an exact identity at special `u`, and equations relating `am(u)` at several points via the
   addition theorem, `am(2u)` in terms of `am(u)`, where a crossing picks a fixed point. Check
   whether any closes up into a single finite equation built only from allowed pieces.
4. **Self-referential crossings.** The curve `arc_of_length` produces has a
   non-constructible endpoint that depends on `L`. Crossing *such arcs*, possibly offset or
   rescaled by amounts computed from `u`, gives numbers depending on inverse arc lengths at
   several lengths simultaneously. Explore whether two or three such arcs on different curves
   can be arranged to meet at a point whose position encodes `am(u)`. Model the constraint system
   and count unknowns vs equations; a count showing zero-dimensional solution sets with the right
   solution is worth reporting, then test numerically.

## Deliverable

Notes with the plain summary, a description of the equation class crossings solve, the
pendulum/Pfaffian analysis, and any candidate constructions with their numerical checks, or
a clear account of why each idea closes off.
