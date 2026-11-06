# PLAN-jacobi-X3: classical geometric mechanisms

Read `PLAN-jacobi-X0-overview.md` first. Log `HANDOFF-jacobi-X3.md`; deliverable
`NOTES-jacobi-X3.md`.

## The idea

Eighteenth- and nineteenth-century geometers found concrete ruler-and-conic mechanisms tied
to elliptic integrals. Several of them are exactly about "arc length minus a straight-line
length", the combination the string tool cannot handle on its own. Catalogue them, and test
whether any yields a construction with our moves.

## Mechanisms to study (for each: statement, source URL, numeric check, then the question)

1. **Graves–Chasles string theorem.** A closed string wrapped around an ellipse and pulled taut
   by a pencil traces a *confocal* ellipse. Equivalently, for `P` on the outer ellipse with
   tangent points `A, B` on the inner one, `|PA| + |PB| − arc(AB)` is constant. So the inner
   arc length equals tangent lengths minus a constant, where the tangent points are constructible
   from `P` by solving a quadratic. Does this let us *choose* an arc of prescribed "arc minus
   tangents" value by constructing a confocal ellipse from `u`? What function of the arc does
   that pin down: `E`, `F`, or a mix?
2. **MacCullagh's theorem** (the hyperbola version: the difference between a hyperbola arc and
   its asymptote tangent length), and **Landen's** theorem expressing hyperbola arcs through two
   ellipse arcs. The hyperbola's arc length contains `F` with a nonzero coefficient. Can a
   hyperbola (an affine image of `y = 1/x`, a drawable power law) plus ellipses be combined so the
   `E` parts cancel geometrically rather than by subtraction?
3. **Fagnano's theorem.** On an ellipse there are pairs of arcs whose difference is a straight
   length computable from the endpoints. This is the addition theorem for `E` in geometric
   form. Is there a first-kind analogue with a geometric realisation?
4. **Poncelet's porism via Jacobi.** For two circles (one inside the other), repeatedly drawing
   tangents to the inner circle from points on the outer one advances the angle `φ` so that
   `F(φ)` increases by a fixed step depending on the radii and the offset between centres. Each
   step is a constructible operation (tangent from a point to a circle). Given `u`, can we choose
   circles, all constructible from `u`, so that the step equals `u` (or `u/N`)? Then the next
   tangent point would be `am(u + F(φ₀))`. Work out the step formula (Jacobi 1828) and check
   whether choosing radii for a given step needs `am` itself. The expectation is that it does,
   but find out how.
5. **Lemniscate division (Gauss/Abel)** and the **pendulum/elastica**: any geometric
   construction in the literature producing `sl(u)` or the pendulum angle at a *general* time
   from finitely many conic or trigonometric operations.
6. Anything else you find in Chasles, Serret, Salmon ("Higher Plane Curves"), Greenhill
   ("Applications of Elliptic Functions", 1892, freely available), or modern sources on
   "geometric construction elliptic functions".

## Deliverable

Notes with the plain summary, and a table: mechanism, what it computes, whether it inverts
anything, verdict, and a numeric check reference. Write out any promising mechanism as an explicit
construction tree.
