# PLAN-jacobi-R2: curves whose arc length is a first-kind integral; minimal extensions

Read `PLAN-jacobi-00-overview.md` first. Research task: **no `.lean` edits**.
Log: `HANDOFF-jacobi-R2.md`. Deliverable: `NOTES-jacobi-R2.md` (repo root).

## Questions

A. **Classical catalogue.** Which algebraic curves have arc length equal to an elliptic integral
of the first kind? Known: the lemniscate of Bernoulli (F1 in the overview). Serret (1845) found
an infinite family of rational ("unicursal") curves with this property, and Liouville commented
on it. Find the explicit parametrisations and the moduli they realise. Is every `c ∈ (0,1)`
realised, or only a countable set? Include any other families you find, e.g. curves
`z = f(t)` with `|f′(t)|² = const/quartic(t)`.

B. **Drawability.** For each curve in the catalogue, is it (or an arc of it) in the drawable
class? An arc coincides with an arc of a drawable algebraic curve only if the whole irreducible
components coincide. So compare degree, genus and singularities against: conics, polynomial
graphs of degree ≤ 6, cubic Béziers (polynomial cubics), `y = a x^b`, linear images of those,
and offsets of linear images (these are generally not rational; offsets of Pythagorean-hodograph
cubics are rational of degree ≤ 5). Also try the transcendental constructors: could an offset
of some drawable curve coincide with a Serret curve?

C. **Minimal extension.** If nothing in the catalogue is drawable, what is the *smallest* new
constructor that makes the amplitude P-constructible for **every** P-constructible `c < 1`? For
example: a rational cubic Bézier (weighted control points); a lemniscate base curve (only one
modulus, so probably not enough alone; say why, or how scaling does or does not change the
modulus); a polar-curve constructor. For the best candidate, give the full construction sketch:
curve, parametrisation, arc length `= α F(φ) + β`, and how the abutting-arcs trick then
yields `am`.

## Steps

1. Literature search (web): "Serret curves arc length elliptic integral first kind",
   "courbes de Serret", Liouville, "curves whose arc length is an elliptic integral". Record
   the sources with URLs.
2. Rederive Serret's parametrisation yourself and verify numerically (mpmath) that
   `speed² · quartic = const` and that the arc length matches `mpmath.ellipf`.
3. Answer B for each curve, with reasons.
4. Answer C.

## Stop

Stop after writing A–C. Do not modify `Defs.lean`: changing the primitive set is the user's
decision.
