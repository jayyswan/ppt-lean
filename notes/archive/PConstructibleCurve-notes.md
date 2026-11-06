# Representing `PConstructibleCurve`

Notes on extending `pptc/Pptc/Basic.lean`'s `PConstructible : ℝ → Prop` (closed under `+ - * /` from `1`) to cover constructible curves — ellipses, polynomials with rational coefficients up to degree 7, and curves of the form `a * x^b` with `a, b` rational.

## Represent curves as loci, not functions

Ellipses aren't graphs of `ℝ → ℝ`, so `PConstructibleCurve : Set (ℝ × ℝ) → Prop` (implicit point-sets) is the right carrier, not something like `PConstructibleCurve : (ℝ → ℝ) → Prop`.

This also lets an ellipse be stated as its polynomial relation

```
((x - h) / a)^2 + ((y - k) / b)^2 = 1
```

with no need to touch trig — important since `PConstructible` has no `sin`/`cos`/`sqrt` closure yet, and implicit conics don't require one.

## Recommendation

An inductive `Prop` mirroring `PConstructible`'s style — one base constructor per curve family, with all numeric parameters required to be `PConstructible` (so the two types compose), plus a small set of closure constructors for how curves combine geometrically:

- **`ellipse`** — center/axes are `PConstructible`, locus is the standard conic equation
- **`poly_graph`** — a `Polynomial ℝ` of `natDegree ≤ 7` with every coefficient `PConstructible`, locus `{(x,y) | y = p.eval x}`
- **`power_law`** — `a b : ℚ`, locus `{(x,y) | 0 < x ∧ y = a * x^(b:ℝ)}`
- closure ops as needed: `union`, `image` under a `PConstructible`-affine map (translate/scale/rotate), maybe `restrict` for arcs

## Main tradeoff

Versus this per-family design, a single unified constructor over `MvPolynomial (Fin 2) ℝ` ("vanishing set of a bivariate polynomial with `PConstructible` coefficients, `totalDegree ≤ 7`") would fold `ellipse` and `poly_graph` into one case and is more mathematically elegant, but:

- it can't express `a * x^b` for non-integer rational `b` (not a polynomial), and
- it's heavier to compute with in proofs.

Per-family constructors also match how the JSON node model (`nodes.json` / `SCHEMA.md`) already separates curve-producing axioms (draw ellipse, etc.) as distinct primitives, so leaning toward per-family constructors.
