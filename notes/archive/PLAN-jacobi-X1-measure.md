# PLAN-jacobi-X1: the amplitude as a measured length

Read `PLAN-jacobi-X0-overview.md` first. Log `HANDOFF-jacobi-X1.md`; deliverable
`NOTES-jacobi-X1.md`.

## The idea

`am(u)` is itself an arc length: on the unit circle, the walk from `(0, 1)` to `(sn u, cn u)`
has length `am(u)`. It is also `∫₀ᵘ dn(t) dt`. The circle version is useless because measuring
needs the endpoint, which *is* the answer. The question is whether **some other curve**, whose
shape and endpoints are computed from `u` without knowing `am(u)`, has length exactly `am(u)`.
Or more modestly, a length from which `am(u)` follows by arithmetic, square roots, `arccos` and
the other known black boxes.

## Questions

1. **The linear-equation test (to verify or break).** Claim to check: if a curve's equation is
   polynomial (ellipse, Bézier, polynomial graph, rational power law, and their affine images)
   and its shape parameters and endpoints are algebraic functions of `u`, then its arc length
   `L(u)` is *D-finite* in `u`. That means it satisfies a linear ODE with polynomial
   coefficients in `u`, and so has only finitely many singular points in the complex `u`-plane.
   `am(u)` has infinitely many singularities (branch points where `dn` has poles, at
   `u = 2mK + (2n+1)iK′`), so it is not D-finite, and no such single measurement equals it.
   * Is each step right? Moving endpoints, parameters inside a square root, `offset` (which
     brings in `1/speed`): does D-finiteness survive each of these?
   * Which moves break the argument? Likely candidates: `sin`/`2^x` curves, endpoints that are
     themselves transcendental in `u` (e.g. produced by `ellipticEAm`), and using the output of
     one measurement as a shape parameter of the next.
   * Is `am` really not D-finite? Give a proof or a solid reference.
2. **Curves that escape the test.** The sine curve `y = A sin(Bx)` with `A, B` built from `u`
   has arc length `∫√(1 + A²B² cos²(Bx)) dx`, which is `E` at a modulus depending on `u`. An
   ellipse whose axes depend on `u` gives `E(φ, c(u))` with the parameter moving. Can a
   *moving-modulus* `E`, `F`, or combination, evaluated at a constructible angle, equal `am(u)`
   or `sn(u)` identically? Differentiate in `u` and see what `∂E/∂c` and `∂F/∂c` contribute
   (these are known in closed form, DLMF 19.4). Test candidates numerically.
3. **Integral representations.** Search the literature (DLMF §22, Byrd–Friedman, Gradshteyn–
   Ryzhik 8.1–8.2, papers on "integral representation of Jacobi amplitude") for any formula
   `am(u) = ∫ₐᵇ g(t, u) dt` or `sn(u) = ∫ …` with `g` built from elementary functions. For each
   one found, ask whether it can be arranged as `√(x′² + y′²)` of a drawable curve with
   constructible endpoints.
4. **Two measurements and arithmetic.** Could `am(u)` be `L₁(u) − L₂(u)`, `L₁(u)·L₂(u)`, or
   similar, for two drawable lengths whose boundary terms cancel? Check the test from
   question 1 against this: D-finite functions are closed under `+` and `×`, so a combination
   of algebraic-curve lengths is still excluded. Find the cheapest combination that is not.

## Deliverable

Notes with the plain summary, a verdict on the D-finite test (correct / correct with these
exceptions / wrong), the list of moves that escape it, and any candidate constructions with their
numerical checks.
