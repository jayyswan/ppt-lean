# Level 24: resolved

The `sorry` this file used to describe is gone. `Γ(1/24)` — and with it every `Γ(n/24)` —
is unconditionally P-constructible, and the project has no `sorry` anywhere.

What replaced the assumption is not Chowla–Selberg. It is an explicit degree-12 algebraic
substitution, found in this session; as far as the literature search went, no elementary
derivation at this level was previously known.

## Why a substitution had to exist

Take `C : y² = v - v¹³`, genus 6. The automorphism `σ : v ↦ ζ₁₂ v, y ↦ ζ₂₄ y` acts on the
holomorphic differentials `ωᵢ = v^(i-1) dv/y` by `ζ₂₄^(2i-1)`, so the six of them carry the
characters `ζ₂₄^{1,3,5,7,9,11}`. The exponents coprime to 24 are

    {1, 5, 7, 11}

and **that set is a subgroup** — it is `ker χ₋₂₄ = Gal(ℚ(ζ₂₄)/ℚ(√-6))`. So the CM type of
the corresponding fourfold is *imprimitive*, induced from `ℚ(√-6)`; the fourfold is
isogenous to `E⁴` with `E` having CM by `ℤ[√-6]`, and a nonconstant map `C → E` exists.

The previous session searched for exactly such a substitution and missed it for one reason:
it fitted `x(v) = sn²(λ∫₀ᵛ ω, k)` with `ω` taken to be **one** of `dv/y, v²dv/y, v³dv/y,
v⁵dv/y` at a time. The pullback `φ*ω_E` is necessarily a *linear combination* of all four —
it cannot be a single eigen-differential, since that would force `ζ₂₄ ∈ End(E)`.

The degree of the map is `Σ_h |σ_h(β)|² R_h / (2√6 · N(𝔞_β))` with `R_h = J_h / I_h²`; run
on the k₂ file's curve as a control it returns exactly `2` (matching that file's known
degree-2 substitution), and at level 24 it returns exactly `12`, minimal over all `β` giving
real coefficients.

## The substitution

Degree 12, targeting `k_{3/2}` (the *other* ideal class of disc −24, not `k₆`), with

    κ = k² = -34 + 24√2 + 20√3 - 14√6            A = -(3+2√2)(3+2√3)
    S = v⁴ - c v³ - (c-1) v² - (7+5√2+4√3+3√6) v + (15+10√2+8√3+6√6)
    Q = v² + v - c                                c = cot(π/24) = 2+√2+√3+√6
    T, U  as in `Pptc/Level24Alg.lean`

    M = (v⁴-v²+1) S²      N = A v (v⁴-1)(v²-v+1) Q²
    M - N = (v²+v+1) T²   M - κN = U²

whence `N M (M-N)(M-κN) = A (v¹³-v)(Q S T U)²`. All coefficients are small integers of
`ℚ(√2, √3)`; the identities are `linear_combination` against `√2²=2`, `√3²=3`.

Dividing the Wronskian returns the differential:

    ρ (1 + (√3+√6) v² + (3+√6) v³ + cot(π/24) v⁵),   ρ = √(-A)/(2 cot(π/24))

and the three coefficients agree with the ratios `I₁/I₃, I₁/I₄, I₁/I₆` of the Beta periods,
computed independently from Γ-values. That cross-check is what pinned the result down. It
also *derives* `λ = 3^(1/4)(√2-1)(√3+1)/2`, the Borwein–Zucker constant, rather than
assuming it.

Numerically the whole chain closes: `Γ(1/24)` predicted `23.462487693183324` against
`23.462487693183313`, relative difference `4.5e-16`.

## Where it lives

* `pptc/Pptc/Level24Alg.lean` — the polynomials and the three certifying identities.
* `pptc/Pptc/Level24.lean` — the amplitude `arccos(-T√G/W)` (which runs `0 → π` in one
  monotone pass, so `(0,1)` substitutes in one piece with no splitting), the integrand
  identity, the change of variables, the twelfth-power substitution to four Beta
  integrands, and `lvGamma_key`.
* `pptc/Pptc/Gamma.lean` — `Gamma_one_twentyfourth_Pconstructible`, from `lvGamma_key`
  plus duplication and the three ratios the functional equations already reached.

`#print axioms Gamma_one_twentyfourth_Pconstructible` gives only
`propext, Classical.choice, Quot.sound`.

`Pptc/EllipticFSixthSingular.lean` (the earlier scaffold around `k₆`, which carried the
`sorry`) has been deleted: nothing now depends on the sixth singular value. The `k₆` route
would still need a Landen step from `k_{3/2}`; it is no longer on the critical path.

## Still open, if anyone wants it

The `K(k₆)` identity itself — `K(k₆)² = Γ(1/24)Γ(5/24)Γ(7/24)Γ(11/24)/(384π(√2+1)k₆)` —
is now *provable* from the above plus the descending Landen transformation
`K(k₆) = (1+k'_{3/2})/2 · K(k_{3/2})`, which is an elementary substitution Mathlib lacks.
Nothing in the project needs it.
