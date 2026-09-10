/- Copyright (c) 2024 Lean Community. All rights reserved.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

This file is part of the Pptc (PowerPoint Constructibility) project.
-/

import Pptc.Basic

/-! # Pptc.ThirdKind

The **incomplete** elliptic integral of the third kind,

  `Π(n, φ, c) = ∫₀^φ dθ / ((1 - n sin²θ) √(1 - c sin²θ))`,

and how far the machinery of `Pptc.Basic` reaches into it.

The complete integral was reducible because the elementary antiderivative in the master
identity vanishes at both `0` and `π/2`. At a general upper limit it does not, and what
survives is `thirdKindAnti c n φ`. Two things follow.

* At the three roots `n ∈ {0, c, 1}` of `P(n) = n (c - n) (1 - n)` the cubic drops out of
  the master identity, exactly as it did at `n = c` in the complete case, and `Π` reduces
  to `F`, `E` and elementary terms — for *every* `φ`. (`n = 1` turns out not to need the
  master identity at all: its antiderivative is `F(φ) + (tan φ Δ(φ) - E(φ))/(1 - c)`.)
* For general `n` the surviving term is itself an incomplete `Π` with the parameter and
  the argument *interchanged*, so the system does not close on its own. What comes out is
  Legendre's interchange relation, `ellipticPiAux_interchange` — antisymmetric, hence
  vacuous on the diagonal, so it gives no value of `Π`.
* **For every `n > 1` it is nevertheless P-constructible**
  (`ellipticPiInc_Pconstructible_gt_one`), by a construction that has nothing to do with
  the master identity's boundary term. That is the second half of this file.

The construction rests on a fact about the framework worth stating on its own. Every
constructible curve is a subset of a linear image of one of the six base curves, so every
arc length available is `∫√(x'² + y'²)` for one of those six; a third-kind integral needs a
differential with a nonzero *residue*, and of the six only the cubic Bézier can supply one.
The Bézier used for `F` in `Pptc.Basic` has speed-quartic `(1 - m t²)² + ((1+m) t)²`, which
is even — residue exactly `0`, which is why `F` came out with no third-kind term. Replacing
the constant `1` by a linear form `1 - h t` gives the general cubic Bézier in one extra
parameter, and its arc length does contain a third-kind integral, at

  `n = 1 + h² = sec² ψ₀`,   where `tan ψ₀ = h`.

That is the whole shape of the result, and of its limit: the parameter reached is `sec²` of
a *real* angle, so it is always `> 1`, and `h = 0` is the degenerate `n = 1` that the old
family sat on. Nothing here reaches `n < 1`.

The construction runs: the general Bézier's arc length is P-constructible by
`arc_length`; the moment reduction splits it into an algebraic term and `∫ tʲ dt/√Q` for
`j = 0, 1, 2`; the substitution `t = sin ψ / (cos ψ + h sin ψ)` puts those in Legendre form,
with the `j = 0` moment landing on `F(Φ, c)` exactly; and *adding the arc lengths for `h`
and `-h`* cancels the two elementary integrals that would otherwise have to be evaluated,
leaving `Π` with the coefficient `thirdKindPiCoeff`. That coefficient vanishes only on the
locus `(n-1)² = 1 - c`, where the two Legendre reductions of the same Bézier coincide; that
locus is the one hypothesis of the headline theorem beyond the natural domain. -/

namespace Pconstructible

/-! ### The incomplete integral -/

/-- The incomplete elliptic integral of the third kind. -/
noncomputable def ellipticPiInc (c n φ : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..φ, ellipticPiIntegrand c n θ

-- Theorem: the complete integral is the incomplete one at a quarter turn.
theorem ellipticPi_eq_inc (c n : ℝ) : ellipticPi c n = ellipticPiInc c n (Real.pi / 2) := rfl

-- Theorem: splitting off the `n = 0` part of the integrand leaves `n · A(n, φ)`.
theorem ellipticPiInc_eq_aux {c n : ℝ} (hc : c < 1) (hn : n < 1) (φ : ℝ) :
    ellipticPiInc c n φ = ellipticF c φ + n * ellipticPiAux c n φ := by
  have hpt : ∀ θ : ℝ, ellipticPiIntegrand c n θ
      = ellipticFIntegrand c θ
        + n * (Real.sin θ ^ 2 / ((1 - n * Real.sin θ ^ 2) * ellipticEIntegrand c θ)) := by
    intro θ
    have h1 := (one_sub_mul_sin_sq_pos hn θ).ne'
    have h2 := (ellipticEIntegrand_pos hc θ).ne'
    simp only [ellipticPiIntegrand, ellipticFIntegrand]
    field_simp
    ring
  unfold ellipticPiInc ellipticF ellipticPiAux
  rw [← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add ((continuous_ellipticFIntegrand hc).intervalIntegrable _ _)
      (((continuous_ellipticPiAuxIntegrand hc hn).const_mul n).intervalIntegrable _ _)]
  exact intervalIntegral.integral_congr fun θ _ => hpt θ

/-! ### The three roots of `P`

At `n = 0`, `n = c` and `n = 1` the cubic `P(n) = n (c - n) (1 - n)` vanishes, so the
second integral drops out of the master identity and `A(n, φ)` is pinned by it alone. -/

-- Theorem: at `n = 0` the third-kind integrand is the first-kind one.
theorem ellipticPiInc_zero {c : ℝ} (hc : c < 1) (φ : ℝ) :
    ellipticPiInc c 0 φ = ellipticF c φ := by
  rw [ellipticPiInc_eq_aux hc (by norm_num) φ]; ring

-- Theorem: the antiderivative at `n = c`, where `1 - c sin²θ` is `Δ(θ)²`.
theorem thirdKindAnti_self {c : ℝ} (hc : c < 1) (φ : ℝ) :
    thirdKindAnti c c φ = c * Real.sin φ * Real.cos φ / ellipticEIntegrand c φ := by
  have hE := (ellipticEIntegrand_pos hc φ).ne'
  have hEsq := ellipticEIntegrand_sq hc φ
  rw [thirdKindAnti, ← hEsq]
  field_simp

-- Theorem: at `n = c` the incomplete integral reduces to the second kind plus an
-- elementary term. This is the incomplete form of `ellipticPi_self`.
theorem ellipticPiInc_self {c : ℝ} (hc : c < 1) (φ : ℝ) :
    ellipticPiInc c c φ
      = (ellipticE c φ - c * Real.sin φ * Real.cos φ / ellipticEIntegrand c φ) / (1 - c) := by
  have hkey := integral_thirdKindMaster hc φ
    (fun θ _ => (one_sub_mul_sin_sq_pos hc θ).ne')
  have hzero : thirdKindCubic c c = 0 := by simp [thirdKindCubic]
  have hpt : ∀ θ : ℝ, thirdKindMaster c c θ
      = thirdKindCubicDeriv c c
        * (Real.sin θ ^ 2 / ((1 - c * Real.sin θ ^ 2) * ellipticEIntegrand c θ)) := by
    intro θ
    simp only [thirdKindMaster, hzero]
    ring
  rw [intervalIntegral.integral_congr (g := fun θ : ℝ => thirdKindCubicDeriv c c
      * (Real.sin θ ^ 2 / ((1 - c * Real.sin θ ^ 2) * ellipticEIntegrand c θ)))
      fun θ _ => hpt θ, intervalIntegral.integral_const_mul] at hkey
  rw [← ellipticPiAux, thirdKindAnti_self hc] at hkey
  rw [ellipticPiInc_eq_aux hc hc]
  have hcc : thirdKindCubicDeriv c c = c ^ 2 - c := by simp only [thirdKindCubicDeriv]; ring
  rw [hcc] at hkey
  have hne1 : (1 : ℝ) - c ≠ 0 := by linarith
  rw [eq_div_iff hne1]
  linear_combination -hkey

/-! At `n = 1` the integrand is `1 / (cos²θ Δ(θ))`, which is not defined past a quarter
turn, so the upper limit is restricted. The reduction needs no master identity: the
antiderivative is `F(φ) + (tan φ Δ(φ) - E(φ))/(1 - c)`, whose derivative is
`1/Δ + tan²φ/Δ = sec²φ/Δ` on the nose. -/

/-- The antiderivative of the `n = 1` integrand. -/
noncomputable def thirdKindOneAnti (c φ : ℝ) : ℝ :=
  ellipticF c φ
    + (Real.tan φ * ellipticEIntegrand c φ - ellipticE c φ) / (1 - c)

-- Theorem: it is one.
theorem hasDerivAt_thirdKindOneAnti {c : ℝ} (hc : c < 1) {φ : ℝ} (hcos : Real.cos φ ≠ 0) :
    HasDerivAt (thirdKindOneAnti c) (ellipticPiIntegrand c 1 φ) φ := by
  have hE := ellipticEIntegrand_pos hc φ
  have hne1 : (1 : ℝ) - c ≠ 0 := by linarith
  have hm : Real.sqrt (1 - c) ^ 2 = 1 - c := Real.sq_sqrt (by linarith)
  have h1 := hasDerivAt_ellipticF hc φ
  have h2 := hasDerivAt_ellipticE c φ
  have h3 := hasDerivAt_tan_mul_ellipticEIntegrand hm hc hcos
  have hcs : (1 : ℝ) - 1 * Real.sin φ ^ 2 = Real.cos φ ^ 2 := by
    linear_combination -Real.sin_sq_add_cos_sq φ
  refine (h1.add (((h3.sub h2).div_const (1 - c)))).congr_deriv ?_
  simp only [ellipticPiIntegrand, ellipticFIntegrand, hm, Real.tan_eq_sin_div_cos, hcs]
  field_simp
  linear_combination (1 - c) * Real.sin_sq_add_cos_sq φ

-- Theorem: at `n = 1` the incomplete integral reduces, for `|φ| < π/2`.
theorem ellipticPiInc_one {c : ℝ} (hc : c < 1) {φ : ℝ} (hφ : |φ| < Real.pi / 2) :
    ellipticPiInc c 1 φ
      = ellipticF c φ
        + (Real.tan φ * ellipticEIntegrand c φ - ellipticE c φ) / (1 - c) := by
  have hcos : ∀ ψ ∈ Set.uIcc (0 : ℝ) φ, Real.cos ψ ≠ 0 :=
    fun ψ hψ => (cos_pos_of_mem_uIcc hφ hψ).ne'
  have hint : IntervalIntegrable (ellipticPiIntegrand c 1) MeasureTheory.volume 0 φ := by
    refine ContinuousOn.intervalIntegrable fun ψ hψ => ?_
    refine ContinuousAt.continuousWithinAt (ContinuousAt.div continuousAt_const ?_ ?_)
    · exact (((by fun_prop : Continuous fun s : ℝ => 1 - 1 * Real.sin s ^ 2).mul
        (continuous_ellipticEIntegrand c))).continuousAt
    · have : (1 : ℝ) - 1 * Real.sin ψ ^ 2 = Real.cos ψ ^ 2 := by
        linear_combination -Real.sin_sq_add_cos_sq ψ
      rw [this]
      exact mul_ne_zero (pow_ne_zero 2 (hcos ψ hψ)) (ellipticEIntegrand_pos hc ψ).ne'
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun ψ hψ => hasDerivAt_thirdKindOneAnti hc (hcos ψ hψ)) hint
  have hzero : thirdKindOneAnti c 0 = 0 := by
    simp [thirdKindOneAnti, ellipticF, ellipticE]
  rw [ellipticPiInc, this, hzero, sub_zero, thirdKindOneAnti]

/-! ### P-constructibility at the three roots -/

-- Theorem: `Π(0, φ, c)` is P-constructible.
theorem ellipticPiInc_zero_Pconstructible {c φ : ℝ} (hcP : PConstructible c)
    (hφP : PConstructible φ) (hc : c < 1) : PConstructible (ellipticPiInc c 0 φ) := by
  rw [ellipticPiInc_zero hc]
  exact ellipticF_Pconstructible hcP hφP hc

-- Theorem: `Π(c, φ, c)` is P-constructible.
theorem ellipticPiInc_self_Pconstructible {c φ : ℝ} (hcP : PConstructible c)
    (hφP : PConstructible φ) (hc : c < 1) :
    PConstructible (ellipticPiInc c c φ) := by
  rw [ellipticPiInc_self hc]
  pconstructible

-- Theorem: `Π(1, φ, c)` is P-constructible for `|φ| < π/2`.
theorem ellipticPiInc_one_Pconstructible {c φ : ℝ} (hcP : PConstructible c)
    (hφP : PConstructible φ) (hc : c < 1) (hφ : |φ| < Real.pi / 2) :
    PConstructible (ellipticPiInc c 1 φ) := by
  rw [ellipticPiInc_one hc hφ]
  pconstructible

/-! ### The interchange relation

For a general `n` the boundary term left by the master identity is, once integrated along
the middle path, another incomplete `Π` with the parameter and the argument swapped. The
result is antisymmetric in the two angles — and therefore says nothing on the diagonal,
which is where one would want to solve for a single value. -/

-- Theorem: the boundary term along the middle path is the interchanged integrand.
theorem middleAnti_swap {c : ℝ} (hc : c < 1) (t φ : ℝ) :
    ellipticFIntegrand c t * thirdKindAnti c (c * Real.sin t ^ 2) φ
      = c * Real.sin φ * Real.cos φ * ellipticEIntegrand c φ
        * (Real.sin t ^ 2
          / ((1 - c * Real.sin φ ^ 2 * Real.sin t ^ 2) * ellipticEIntegrand c t)) := by
  have h1 := (ellipticEIntegrand_pos hc t).ne'
  have h2 : (0 : ℝ) < 1 - c * Real.sin t ^ 2 * Real.sin φ ^ 2 :=
    one_sub_mul_sin_sq_pos (middleNu_lt_one hc t) φ
  simp only [ellipticFIntegrand, thirdKindAnti]
  rw [show (1 : ℝ) - c * Real.sin φ ^ 2 * Real.sin t ^ 2
      = 1 - c * Real.sin t ^ 2 * Real.sin φ ^ 2 by ring]
  field_simp

-- Theorem: **Legendre's interchange relation** for the incomplete third kind. Both sides
-- change sign under swapping `β` and `φ`, so the diagonal `β = φ` gives `0 = 0`.
theorem ellipticPiAux_interchange {c : ℝ} (hc : c < 1) (β φ : ℝ) :
    c * Real.sin β * Real.cos β * ellipticEIntegrand c β
        * ellipticPiAux c (c * Real.sin β ^ 2) φ
      - c * Real.sin φ * Real.cos φ * ellipticEIntegrand c φ
        * ellipticPiAux c (c * Real.sin φ ^ 2) β
      = ellipticF c φ * ellipticE c β - ellipticE c φ * ellipticF c β := by
  have hkey := middlePath_key hc β φ
  have hsplit : ∀ t : ℝ, ellipticFIntegrand c t
        * ((1 - c * Real.sin t ^ 2) * ellipticF c φ - ellipticE c φ
          + thirdKindAnti c (c * Real.sin t ^ 2) φ)
      = (ellipticF c φ * ellipticEIntegrand c t - ellipticE c φ * ellipticFIntegrand c t)
        + c * Real.sin φ * Real.cos φ * ellipticEIntegrand c φ
          * (Real.sin t ^ 2
            / ((1 - c * Real.sin φ ^ 2 * Real.sin t ^ 2) * ellipticEIntegrand c t)) := by
    intro t
    rw [mul_add, middleAnti_swap hc t φ]
    congr 1
    have hE := (ellipticEIntegrand_pos hc t).ne'
    have hEsq := ellipticEIntegrand_sq hc t
    simp only [ellipticFIntegrand]
    field_simp
    linear_combination (-ellipticF c φ) * hEsq
  rw [intervalIntegral.integral_congr fun t _ => hsplit t] at hkey
  rw [intervalIntegral.integral_add, intervalIntegral.integral_sub,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, ← ellipticE, ← ellipticF, ← ellipticPiAux] at hkey
  · linarith
  · exact ((continuous_ellipticEIntegrand c).const_mul _).intervalIntegrable _ _
  · exact ((continuous_ellipticFIntegrand hc).const_mul _).intervalIntegrable _ _
  · exact (((continuous_ellipticEIntegrand c).const_mul _).sub
      ((continuous_ellipticFIntegrand hc).const_mul _)).intervalIntegrable _ _
  · exact ((continuous_ellipticPiAuxIntegrand hc
      (middleNu_lt_one hc φ)).const_mul _).intervalIntegrable _ _

/-! ### Investigation: where a third-kind integral could come from

Everything above stops at Legendre's wall. This section records what the search for a way
round it has found; the first step of it is proved, the rest is stated as it stands.

**Every arc length available here is `∫ √(x'² + y'²)`.** Each constructor either produces
one of the six base curves, applies a linear map, or passes to a subset (`restrict` and
`arc_of_length` both do), so every constructible curve is contained in a linear image of a
base curve, and the speeds are exactly those of the six families. A third-kind elliptic
integral is one whose differential has a nonzero *residue*, so the question is which of
those speeds can have one. Expanding `√Q` at infinity answers it:

* `poly_graph` under a linear map has speed `√(A p'² + B p' + C)` for the single quadratic
  `p'`, so `√Q` expands in powers of `1/p' ∼ 1/t²` and the residue vanishes identically;
* the ellipse gives `∫(1 - c t²)dt/√R`, only the even moments, so no residue;
* power laws force the degenerate exponent `b = 0` before a residue appears;
* `exp_two` does have a residue — but its curve is rational, and that is where `log` came
  from rather than anything elliptic;
* **the cubic Bézier is the exception.** Its `x'` and `y'` are two *independent* quadratics,
  so `Q = x'² + y'²` need not be even, and the residue is generally nonzero. The Bézier
  used for `F` in `Pptc.Basic` is `firstKindQuartic m t = (1 - m t²)² + ((1 + m) t)²`, which
  *is* even — residue exactly `0`. That is why `F` came out with no third-kind term, and it
  means the general Bézier is an unexploited resource.

The first step is the moment reduction below: `∫₀^T √Q` is an algebraic term plus a
combination of the three moments `∫ t^j dt/√Q`, `j = 0, 1, 2`, and `∫ t dt/√Q` is precisely
the third-kind one (`dt/√Q` is first kind, `t² dt/√Q` second, `t dt/√Q` has the residue).

What numerics then say, checked to 40+ digits on random Béziers, is that the rest of the
chain closes:

* reducing `Q` to `(1 + u²)(1 + κ²u²)` by a real Möbius map `t = M(u)` and then `u = tan ψ`
  puts everything on the Legendre curve at parameter `c = 1 - κ²`;
* `∫dt/√Q` is `F(ψ, c)` on the nose, and `∫t dt/√Q` fits `{F(ψ,c), Π(n;ψ,c), elementary}`
  exactly, where `n` comes from `u₀ = M⁻¹(∞)` as `n = (1 + u₀²)/u₀²`;
* the whole arc length fits `{algebraic, 1, F, E, Π, elementary}` exactly, with a nonzero
  coefficient on `Π`.

So the arc length of a general cubic Bézier really does contain an incomplete third-kind
integral. **But the parameter it reaches is always `n > 1`.** That is forced, not accidental:
the arc-length differential has its poles at the point at infinity of the Bézier parameter,
`M⁻¹(∞) = u₀` is a *real* number, so in the Legendre variable the pole lands at
`s₀ = sin (arctan u₀)` with `|s₀| < 1`, and `n = 1/s₀² > 1`. Every one of 1486 sampled
Béziers obeyed it. The two Legendre reductions of a single Bézier (they differ by
`u ↦ 1/(κu)`) give parameters `n₁, n₂` satisfying `(n₁ - 1)(n₂ - 1) = 1 - c`, and between
them `n` ranges over all of `(1, ∞)`.

That is the state of it. `n > 1` is exactly the range this project's complete-integral
theorem excludes, so it is new ground rather than a second route to old ground; and `n < 1`
— the classical range — stays out of reach, because no constructible curve has an
arc-length differential whose pole sits anywhere but at infinity. -/

/-- A quartic in coefficient form. -/
def quartic (q₄ q₃ q₂ q₁ q₀ t : ℝ) : ℝ := q₄ * t ^ 4 + q₃ * t ^ 3 + q₂ * t ^ 2 + q₁ * t + q₀

/-- The algebraic part of the moment reduction of `∫ √Q`. -/
noncomputable def quarticArcAnti (q₄ q₃ q₂ q₁ q₀ t : ℝ) : ℝ :=
  (q₃ / (12 * q₄) + t / 3) * Real.sqrt (quartic q₄ q₃ q₂ q₁ q₀ t)

theorem quarticArc_alg {w D q₄ q₃ q₂ q₁ q₀ t : ℝ} (hw : w ≠ 0) (hq₄ : q₄ ≠ 0)
    (hsq : w ^ 2 = q₄ * t ^ 4 + q₃ * t ^ 3 + q₂ * t ^ 2 + q₁ * t + q₀)
    (hD : D = 4 * q₄ * t ^ 3 + 3 * q₃ * t ^ 2 + 2 * q₂ * t + q₁) :
    1 / 3 * w + (q₃ / (12 * q₄) + t / 3) * (D / (2 * w))
      = w - ((2 * q₀ / 3 - q₃ * q₁ / (24 * q₄))
          + (q₁ / 2 - q₃ * q₂ / (12 * q₄)) * t
          + (q₂ / 3 - q₃ ^ 2 / (8 * q₄)) * t ^ 2) / w := by
  subst hD
  field_simp
  linear_combination (-9216 * q₄) * hsq

-- Theorem: the moment reduction. `√Q` differs from an explicit algebraic derivative by
-- `(α + β t + γ t²)/√Q`, so an arc length `∫ √Q` is an algebraic term plus a combination of
-- the three moments. The middle one, `β ∫ t dt/√Q`, is the third-kind piece.
theorem hasDerivAt_quarticArcAnti {q₄ q₃ q₂ q₁ q₀ : ℝ} (hq₄ : q₄ ≠ 0)
    (hpos : ∀ s : ℝ, 0 < quartic q₄ q₃ q₂ q₁ q₀ s) (t : ℝ) :
    HasDerivAt (quarticArcAnti q₄ q₃ q₂ q₁ q₀)
      (Real.sqrt (quartic q₄ q₃ q₂ q₁ q₀ t)
        - ((2 * q₀ / 3 - q₃ * q₁ / (24 * q₄))
            + (q₁ / 2 - q₃ * q₂ / (12 * q₄)) * t
            + (q₂ / 3 - q₃ ^ 2 / (8 * q₄)) * t ^ 2)
          / Real.sqrt (quartic q₄ q₃ q₂ q₁ q₀ t)) t := by
  have hQ := hpos t
  have hs : 0 < Real.sqrt (quartic q₄ q₃ q₂ q₁ q₀ t) := Real.sqrt_pos.mpr hQ
  have hsq : Real.sqrt (quartic q₄ q₃ q₂ q₁ q₀ t) ^ 2
      = q₄ * t ^ 4 + q₃ * t ^ 3 + q₂ * t ^ 2 + q₁ * t + q₀ := Real.sq_sqrt hQ.le
  have hQd : HasDerivAt (quartic q₄ q₃ q₂ q₁ q₀)
      (4 * q₄ * t ^ 3 + 3 * q₃ * t ^ 2 + 2 * q₂ * t + q₁) t := by
    have h4 := (hasDerivAt_pow 4 t).const_mul q₄
    have h3 := (hasDerivAt_pow 3 t).const_mul q₃
    have h2 := (hasDerivAt_pow 2 t).const_mul q₂
    have h1 := (hasDerivAt_id t).const_mul q₁
    exact ((((h4.add h3).add h2).add h1).add_const q₀).congr_deriv (by push_cast; ring)
  have hroot := hQd.sqrt hQ.ne'
  have hlin : HasDerivAt (fun s : ℝ => q₃ / (12 * q₄) + s / 3) (1 / 3) t := by
    simpa using ((hasDerivAt_id t).div_const 3).const_add (q₃ / (12 * q₄))
  exact (hlin.mul hroot).congr_deriv (quarticArc_alg hs.ne' hq₄ hsq rfl)

-- Theorem: integrating it. `∫₀^T √Q` is an algebraic term plus the three moments; the
-- coefficient of the third-kind moment `∫ t dt/√Q` is `q₁/2 - q₃q₂/(12q₄)`, which vanishes
-- exactly when the reduction has no third-kind content.
theorem integral_sqrt_quartic {q₄ q₃ q₂ q₁ q₀ : ℝ} (hq₄ : q₄ ≠ 0)
    (hpos : ∀ s : ℝ, 0 < quartic q₄ q₃ q₂ q₁ q₀ s) (T : ℝ) :
    (∫ t in (0 : ℝ)..T, Real.sqrt (quartic q₄ q₃ q₂ q₁ q₀ t))
      = (quarticArcAnti q₄ q₃ q₂ q₁ q₀ T - quarticArcAnti q₄ q₃ q₂ q₁ q₀ 0)
        + ∫ t in (0 : ℝ)..T,
            ((2 * q₀ / 3 - q₃ * q₁ / (24 * q₄))
              + (q₁ / 2 - q₃ * q₂ / (12 * q₄)) * t
              + (q₂ / 3 - q₃ ^ 2 / (8 * q₄)) * t ^ 2)
            / Real.sqrt (quartic q₄ q₃ q₂ q₁ q₀ t) := by
  have hQc : Continuous (quartic q₄ q₃ q₂ q₁ q₀) := by unfold quartic; fun_prop
  have hroot : Continuous fun t : ℝ => Real.sqrt (quartic q₄ q₃ q₂ q₁ q₀ t) :=
    Real.continuous_sqrt.comp hQc
  have hne : ∀ t : ℝ, Real.sqrt (quartic q₄ q₃ q₂ q₁ q₀ t) ≠ 0 :=
    fun t => (Real.sqrt_pos.mpr (hpos t)).ne'
  have hmom : Continuous fun t : ℝ =>
      ((2 * q₀ / 3 - q₃ * q₁ / (24 * q₄))
        + (q₁ / 2 - q₃ * q₂ / (12 * q₄)) * t
        + (q₂ / 3 - q₃ ^ 2 / (8 * q₄)) * t ^ 2)
      / Real.sqrt (quartic q₄ q₃ q₂ q₁ q₀ t) :=
    (by fun_prop : Continuous fun t : ℝ =>
      ((2 * q₀ / 3 - q₃ * q₁ / (24 * q₄))
        + (q₁ / 2 - q₃ * q₂ / (12 * q₄)) * t
        + (q₂ / 3 - q₃ ^ 2 / (8 * q₄)) * t ^ 2)).div hroot hne
  have hkey := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_quarticArcAnti hq₄ hpos t)
    ((hroot.sub hmom).intervalIntegrable 0 T)
  rw [intervalIntegral.integral_sub (hroot.intervalIntegrable 0 T)
    (hmom.intervalIntegrable 0 T)] at hkey
  linarith

/-! ### The general cubic Bézier, in one extra parameter

The `firstKind` family in `Pptc.Basic` uses the quartic `(1 - m t²)² + ((1+m) t)²`, which is
even, and that is exactly why it carries no third-kind content. Replacing the constant `1`
by a linear form `1 - h t` — and keeping Brahmagupta–Fibonacci, so the quartic is still
visibly a sum of two squares of quadratics, i.e. still the speed of a cubic Bézier — gives
the general case in *one* extra parameter `h`. Setting `h = 0` recovers the old family.

The whole reduction survives the change. Writing `D(ψ) = cos ψ + h sin ψ`, the substitution
`t = sin ψ / D(ψ)` (which is `t = tan ψ` when `h = 0`) gives

  `√Q = Δ(ψ) / D(ψ)²`,   `dt/dψ = 1 / D(ψ)²`,   so   `speed dψ = Δ(ψ) dψ / D(ψ)⁴`,

against the old `Δ(ψ) dψ / cos⁴ψ`. Since `D(ψ) = √(1+h²)·cos(ψ - ψ₀)` with `tan ψ₀ = h`, the
arc length of a general cubic Bézier is the old integral **shifted by an angle** `ψ₀`, and
rationalising `1/D⁴` produces the factor `1 - n sin²ψ` with

  `n = 1 + h² = sec² ψ₀`.

That is the whole story of the third kind in this framework, in one line: the parameter
reached is `sec²` of a real angle, hence always `> 1`, and `h = 0` is the degenerate `n = 1`
that the old family sat on. -/

/-- The quartic met by a general cubic Bézier: `firstKindQuartic` with `1` replaced by the
linear form `1 - h t`. -/
def thirdKindQuartic (m h t : ℝ) : ℝ :=
  ((1 - h * t) ^ 2 - m * t ^ 2) ^ 2 + ((1 + m) * (1 - h * t) * t) ^ 2

-- Theorem: Brahmagupta–Fibonacci again — the sum of two squares splits.
theorem thirdKindQuartic_eq (m h t : ℝ) :
    thirdKindQuartic m h t
      = ((1 - h * t) ^ 2 + t ^ 2) * ((1 - h * t) ^ 2 + m ^ 2 * t ^ 2) := by
  unfold thirdKindQuartic; ring

-- Theorem: `h = 0` is the family already in `Pptc.Basic`.
theorem thirdKindQuartic_zero (m t : ℝ) : thirdKindQuartic m 0 t = firstKindQuartic m t := by
  unfold thirdKindQuartic firstKindQuartic; ring

theorem thirdKindQuartic_pos {m : ℝ} (hm : m ≠ 0) (h t : ℝ) : 0 < thirdKindQuartic m h t := by
  rw [thirdKindQuartic_eq]
  have h1 : 0 < (1 - h * t) ^ 2 + t ^ 2 := by
    rcases eq_or_ne t 0 with rfl | ht
    · norm_num
    · positivity
  have h2 : 0 < (1 - h * t) ^ 2 + m ^ 2 * t ^ 2 := by
    rcases eq_or_ne t 0 with rfl | ht
    · norm_num
    · positivity
  positivity

/-- The cubic curve whose speed is `√(thirdKindQuartic m h ·)`: the componentwise
antiderivative of `((1 - h t)² - m t², (1+m)(1 - h t) t)`. -/
noncomputable def thirdKindCurve (m h t : ℝ) : ℝ × ℝ :=
  (t - h * t ^ 2 + (h ^ 2 - m) * t ^ 3 / 3, (1 + m) * (t ^ 2 / 2 - h * t ^ 3 / 3))

-- Theorem: `h = 0` is the curve already in `Pptc.Basic`.
theorem thirdKindCurve_zero (m t : ℝ) : thirdKindCurve m 0 t = firstKindCurve m t := by
  simp only [thirdKindCurve, firstKindCurve, Prod.mk.injEq]
  constructor <;> ring

-- Theorem: it is a cubic Bézier, with these control points — the `h = 0` case is
-- `bezierParam_firstKind`.
theorem bezierParam_thirdKind (m h T s : ℝ) :
    bezierParam (0, 0) (T / 3, 0) (2 * T / 3 - h * T ^ 2 / 3, (1 + m) * T ^ 2 / 6)
        (T - h * T ^ 2 + (h ^ 2 - m) * T ^ 3 / 3, (1 + m) * (T ^ 2 / 2 - h * T ^ 3 / 3)) s
      = thirdKindCurve m h (T * s) := by
  simp only [bezierParam, thirdKindCurve, Prod.mk.injEq]
  constructor <;> ring

/-- The denominator `D(ψ) = cos ψ + h sin ψ` that replaces `cos ψ`. -/
noncomputable def thirdKindDen (h ψ : ℝ) : ℝ := Real.cos ψ + h * Real.sin ψ

/-- The substitution `t = sin ψ / D(ψ)`, which is `t = tan ψ` when `h = 0`. -/
noncomputable def thirdKindTan (h ψ : ℝ) : ℝ := Real.sin ψ / thirdKindDen h ψ

-- Theorem: the linear form pulls back to `cos ψ / D(ψ)`.
theorem one_sub_mul_thirdKindTan {h ψ : ℝ} (hD : thirdKindDen h ψ ≠ 0) :
    1 - h * thirdKindTan h ψ = Real.cos ψ / thirdKindDen h ψ := by
  rw [thirdKindTan, thirdKindDen] at *
  field_simp
  ring

-- Theorem: the substitution has derivative `1 / D(ψ)²`.
theorem hasDerivAt_thirdKindTan {h ψ : ℝ} (hD : thirdKindDen h ψ ≠ 0) :
    HasDerivAt (thirdKindTan h) (1 / thirdKindDen h ψ ^ 2) ψ := by
  have hden : HasDerivAt (thirdKindDen h) (-Real.sin ψ + h * Real.cos ψ) ψ := by
    have := (Real.hasDerivAt_cos ψ).add ((Real.hasDerivAt_sin ψ).const_mul h)
    exact this.congr_deriv (by ring)
  refine ((Real.hasDerivAt_sin ψ).div hden hD).congr_deriv ?_
  rw [thirdKindDen] at hD ⊢
  field_simp
  linear_combination Real.sin_sq_add_cos_sq ψ

-- Theorem: the key substitution identity. `√Q` at `t = sin ψ / D(ψ)` is `Δ(ψ) / D(ψ)²`,
-- generalising `sqrt_firstKindQuartic_tan`.
theorem sqrt_thirdKindQuartic_tan {c m h ψ : ℝ} (hm : m ^ 2 = 1 - c) (hc : c < 1)
    (hD : thirdKindDen h ψ ≠ 0) :
    Real.sqrt (thirdKindQuartic m h (thirdKindTan h ψ))
      = ellipticEIntegrand c ψ / thirdKindDen h ψ ^ 2 := by
  have hE := ellipticEIntegrand_pos hc ψ
  have hEsq := ellipticEIntegrand_sq hc ψ
  have hkey : thirdKindQuartic m h (thirdKindTan h ψ)
      = (ellipticEIntegrand c ψ / thirdKindDen h ψ ^ 2) ^ 2 := by
    rw [thirdKindQuartic_eq, one_sub_mul_thirdKindTan hD, thirdKindTan]
    rw [thirdKindDen] at hD ⊢
    field_simp
    linear_combination (-1 : ℝ) * hEsq
      + (1 + m ^ 2 * Real.sin ψ ^ 2 + Real.cos ψ ^ 2) * Real.sin_sq_add_cos_sq ψ
      + Real.sin ψ ^ 2 * hm
  rw [hkey, Real.sqrt_sq (by positivity)]

/-- The general cubic Bézier, read in the angle `ψ`. -/
noncomputable def thirdKindTanParam (m h : ℝ) : ℝ → ℝ × ℝ :=
  fun ψ => thirdKindCurve m h (thirdKindTan h ψ)

theorem hasDerivAt_thirdKindTanParam_fst {m h ψ : ℝ} (hD : thirdKindDen h ψ ≠ 0) :
    HasDerivAt (fun s : ℝ => (thirdKindTanParam m h s).1)
      (((1 - h * thirdKindTan h ψ) ^ 2 - m * thirdKindTan h ψ ^ 2)
        * (1 / thirdKindDen h ψ ^ 2)) ψ := by
  set t := thirdKindTan h ψ with ht
  have hg : HasDerivAt (fun s : ℝ => s - h * s ^ 2 + (h ^ 2 - m) * s ^ 3 / 3)
      ((1 - h * t) ^ 2 - m * t ^ 2) t := by
    have h1 := hasDerivAt_id t
    have h2 := (hasDerivAt_pow 2 t).const_mul h
    have h3 := ((hasDerivAt_pow 3 t).const_mul (h ^ 2 - m)).div_const 3
    exact ((h1.sub h2).add h3).congr_deriv (by push_cast; ring)
  exact hg.comp ψ (hasDerivAt_thirdKindTan hD)

theorem hasDerivAt_thirdKindTanParam_snd {m h ψ : ℝ} (hD : thirdKindDen h ψ ≠ 0) :
    HasDerivAt (fun s : ℝ => (thirdKindTanParam m h s).2)
      (((1 + m) * (1 - h * thirdKindTan h ψ) * thirdKindTan h ψ)
        * (1 / thirdKindDen h ψ ^ 2)) ψ := by
  set t := thirdKindTan h ψ with ht
  have hg : HasDerivAt (fun s : ℝ => (1 + m) * (s ^ 2 / 2 - h * s ^ 3 / 3))
      ((1 + m) * (1 - h * t) * t) t := by
    have h2 := (hasDerivAt_pow 2 t).div_const 2
    have h3 := ((hasDerivAt_pow 3 t).const_mul h).div_const 3
    exact ((h2.sub h3).const_mul (1 + m)).congr_deriv (by push_cast; ring)
  have hcomp := hg.comp ψ (hasDerivAt_thirdKindTan hD)
  exact hcomp

-- Theorem: **the general Bézier, read in the angle.** Its speed is `Δ(ψ)/D(ψ)⁴`, against
-- `Δ(ψ)/cos⁴ψ` for the family already in `Pptc.Basic`. Since `D(ψ) = √(1+h²) cos(ψ - ψ₀)`
-- with `tan ψ₀ = h`, a general cubic Bézier's arc length is the old integral shifted by a
-- real angle — and that shift is the entire source of third-kind content.
theorem speed_thirdKindTanParam {c m h : ℝ} (hm : m ^ 2 = 1 - c) (hc : c < 1) {ψ : ℝ}
    (hD : thirdKindDen h ψ ≠ 0) :
    speed (thirdKindTanParam m h) ψ
      = ellipticEIntegrand c ψ / thirdKindDen h ψ ^ 4 := by
  have hE := ellipticEIntegrand_pos hc ψ
  have hm0 : m ≠ 0 := by
    intro h0; rw [h0] at hm; nlinarith
  have hQpos := thirdKindQuartic_pos hm0 h (thirdKindTan h ψ)
  have hQ : thirdKindQuartic m h (thirdKindTan h ψ)
      = (ellipticEIntegrand c ψ / thirdKindDen h ψ ^ 2) ^ 2 := by
    rw [← sqrt_thirdKindQuartic_tan hm hc hD, Real.sq_sqrt hQpos.le]
  rw [speed, (hasDerivAt_thirdKindTanParam_fst hD).deriv,
    (hasDerivAt_thirdKindTanParam_snd hD).deriv]
  have hsum : (((1 - h * thirdKindTan h ψ) ^ 2 - m * thirdKindTan h ψ ^ 2)
        * (1 / thirdKindDen h ψ ^ 2)) ^ 2
      + (((1 + m) * (1 - h * thirdKindTan h ψ) * thirdKindTan h ψ)
        * (1 / thirdKindDen h ψ ^ 2)) ^ 2
      = (ellipticEIntegrand c ψ / thirdKindDen h ψ ^ 4) ^ 2 := by
    have hbase : ((1 - h * thirdKindTan h ψ) ^ 2 - m * thirdKindTan h ψ ^ 2) ^ 2
        + ((1 + m) * (1 - h * thirdKindTan h ψ) * thirdKindTan h ψ) ^ 2
        = (ellipticEIntegrand c ψ / thirdKindDen h ψ ^ 2) ^ 2 := hQ
    calc (((1 - h * thirdKindTan h ψ) ^ 2 - m * thirdKindTan h ψ ^ 2)
            * (1 / thirdKindDen h ψ ^ 2)) ^ 2
          + (((1 + m) * (1 - h * thirdKindTan h ψ) * thirdKindTan h ψ)
            * (1 / thirdKindDen h ψ ^ 2)) ^ 2
        = (((1 - h * thirdKindTan h ψ) ^ 2 - m * thirdKindTan h ψ ^ 2) ^ 2
            + ((1 + m) * (1 - h * thirdKindTan h ψ) * thirdKindTan h ψ) ^ 2)
          * (1 / thirdKindDen h ψ ^ 2) ^ 2 := by ring
      _ = (ellipticEIntegrand c ψ / thirdKindDen h ψ ^ 2) ^ 2
          * (1 / thirdKindDen h ψ ^ 2) ^ 2 := by rw [hbase]
      _ = (ellipticEIntegrand c ψ / thirdKindDen h ψ ^ 4) ^ 2 := by field_simp
  rw [hsum]
  exact Real.sqrt_sq (by positivity)

-- Theorem: the parameter the shift produces. Rationalising `1/D(ψ)²` throws up the factor
-- `1 - n sin²ψ` with `n = 1 + h²`, and `1 + h² > 1` for every real `h`. This is the whole
-- obstruction in one line: the reachable parameter is `sec²` of a real angle.
theorem thirdKindDen_mul_conj (h ψ : ℝ) :
    thirdKindDen h ψ * (Real.cos ψ - h * Real.sin ψ)
      = 1 - (1 + h ^ 2) * Real.sin ψ ^ 2 := by
  rw [thirdKindDen]
  linear_combination Real.sin_sq_add_cos_sq ψ

/-! #### The change of variables, and the three moments

`integral_sqrt_quartic` splits an arc length `∫√Q` into an algebraic term and the three
moments `∫ tʲ dt/√Q`, `j = 0, 1, 2`. Pulling those back along `t = sin ψ / D(ψ)` puts each
into Legendre form, and the middle one — the third-kind moment — is where `Π` appears.

The two proved here are the point of the whole exercise:

* `j = 0` gives `F(Φ, c)` exactly, nothing bolted on;
* `j = 1` gives `∫ sin ψ (cos ψ - h sin ψ) dψ / ((1 - n sin²ψ) Δ(ψ))` with `n = 1 + h²`,
  whose second half is `-h` times the auxiliary integral `A(n, ·)` of `Pptc.Basic` — and
  `Π = F + n·A`. So the third kind really does appear, at parameter `n = 1 + h²`.

The standing hypothesis is that `1 - n sin²ψ` does not vanish on the interval, which is
exactly the statement that the path stops short of the pole of `Π(n; ·, c)`. It implies
`D(ψ) ≠ 0`, since `D(ψ)·(cos ψ - h sin ψ) = 1 - n sin²ψ`. -/

theorem thirdKindDen_ne_zero {h ψ : ℝ} (hn : 1 - (1 + h ^ 2) * Real.sin ψ ^ 2 ≠ 0) :
    thirdKindDen h ψ ≠ 0 := by
  intro h0
  exact hn (by rw [← thirdKindDen_mul_conj, h0, zero_mul])

theorem thirdKindConj_ne_zero {h ψ : ℝ} (hn : 1 - (1 + h ^ 2) * Real.sin ψ ^ 2 ≠ 0) :
    Real.cos ψ - h * Real.sin ψ ≠ 0 := by
  intro h0
  exact hn (by rw [← thirdKindDen_mul_conj, h0, mul_zero])

theorem integral_comp_thirdKindTan {h Φ : ℝ}
    (hD : ∀ ψ ∈ Set.uIcc (0 : ℝ) Φ, thirdKindDen h ψ ≠ 0)
    {g : ℝ → ℝ} (hg : Continuous g) :
    (∫ ψ in (0 : ℝ)..Φ, (1 / thirdKindDen h ψ ^ 2) * g (thirdKindTan h ψ))
      = ∫ t in (0 : ℝ)..thirdKindTan h Φ, g t := by
  have hd : ∀ ψ ∈ Set.uIcc (0 : ℝ) Φ,
      HasDerivAt (thirdKindTan h) (1 / thirdKindDen h ψ ^ 2) ψ :=
    fun ψ hψ => hasDerivAt_thirdKindTan (hD ψ hψ)
  have hc' : ContinuousOn (fun ψ => 1 / thirdKindDen h ψ ^ 2) (Set.uIcc (0 : ℝ) Φ) := by
    refine ContinuousOn.div continuousOn_const
      (Continuous.continuousOn (by unfold thirdKindDen; fun_prop))
      fun ψ hψ => pow_ne_zero 2 (hD ψ hψ)
  have h0 : thirdKindTan h 0 = 0 := by simp [thirdKindTan, thirdKindDen]
  simpa [h0] using intervalIntegral.integral_deriv_smul_comp hd hc' hg

theorem continuous_thirdKindQuartic (m h : ℝ) : Continuous (thirdKindQuartic m h) := by
  unfold thirdKindQuartic; fun_prop

-- Theorem: the zeroth moment is `F` on the nose. The general Bézier meets the first-kind
-- integral exactly as the special one did.
theorem integral_inv_sqrt_thirdKindQuartic {c m h Φ : ℝ} (hm : m ^ 2 = 1 - c) (hc : c < 1)
    (hD : ∀ ψ ∈ Set.uIcc (0 : ℝ) Φ, thirdKindDen h ψ ≠ 0) :
    (∫ t in (0 : ℝ)..thirdKindTan h Φ, 1 / Real.sqrt (thirdKindQuartic m h t))
      = ellipticF c Φ := by
  have hm0 : m ≠ 0 := by intro h0; rw [h0] at hm; nlinarith
  have hgc : Continuous fun t : ℝ => 1 / Real.sqrt (thirdKindQuartic m h t) :=
    continuous_const.div (Real.continuous_sqrt.comp (continuous_thirdKindQuartic m h))
      fun t => (Real.sqrt_pos.mpr (thirdKindQuartic_pos hm0 h t)).ne'
  rw [← integral_comp_thirdKindTan hD hgc, ellipticF]
  refine intervalIntegral.integral_congr fun ψ hψ => ?_
  have hE := ellipticEIntegrand_pos hc ψ
  have hDψ := hD ψ hψ
  rw [sqrt_thirdKindQuartic_tan hm hc hDψ, ellipticFIntegrand]
  field_simp

-- Theorem: the first moment, pulled back. This is the third-kind moment: the factor
-- `1 - (1 + h²) sin²ψ` in the denominator is the characteristic of `Π` at `n = 1 + h²`.
theorem integral_mul_inv_sqrt_thirdKindQuartic {c m h Φ : ℝ} (hm : m ^ 2 = 1 - c) (hc : c < 1)
    (hn : ∀ ψ ∈ Set.uIcc (0 : ℝ) Φ, 1 - (1 + h ^ 2) * Real.sin ψ ^ 2 ≠ 0) :
    (∫ t in (0 : ℝ)..thirdKindTan h Φ, t / Real.sqrt (thirdKindQuartic m h t))
      = ∫ ψ in (0 : ℝ)..Φ, Real.sin ψ * (Real.cos ψ - h * Real.sin ψ)
          / ((1 - (1 + h ^ 2) * Real.sin ψ ^ 2) * ellipticEIntegrand c ψ) := by
  have hm0 : m ≠ 0 := by intro h0; rw [h0] at hm; nlinarith
  have hD : ∀ ψ ∈ Set.uIcc (0 : ℝ) Φ, thirdKindDen h ψ ≠ 0 :=
    fun ψ hψ => thirdKindDen_ne_zero (hn ψ hψ)
  have hgc : Continuous fun t : ℝ => t / Real.sqrt (thirdKindQuartic m h t) :=
    continuous_id.div (Real.continuous_sqrt.comp (continuous_thirdKindQuartic m h))
      fun t => (Real.sqrt_pos.mpr (thirdKindQuartic_pos hm0 h t)).ne'
  rw [← integral_comp_thirdKindTan hD hgc]
  refine intervalIntegral.integral_congr fun ψ hψ => ?_
  have hE := ellipticEIntegrand_pos hc ψ
  have hDψ := hD ψ hψ
  have hcj := thirdKindConj_ne_zero (hn ψ hψ)
  have hcj2 : -(Real.sin ψ * h) + Real.cos ψ ≠ 0 := by intro h0; exact hcj (by linarith)
  rw [sqrt_thirdKindQuartic_tan hm hc hDψ, thirdKindTan,
    show (1 : ℝ) - (1 + h ^ 2) * Real.sin ψ ^ 2
      = thirdKindDen h ψ * (Real.cos ψ - h * Real.sin ψ) from
      (thirdKindDen_mul_conj h ψ).symm]
  have hcj3 : Real.cos ψ - Real.sin ψ * h ≠ 0 := by intro h0; exact hcj (by linarith)
  field_simp

-- Theorem: **the third kind, isolated.** Splitting the first moment by partial fractions
-- leaves an elementary integral and exactly `-h · A(1 + h², Φ)`, where `A` is the auxiliary
-- integral of `Pptc.Basic`. Since `Π = F + n·A`, a general cubic Bézier's arc length
-- contains the incomplete elliptic integral of the third kind at parameter `n = 1 + h²`,
-- and at no other. `h = 0` is the file's old family, where the term is absent.
theorem thirdKindMoment_one {c m h Φ : ℝ} (hm : m ^ 2 = 1 - c) (hc : c < 1)
    (hn : ∀ ψ ∈ Set.uIcc (0 : ℝ) Φ, 1 - (1 + h ^ 2) * Real.sin ψ ^ 2 ≠ 0) :
    (∫ t in (0 : ℝ)..thirdKindTan h Φ, t / Real.sqrt (thirdKindQuartic m h t))
      = (∫ ψ in (0 : ℝ)..Φ, Real.sin ψ * Real.cos ψ
            / ((1 - (1 + h ^ 2) * Real.sin ψ ^ 2) * ellipticEIntegrand c ψ))
        - h * ellipticPiAux c (1 + h ^ 2) Φ := by
  have hden : ∀ ψ ∈ Set.uIcc (0 : ℝ) Φ,
      (1 - (1 + h ^ 2) * Real.sin ψ ^ 2) * ellipticEIntegrand c ψ ≠ 0 :=
    fun ψ hψ => mul_ne_zero (hn ψ hψ) (ellipticEIntegrand_pos hc ψ).ne'
  have hcd : ContinuousOn (fun ψ : ℝ =>
      (1 - (1 + h ^ 2) * Real.sin ψ ^ 2) * ellipticEIntegrand c ψ) (Set.uIcc (0 : ℝ) Φ) :=
    (Continuous.continuousOn (by fun_prop)).mul
      (continuous_ellipticEIntegrand c).continuousOn
  have hi1 : IntervalIntegrable (fun ψ : ℝ => Real.sin ψ * Real.cos ψ
      / ((1 - (1 + h ^ 2) * Real.sin ψ ^ 2) * ellipticEIntegrand c ψ))
      MeasureTheory.volume 0 Φ :=
    ContinuousOn.intervalIntegrable
      ((Continuous.continuousOn (by fun_prop)).div hcd hden)
  have hi2 : IntervalIntegrable (fun ψ : ℝ => h * (Real.sin ψ ^ 2
      / ((1 - (1 + h ^ 2) * Real.sin ψ ^ 2) * ellipticEIntegrand c ψ)))
      MeasureTheory.volume 0 Φ :=
    ContinuousOn.intervalIntegrable
      (continuousOn_const.mul ((Continuous.continuousOn (by fun_prop)).div hcd hden))
  rw [integral_mul_inv_sqrt_thirdKindQuartic hm hc hn, ellipticPiAux,
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hi1 hi2]
  refine intervalIntegral.integral_congr fun ψ hψ => ?_
  have := hden ψ hψ
  field_simp

/-! #### The general Bézier as a drawable curve

Everything above is calculus. This is the geometric input: the cubic is a Bézier with
P-constructible control points, and the arc swept over `[0, Φ]` is injective and smooth, so
`PConstructible.arc_length` applies. The standing hypotheses are `0 < Φ < π/2` and
`(1 + h²) sin²Φ < 1` — the second says the arc stops short of the pole of `Π(1 + h²; ·, c)`,
and it is what keeps `D(ψ)` positive. -/

theorem thirdKindBezier_PConstructibleCurve {m h T : ℝ} (hm : PConstructible m)
    (hh : PConstructible h) (hT : PConstructible T) :
    PConstructibleCurve (bezierParam (0, 0) (T / 3, 0)
      (2 * T / 3 - h * T ^ 2 / 3, (1 + m) * T ^ 2 / 6)
      (T - h * T ^ 2 + (h ^ 2 - m) * T ^ 3 / 3, (1 + m) * (T ^ 2 / 2 - h * T ^ 3 / 3)) ''
      Set.Icc 0 1) := by
  have h3 : PConstructible (3 : ℝ) := three_Pconstructible
  have h6 : PConstructible (6 : ℝ) := by
    convert PConstructible.mul two_Pconstructible h3 using 1; norm_num
  have hT2 : PConstructible (T ^ 2) := sq_Pconstructible hT
  have hT3 : PConstructible (T ^ 3) := by
    convert PConstructible.mul hT2 hT using 1; ring
  have h1m : PConstructible (1 + m) := PConstructible.add PConstructible.base_one hm
  exact PConstructibleCurve.cubic_bezier _ _ _ _
    zero_Pconstructible zero_Pconstructible (PConstructible.div hT h3) zero_Pconstructible
    (PConstructible.sub (PConstructible.div (PConstructible.mul two_Pconstructible hT) h3)
      (PConstructible.div (PConstructible.mul hh hT2) h3))
    (PConstructible.div (PConstructible.mul h1m hT2) h6)
    (PConstructible.add (PConstructible.sub hT (PConstructible.mul hh hT2))
      (PConstructible.div (PConstructible.mul (PConstructible.sub (sq_Pconstructible hh) hm)
        hT3) h3))
    (PConstructible.mul h1m (PConstructible.sub (PConstructible.div hT2 two_Pconstructible)
      (PConstructible.div (PConstructible.mul hh hT3) h3)))

-- Theorem: below the pole and inside a quarter turn, `D(ψ)` is positive.
theorem thirdKindDen_pos {h ψ : ℝ} (hcos : 0 < Real.cos ψ)
    (hp : (1 + h ^ 2) * Real.sin ψ ^ 2 < 1) : 0 < thirdKindDen h ψ := by
  have hprod : thirdKindDen h ψ * (Real.cos ψ - h * Real.sin ψ)
      = 1 - (1 + h ^ 2) * Real.sin ψ ^ 2 := thirdKindDen_mul_conj h ψ
  have hsum : thirdKindDen h ψ + (Real.cos ψ - h * Real.sin ψ) = 2 * Real.cos ψ := by
    rw [thirdKindDen]; ring
  rcases lt_trichotomy (thirdKindDen h ψ) 0 with hneg | hzero | hpos
  · exfalso
    rcases le_total 0 (Real.cos ψ - h * Real.sin ψ) with hc | hc
    · nlinarith
    · nlinarith
  · exfalso; rw [hzero, zero_mul] at hprod; linarith
  · exact hpos

-- Theorem: the pole condition propagates from the endpoint to the whole arc.
theorem thirdKindPole_of_mem {h Φ : ℝ} (h0 : 0 ≤ Φ) (hlt : Φ < Real.pi / 2)
    (hp : (1 + h ^ 2) * Real.sin Φ ^ 2 < 1) {ψ : ℝ} (hψ : ψ ∈ Set.Icc (0 : ℝ) Φ) :
    (1 + h ^ 2) * Real.sin ψ ^ 2 < 1 := by
  have hpi := Real.pi_pos
  have hs : Real.sin ψ ≤ Real.sin Φ :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [hψ.1]) (by linarith) hψ.2
  have hs0 : 0 ≤ Real.sin ψ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hψ.1 (by linarith [hψ.2])
  have hsq : Real.sin ψ ^ 2 ≤ Real.sin Φ ^ 2 := by nlinarith
  nlinarith [sq_nonneg h]

theorem thirdKindCos_pos {Φ : ℝ} (hlt : Φ < Real.pi / 2) {ψ : ℝ}
    (hψ : ψ ∈ Set.Icc (0 : ℝ) Φ) : 0 < Real.cos ψ :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [hψ.1, Real.pi_pos], by linarith [hψ.2]⟩

theorem strictMonoOn_thirdKindTan {h Φ : ℝ} (hlt : Φ < Real.pi / 2)
    (hp : (1 + h ^ 2) * Real.sin Φ ^ 2 < 1) (h0 : 0 ≤ Φ) :
    StrictMonoOn (thirdKindTan h) (Set.Icc 0 Φ) := by
  have hD : ∀ ψ ∈ Set.Icc (0 : ℝ) Φ, 0 < thirdKindDen h ψ := fun ψ hψ =>
    thirdKindDen_pos (thirdKindCos_pos hlt hψ) (thirdKindPole_of_mem h0 hlt hp hψ)
  refine strictMonoOn_of_deriv_pos (convex_Icc 0 Φ) ?_ ?_
  · exact fun ψ hψ =>
      ((hasDerivAt_thirdKindTan (hD ψ hψ).ne').continuousAt).continuousWithinAt
  · intro ψ hψ
    have hψ' : ψ ∈ Set.Icc (0 : ℝ) Φ := interior_subset hψ
    rw [(hasDerivAt_thirdKindTan (hD ψ hψ').ne').deriv]
    have := hD ψ hψ'
    positivity

-- Theorem: the arc length of the general cubic Bézier, over `[0, Φ]`, is P-constructible.
-- This is the geometric input; everything else in this section is calculus.
theorem arcLength_thirdKind_Pconstructible {c m h Φ : ℝ} (hm : m ^ 2 = 1 - c) (hc : c < 1)
    (hmpos : 0 < m) (hmP : PConstructible m) (hhP : PConstructible h)
    (hΦP : PConstructible Φ) (h0 : 0 < Φ) (hlt : Φ < Real.pi / 2)
    (hp : (1 + h ^ 2) * Real.sin Φ ^ 2 < 1) :
    PConstructible (arcLengthOf (thirdKindTanParam m h) 0 Φ) := by
  have hpi := Real.pi_pos
  have hD : ∀ ψ ∈ Set.Icc (0 : ℝ) Φ, 0 < thirdKindDen h ψ := fun ψ hψ =>
    thirdKindDen_pos (thirdKindCos_pos hlt hψ) (thirdKindPole_of_mem h0.le hlt hp hψ)
  have hsinpos : 0 < Real.sin Φ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith)
  set T := thirdKindTan h Φ with hTdef
  have hTpos : 0 < T := by
    rw [hTdef, thirdKindTan]
    exact div_pos hsinpos (hD Φ ⟨h0.le, le_rfl⟩)
  have hmono := strictMonoOn_thirdKindTan hlt hp h0.le
  have hzero : thirdKindTan h 0 = 0 := by simp [thirdKindTan, thirdKindDen]
  have hrange : ∀ ψ ∈ Set.Icc (0 : ℝ) Φ, thirdKindTan h ψ ∈ Set.Icc (0 : ℝ) T := by
    intro ψ hψ
    constructor
    · rcases eq_or_lt_of_le hψ.1 with h' | h'
      · rw [← h', hzero]
      · rw [← hzero]
        exact (hmono ⟨le_rfl, h0.le⟩ hψ h').le
    · rcases eq_or_lt_of_le hψ.2 with h' | h'
      · rw [h']
      · exact (hmono hψ ⟨h0.le, le_rfl⟩ h').le
  have hTP : PConstructible T := by
    rw [hTdef, thirdKindTan, thirdKindDen]
    pconstructible
  refine PConstructible.arc_length (thirdKindBezier_PConstructibleCurve hmP hhP hTP)
    (thirdKindTanParam m h) h0.le ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rintro p ⟨ψ, hψ, rfl⟩
    obtain ⟨h1, h2⟩ := hrange ψ hψ
    refine ⟨thirdKindTan h ψ / T, ⟨div_nonneg h1 hTpos.le, (div_le_one hTpos).mpr h2⟩, ?_⟩
    rw [bezierParam_thirdKind]
    simp only [thirdKindTanParam]
    congr 1
    field_simp
  · -- injective: the second coordinate is strictly increasing
    have hsnd : StrictMonoOn (fun ψ => (thirdKindTanParam m h ψ).2) (Set.Icc 0 Φ) := by
      refine strictMonoOn_of_deriv_pos (convex_Icc 0 Φ) ?_ ?_
      · exact fun ψ hψ =>
          ((hasDerivAt_thirdKindTanParam_snd (hD ψ hψ).ne').continuousAt).continuousWithinAt
      · intro ψ hψ
        have hψ' : ψ ∈ Set.Icc (0 : ℝ) Φ := interior_subset hψ
        rw [interior_Icc] at hψ
        have hDψ := hD ψ hψ'
        rw [(hasDerivAt_thirdKindTanParam_snd hDψ.ne').deriv,
          one_sub_mul_thirdKindTan hDψ.ne', thirdKindTan]
        have hs : 0 < Real.sin ψ := Real.sin_pos_of_pos_of_lt_pi hψ.1 (by linarith [hψ.2])
        have hcos := thirdKindCos_pos hlt hψ'
        have : 0 < 1 + m := by linarith
        positivity
    exact fun ψ₁ h₁ ψ₂ h₂ heq => hsnd.injOn h₁ h₂ (congrArg Prod.snd heq)
  · intro ψ hψ
    exact ⟨(hasDerivAt_thirdKindTanParam_fst (hD ψ hψ).ne').differentiableAt,
      (hasDerivAt_thirdKindTanParam_snd (hD ψ hψ).ne').differentiableAt⟩
  · refine ContinuousOn.intervalIntegrable (ContinuousOn.congr
      (f := fun ψ => ellipticEIntegrand c ψ / thirdKindDen h ψ ^ 4) ?_ ?_)
    · refine ContinuousOn.div (continuous_ellipticEIntegrand c).continuousOn
        (Continuous.continuousOn (by unfold thirdKindDen; fun_prop)) fun ψ hψ => ?_
      rw [Set.uIcc_of_le h0.le] at hψ
      exact pow_ne_zero 4 (hD ψ hψ).ne'
    · intro ψ hψ
      rw [Set.uIcc_of_le h0.le] at hψ
      exact speed_thirdKindTanParam hm hc (hD ψ hψ).ne'
  · simpa [thirdKindTanParam, thirdKindCurve, hzero] using zero_Pconstructible
  · simpa [thirdKindTanParam, thirdKindCurve, hzero] using zero_Pconstructible
  · have hT2 : PConstructible (T ^ 2) := sq_Pconstructible hTP
    have hT3 : PConstructible (T ^ 3) := by
      convert PConstructible.mul hT2 hTP using 1; ring
    simpa [thirdKindTanParam, thirdKindCurve, ← hTdef] using
      PConstructible.add (PConstructible.sub hTP (PConstructible.mul hhP hT2))
        (PConstructible.div (PConstructible.mul
          (PConstructible.sub (sq_Pconstructible hhP) hmP) hT3) three_Pconstructible)
  · have hT2 : PConstructible (T ^ 2) := sq_Pconstructible hTP
    have hT3 : PConstructible (T ^ 3) := by
      convert PConstructible.mul hT2 hTP using 1; ring
    simpa [thirdKindTanParam, thirdKindCurve, ← hTdef] using
      PConstructible.mul (PConstructible.add PConstructible.base_one hmP)
        (PConstructible.sub (PConstructible.div hT2 two_Pconstructible)
          (PConstructible.div (PConstructible.mul hhP hT3) three_Pconstructible))

theorem thirdKindDen_ne_zero_of_mem {h Φ : ℝ} (h0 : 0 ≤ Φ) (hlt : Φ < Real.pi / 2)
    (hp : (1 + h ^ 2) * Real.sin Φ ^ 2 < 1) {ψ : ℝ} (hψ : ψ ∈ Set.uIcc (0 : ℝ) Φ) :
    thirdKindDen h ψ ≠ 0 := by
  rw [Set.uIcc_of_le h0] at hψ
  exact (thirdKindDen_pos (thirdKindCos_pos hlt hψ) (thirdKindPole_of_mem h0 hlt hp hψ)).ne'

theorem thirdKindPole_ne_zero_of_mem {h Φ : ℝ} (h0 : 0 ≤ Φ) (hlt : Φ < Real.pi / 2)
    (hp : (1 + h ^ 2) * Real.sin Φ ^ 2 < 1) {ψ : ℝ} (hψ : ψ ∈ Set.uIcc (0 : ℝ) Φ) :
    1 - (1 + h ^ 2) * Real.sin ψ ^ 2 ≠ 0 := by
  rw [Set.uIcc_of_le h0] at hψ
  have := thirdKindPole_of_mem h0 hlt hp hψ
  linarith

-- Theorem: the arc length is the `t`-integral of `√Q`, so `integral_sqrt_quartic` applies.
theorem arcLengthOf_thirdKindTanParam {c m h Φ : ℝ} (hm : m ^ 2 = 1 - c) (hc : c < 1)
    (h0 : 0 ≤ Φ) (hlt : Φ < Real.pi / 2) (hp : (1 + h ^ 2) * Real.sin Φ ^ 2 < 1) :
    arcLengthOf (thirdKindTanParam m h) 0 Φ
      = ∫ t in (0 : ℝ)..thirdKindTan h Φ, Real.sqrt (thirdKindQuartic m h t) := by
  have hD : ∀ ψ ∈ Set.uIcc (0 : ℝ) Φ, thirdKindDen h ψ ≠ 0 :=
    fun ψ hψ => thirdKindDen_ne_zero_of_mem h0 hlt hp hψ
  have hgc : Continuous fun t : ℝ => Real.sqrt (thirdKindQuartic m h t) :=
    Real.continuous_sqrt.comp (continuous_thirdKindQuartic m h)
  rw [arcLengthOf, ← integral_comp_thirdKindTan hD
    (g := fun t : ℝ => Real.sqrt (thirdKindQuartic m h t)) hgc]
  refine intervalIntegral.integral_congr fun ψ hψ => ?_
  have hE := ellipticEIntegrand_pos hc ψ
  have hDψ := hD ψ hψ
  rw [speed_thirdKindTanParam hm hc hDψ, sqrt_thirdKindQuartic_tan hm hc hDψ]
  field_simp

/-! #### Symmetrising over `±h`

Replacing `h` by `-h` fixes the quartic's even coefficients and flips the odd ones, so in the
moment reduction `α` and `γ` are unchanged while `β` changes sign. Adding the two arc lengths
therefore cancels the two elementary integrals that would otherwise have to be evaluated,
and leaves `Π` with the coefficient below. It vanishes only when `h = 0` (the old family),
`h⁴ = m²`, or `m² = 1` (that is, `c = 0`). -/

/-- The quartic's coefficients, in the order `integral_sqrt_quartic` wants them. -/
noncomputable def thirdKindQ4 (m h : ℝ) : ℝ := (h ^ 2 + 1) * (h ^ 2 + m ^ 2)
noncomputable def thirdKindQ3 (m h : ℝ) : ℝ := -2 * h * (2 * h ^ 2 + 1 + m ^ 2)
noncomputable def thirdKindQ2 (m h : ℝ) : ℝ := 6 * h ^ 2 + 1 + m ^ 2
noncomputable def thirdKindQ1 (h : ℝ) : ℝ := -4 * h

theorem thirdKindQuartic_eq_quartic (m h t : ℝ) :
    thirdKindQuartic m h t
      = quartic (thirdKindQ4 m h) (thirdKindQ3 m h) (thirdKindQ2 m h) (thirdKindQ1 h) 1 t := by
  unfold thirdKindQuartic quartic thirdKindQ4 thirdKindQ3 thirdKindQ2 thirdKindQ1
  ring

/-- The coefficient with which `Π` survives the symmetrisation. -/
noncomputable def thirdKindPiCoeff (m h : ℝ) : ℝ :=
  h ^ 2 * (h ^ 4 - m ^ 2) * (m ^ 2 - 1) ^ 2 / ((h ^ 2 + 1) ^ 2 * (h ^ 2 + m ^ 2) ^ 2)

-- Theorem: the coefficient, computed. `α` drops out, `β` enters with a factor `-2h` from
-- the sign flip, and `γ` enters through the reduction of the squared-denominator moment.
theorem thirdKindPiCoeff_eq {m h : ℝ} (hQ4 : thirdKindQ4 m h ≠ 0) :
    -2 * h * (thirdKindQ1 h / 2
        - thirdKindQ3 m h * thirdKindQ2 m h / (12 * thirdKindQ4 m h))
      + 2 * (thirdKindQ2 m h / 3 - thirdKindQ3 m h ^ 2 / (8 * thirdKindQ4 m h))
        * (1 - thirdKindCubicDeriv (1 - m ^ 2) (1 + h ^ 2) / thirdKindQ4 m h)
      = thirdKindPiCoeff m h := by
  rw [thirdKindQ4] at hQ4
  unfold thirdKindQ4 thirdKindQ3 thirdKindQ2 thirdKindQ1 thirdKindCubicDeriv thirdKindPiCoeff
  have h1 : (h ^ 2 + 1) ≠ 0 := by positivity
  have h2 : (h ^ 2 + m ^ 2) ≠ 0 := fun h0 => hQ4 (by rw [h0, mul_zero])
  field_simp
  ring

/-- The three moment coefficients of `integral_sqrt_quartic`, for this quartic. -/
noncomputable def thirdKindAlpha (m h : ℝ) : ℝ :=
  2 / 3 - thirdKindQ3 m h * thirdKindQ1 h / (24 * thirdKindQ4 m h)
noncomputable def thirdKindBeta (m h : ℝ) : ℝ :=
  thirdKindQ1 h / 2 - thirdKindQ3 m h * thirdKindQ2 m h / (12 * thirdKindQ4 m h)
noncomputable def thirdKindGamma (m h : ℝ) : ℝ :=
  thirdKindQ2 m h / 3 - thirdKindQ3 m h ^ 2 / (8 * thirdKindQ4 m h)

theorem thirdKindQ4_pos {m : ℝ} (hm0 : m ≠ 0) (h : ℝ) : 0 < thirdKindQ4 m h := by
  rw [thirdKindQ4]; positivity

theorem thirdKindQ4_neg (m h : ℝ) : thirdKindQ4 m (-h) = thirdKindQ4 m h := by
  unfold thirdKindQ4; ring
theorem thirdKindQ3_neg (m h : ℝ) : thirdKindQ3 m (-h) = -thirdKindQ3 m h := by
  unfold thirdKindQ3; ring
theorem thirdKindQ2_neg (m h : ℝ) : thirdKindQ2 m (-h) = thirdKindQ2 m h := by
  unfold thirdKindQ2; ring
theorem thirdKindQ1_neg (h : ℝ) : thirdKindQ1 (-h) = -thirdKindQ1 h := by
  unfold thirdKindQ1; ring
theorem thirdKindAlpha_neg (m h : ℝ) : thirdKindAlpha m (-h) = thirdKindAlpha m h := by
  unfold thirdKindAlpha; rw [thirdKindQ4_neg, thirdKindQ3_neg, thirdKindQ1_neg]; ring
theorem thirdKindBeta_neg (m h : ℝ) : thirdKindBeta m (-h) = -thirdKindBeta m h := by
  unfold thirdKindBeta
  rw [thirdKindQ4_neg, thirdKindQ3_neg, thirdKindQ2_neg, thirdKindQ1_neg]; ring
theorem thirdKindGamma_neg (m h : ℝ) : thirdKindGamma m (-h) = thirdKindGamma m h := by
  unfold thirdKindGamma; rw [thirdKindQ4_neg, thirdKindQ3_neg, thirdKindQ2_neg]; ring

-- Theorem: the arc length, with the moment reduction applied and pulled back to the angle.
-- The `1/D²` from the substitution cancels the `D²` in `√Q`, so the integrand is simply the
-- moment polynomial over `Δ(ψ)`.
theorem arcLength_thirdKind_pullback {c m h Φ : ℝ} (hm : m ^ 2 = 1 - c) (hc : c < 1)
    (hm0 : m ≠ 0) (h0 : 0 ≤ Φ) (hlt : Φ < Real.pi / 2)
    (hp : (1 + h ^ 2) * Real.sin Φ ^ 2 < 1) :
    arcLengthOf (thirdKindTanParam m h) 0 Φ
      = (quarticArcAnti (thirdKindQ4 m h) (thirdKindQ3 m h) (thirdKindQ2 m h)
            (thirdKindQ1 h) 1 (thirdKindTan h Φ)
          - quarticArcAnti (thirdKindQ4 m h) (thirdKindQ3 m h) (thirdKindQ2 m h)
            (thirdKindQ1 h) 1 0)
        + ∫ ψ in (0 : ℝ)..Φ, (thirdKindAlpha m h + thirdKindBeta m h * thirdKindTan h ψ
            + thirdKindGamma m h * thirdKindTan h ψ ^ 2) / ellipticEIntegrand c ψ := by
  have hQ4 := (thirdKindQ4_pos hm0 h).ne'
  have hpos : ∀ s : ℝ, 0 < quartic (thirdKindQ4 m h) (thirdKindQ3 m h) (thirdKindQ2 m h)
      (thirdKindQ1 h) 1 s := by
    intro s
    rw [← thirdKindQuartic_eq_quartic]
    exact thirdKindQuartic_pos hm0 h s
  have hD : ∀ ψ ∈ Set.uIcc (0 : ℝ) Φ, thirdKindDen h ψ ≠ 0 :=
    fun ψ hψ => thirdKindDen_ne_zero_of_mem h0 hlt hp hψ
  rw [arcLengthOf_thirdKindTanParam hm hc h0 hlt hp]
  have hq : ∀ t : ℝ, Real.sqrt (thirdKindQuartic m h t)
      = Real.sqrt (quartic (thirdKindQ4 m h) (thirdKindQ3 m h) (thirdKindQ2 m h)
          (thirdKindQ1 h) 1 t) := fun t => by rw [thirdKindQuartic_eq_quartic]
  simp only [hq]
  rw [integral_sqrt_quartic hQ4 hpos]
  congr 1
  set A0 : ℝ := 2 * 1 / 3 - thirdKindQ3 m h * thirdKindQ1 h / (24 * thirdKindQ4 m h) with hA0
  set A1 : ℝ := thirdKindQ1 h / 2
    - thirdKindQ3 m h * thirdKindQ2 m h / (12 * thirdKindQ4 m h) with hA1
  set A2 : ℝ := thirdKindQ2 m h / 3
    - thirdKindQ3 m h ^ 2 / (8 * thirdKindQ4 m h) with hA2
  have hgc : Continuous fun t : ℝ => (A0 + A1 * t + A2 * t ^ 2)
      / Real.sqrt (quartic (thirdKindQ4 m h) (thirdKindQ3 m h) (thirdKindQ2 m h)
        (thirdKindQ1 h) 1 t) := by
    refine Continuous.div (by fun_prop) ?_ fun t => (Real.sqrt_pos.mpr (hpos t)).ne'
    exact Real.continuous_sqrt.comp (by unfold quartic; fun_prop)
  rw [← integral_comp_thirdKindTan hD (g := fun t : ℝ => (A0 + A1 * t + A2 * t ^ 2)
    / Real.sqrt (quartic (thirdKindQ4 m h) (thirdKindQ3 m h) (thirdKindQ2 m h)
      (thirdKindQ1 h) 1 t)) hgc]
  refine intervalIntegral.integral_congr fun ψ hψ => ?_
  have hE := ellipticEIntegrand_pos hc ψ
  have hDψ := hD ψ hψ
  have hAlpha : thirdKindAlpha m h = A0 := by rw [thirdKindAlpha, hA0]; ring
  have hBeta : thirdKindBeta m h = A1 := by rw [thirdKindBeta, hA1]
  have hGamma : thirdKindGamma m h = A2 := by rw [thirdKindGamma, hA2]
  rw [hAlpha, hBeta, hGamma, ← thirdKindQuartic_eq_quartic,
    sqrt_thirdKindQuartic_tan hm hc hDψ]
  field_simp

theorem thirdKindCubic_eq (m h : ℝ) :
    thirdKindCubic (1 - m ^ 2) (1 + h ^ 2) = h ^ 2 * thirdKindQ4 m h := by
  unfold thirdKindCubic thirdKindQ4; ring

theorem thirdKind_tan_diff_alg {S p q u hh : ℝ} (hp : p ≠ 0) (hq : q ≠ 0)
    (hpq : p * q = u) (hqp : q - p = -2 * hh * S) :
    S / p - S / q = -2 * hh * S ^ 2 / u := by
  subst hpq
  field_simp
  linear_combination S * hqp

theorem thirdKind_tan_sq_alg {S p q u hh : ℝ} (hp : p ≠ 0) (hq : q ≠ 0)
    (hpq : p * q = u) (hqp : q - p = -2 * hh * S) :
    (S / p) ^ 2 + (S / q) ^ 2 = 2 * S ^ 2 / u + 4 * hh ^ 2 * S ^ 4 / u ^ 2 := by
  subst hpq
  field_simp
  linear_combination (S ^ 2 * (q - p - 2 * hh * S)) * hqp

theorem thirdKind_sum_alg {S u E A B G Q4 Pd hpar tp tm : ℝ}
    (hu : u ≠ 0) (hE : E ≠ 0) (hQ4 : Q4 ≠ 0)
    (hdiff : tp - tm = -2 * hpar * S ^ 2 / u)
    (hsum : tp ^ 2 + tm ^ 2 = 2 * S ^ 2 / u + 4 * hpar ^ 2 * S ^ 4 / u ^ 2) :
    (A + B * tp + G * tp ^ 2) / E + (A + -B * tm + G * tm ^ 2) / E
      = 2 * A * E⁻¹
        + (-2 * hpar * B + 2 * G * (1 - Pd / Q4)) * (S ^ 2 / (u * E))
        + 2 * G / Q4 * (Pd * S ^ 2 / (u * E)
            + 2 * (hpar ^ 2 * Q4) * S ^ 4 / (u ^ 2 * E)) := by
  have key : (A + B * tp + G * tp ^ 2) / E + (A + -B * tm + G * tm ^ 2) / E
      = (2 * A + B * (tp - tm) + G * (tp ^ 2 + tm ^ 2)) / E := by ring
  rw [key, hdiff, hsum]
  field_simp
  ring

-- Theorem: the pointwise identity behind the symmetrisation. Adding the two integrands (for
-- `h` and `-h`) kills the odd part, and what is left is a combination of the first-kind
-- integrand, the auxiliary integrand `A`, and the master integrand.
theorem thirdKind_sum_integrand {c m h : ℝ} (hm : m ^ 2 = 1 - c) (hc : c < 1) (hm0 : m ≠ 0)
    {ψ : ℝ} (hDh : thirdKindDen h ψ ≠ 0) (hDm : thirdKindDen (-h) ψ ≠ 0)
    (hu : 1 - (1 + h ^ 2) * Real.sin ψ ^ 2 ≠ 0) :
    (thirdKindAlpha m h + thirdKindBeta m h * thirdKindTan h ψ
        + thirdKindGamma m h * thirdKindTan h ψ ^ 2) / ellipticEIntegrand c ψ
      + (thirdKindAlpha m (-h) + thirdKindBeta m (-h) * thirdKindTan (-h) ψ
        + thirdKindGamma m (-h) * thirdKindTan (-h) ψ ^ 2) / ellipticEIntegrand c ψ
      = 2 * thirdKindAlpha m h * ellipticFIntegrand c ψ
        + thirdKindPiCoeff m h * (Real.sin ψ ^ 2
            / ((1 - (1 + h ^ 2) * Real.sin ψ ^ 2) * ellipticEIntegrand c ψ))
        + 2 * thirdKindGamma m h / thirdKindQ4 m h
            * thirdKindMaster c (1 + h ^ 2) ψ := by
  have hcm : c = 1 - m ^ 2 := by linarith
  subst hcm
  have hE := (ellipticEIntegrand_pos hc ψ).ne'
  have hQ4 := (thirdKindQ4_pos hm0 h).ne'
  have hDh' : Real.cos ψ + h * Real.sin ψ ≠ 0 := by rw [thirdKindDen] at hDh; exact hDh
  have hDm' : Real.cos ψ - h * Real.sin ψ ≠ 0 := by
    rw [thirdKindDen] at hDm; intro h0; exact hDm (by linarith)
  have hfac : (Real.cos ψ + h * Real.sin ψ) * (Real.cos ψ - h * Real.sin ψ)
      = 1 - (1 + h ^ 2) * Real.sin ψ ^ 2 := by
    linear_combination Real.sin_sq_add_cos_sq ψ
  have hqp : (Real.cos ψ - h * Real.sin ψ) - (Real.cos ψ + h * Real.sin ψ)
      = -2 * h * Real.sin ψ := by ring
  have htp : thirdKindTan h ψ = Real.sin ψ / (Real.cos ψ + h * Real.sin ψ) := by
    rw [thirdKindTan, thirdKindDen]
  have htq : thirdKindTan (-h) ψ = Real.sin ψ / (Real.cos ψ - h * Real.sin ψ) := by
    rw [thirdKindTan, thirdKindDen]; ring_nf
  have hdiff : thirdKindTan h ψ - thirdKindTan (-h) ψ
      = -2 * h * Real.sin ψ ^ 2 / (1 - (1 + h ^ 2) * Real.sin ψ ^ 2) := by
    rw [htp, htq]
    exact thirdKind_tan_diff_alg hDh' hDm' hfac hqp
  have hsum : thirdKindTan h ψ ^ 2 + thirdKindTan (-h) ψ ^ 2
      = 2 * Real.sin ψ ^ 2 / (1 - (1 + h ^ 2) * Real.sin ψ ^ 2)
        + 4 * h ^ 2 * Real.sin ψ ^ 4 / (1 - (1 + h ^ 2) * Real.sin ψ ^ 2) ^ 2 := by
    rw [htp, htq]
    exact thirdKind_tan_sq_alg hDh' hDm' hfac hqp
  rw [thirdKindAlpha_neg, thirdKindBeta_neg, thirdKindGamma_neg,
    ← thirdKindPiCoeff_eq hQ4, thirdKindMaster, thirdKindCubic_eq, ellipticFIntegrand]
  unfold thirdKindBeta thirdKindGamma
  exact thirdKind_sum_alg hu hE hQ4 hdiff hsum

-- Theorem: **the symmetrised arc length.** Adding the arc lengths of the Béziers for `h`
-- and `-h` gives an algebraic term, a multiple of `F`, a multiple of `Π`'s auxiliary
-- integral, and a multiple of the master identity's right-hand side. Everything but the
-- `Π` term is already known to be P-constructible.
theorem thirdKind_sum_key {c m h Φ : ℝ} (hm : m ^ 2 = 1 - c) (hc : c < 1) (hm0 : m ≠ 0)
    (h0 : 0 ≤ Φ) (hlt : Φ < Real.pi / 2) (hp : (1 + h ^ 2) * Real.sin Φ ^ 2 < 1) :
    arcLengthOf (thirdKindTanParam m h) 0 Φ + arcLengthOf (thirdKindTanParam m (-h)) 0 Φ
      = ((quarticArcAnti (thirdKindQ4 m h) (thirdKindQ3 m h) (thirdKindQ2 m h)
              (thirdKindQ1 h) 1 (thirdKindTan h Φ)
            - quarticArcAnti (thirdKindQ4 m h) (thirdKindQ3 m h) (thirdKindQ2 m h)
              (thirdKindQ1 h) 1 0)
          + (quarticArcAnti (thirdKindQ4 m (-h)) (thirdKindQ3 m (-h)) (thirdKindQ2 m (-h))
              (thirdKindQ1 (-h)) 1 (thirdKindTan (-h) Φ)
            - quarticArcAnti (thirdKindQ4 m (-h)) (thirdKindQ3 m (-h)) (thirdKindQ2 m (-h))
              (thirdKindQ1 (-h)) 1 0))
        + (2 * thirdKindAlpha m h * ellipticF c Φ
          + thirdKindPiCoeff m h * ellipticPiAux c (1 + h ^ 2) Φ
          + 2 * thirdKindGamma m h / thirdKindQ4 m h
            * ((1 - (1 + h ^ 2)) * ellipticF c Φ - ellipticE c Φ
              + thirdKindAnti c (1 + h ^ 2) Φ)) := by
  have hpn : (1 + (-h) ^ 2) * Real.sin Φ ^ 2 < 1 := by
    rw [show (-h) ^ 2 = h ^ 2 from by ring]; exact hp
  have hne : ∀ ψ ∈ Set.uIcc (0 : ℝ) Φ, 1 - (1 + h ^ 2) * Real.sin ψ ^ 2 ≠ 0 :=
    fun ψ hψ => thirdKindPole_ne_zero_of_mem h0 hlt hp hψ
  have hDh : ∀ ψ ∈ Set.uIcc (0 : ℝ) Φ, thirdKindDen h ψ ≠ 0 :=
    fun ψ hψ => thirdKindDen_ne_zero_of_mem h0 hlt hp hψ
  have hDm : ∀ ψ ∈ Set.uIcc (0 : ℝ) Φ, thirdKindDen (-h) ψ ≠ 0 :=
    fun ψ hψ => thirdKindDen_ne_zero_of_mem h0 hlt hpn hψ
  have hEne : ∀ ψ : ℝ, ellipticEIntegrand c ψ ≠ 0 :=
    fun ψ => (ellipticEIntegrand_pos hc ψ).ne'
  have hmom : ∀ k : ℝ, (∀ ψ ∈ Set.uIcc (0 : ℝ) Φ, thirdKindDen k ψ ≠ 0) →
      ContinuousOn (fun ψ => (thirdKindAlpha m k + thirdKindBeta m k * thirdKindTan k ψ
        + thirdKindGamma m k * thirdKindTan k ψ ^ 2) / ellipticEIntegrand c ψ)
        (Set.uIcc (0 : ℝ) Φ) := by
    intro k hk
    have ht : ContinuousOn (thirdKindTan k) (Set.uIcc (0 : ℝ) Φ) :=
      fun ψ hψ => ((hasDerivAt_thirdKindTan (hk ψ hψ)).continuousAt).continuousWithinAt
    exact ((continuousOn_const.add (continuousOn_const.mul ht)).add
      (continuousOn_const.mul (ht.pow 2))).div
      (continuous_ellipticEIntegrand c).continuousOn fun ψ _ => hEne ψ
  have hauxc : ContinuousOn (fun ψ : ℝ => Real.sin ψ ^ 2
      / ((1 - (1 + h ^ 2) * Real.sin ψ ^ 2) * ellipticEIntegrand c ψ))
      (Set.uIcc (0 : ℝ) Φ) :=
    (Continuous.continuousOn (by fun_prop)).div
      ((Continuous.continuousOn (by fun_prop)).mul
        (continuous_ellipticEIntegrand c).continuousOn)
      fun ψ hψ => mul_ne_zero (hne ψ hψ) (hEne ψ)
  have hmasterc : ContinuousOn (thirdKindMaster c (1 + h ^ 2)) (Set.uIcc (0 : ℝ) Φ) :=
    continuousOn_thirdKindMaster hc hne
  rw [arcLength_thirdKind_pullback hm hc hm0 h0 hlt hp,
    arcLength_thirdKind_pullback hm hc hm0 h0 hlt hpn]
  rw [show ∀ a b x y : ℝ, a + x + (b + y) = a + b + (x + y) from fun a b x y => by ring]
  congr 1
  rw [← intervalIntegral.integral_add ((hmom h hDh).intervalIntegrable)
    ((hmom (-h) hDm).intervalIntegrable)]
  rw [intervalIntegral.integral_congr (g := fun ψ =>
      2 * thirdKindAlpha m h * ellipticFIntegrand c ψ
        + thirdKindPiCoeff m h * (Real.sin ψ ^ 2
            / ((1 - (1 + h ^ 2) * Real.sin ψ ^ 2) * ellipticEIntegrand c ψ))
        + 2 * thirdKindGamma m h / thirdKindQ4 m h * thirdKindMaster c (1 + h ^ 2) ψ)
    fun ψ hψ => thirdKind_sum_integrand hm hc hm0 (hDh ψ hψ) (hDm ψ hψ) (hne ψ hψ)]
  rw [intervalIntegral.integral_add
      (((continuous_ellipticFIntegrand hc).const_mul _).intervalIntegrable _ _ |>.add
        ((hauxc.const_smul (thirdKindPiCoeff m h)).intervalIntegrable.congr
          (fun ψ _ => by simp [smul_eq_mul])))
      ((hmasterc.const_smul (2 * thirdKindGamma m h / thirdKindQ4 m h)).intervalIntegrable.congr
        (fun ψ _ => by simp [smul_eq_mul])),
    intervalIntegral.integral_add
      (((continuous_ellipticFIntegrand hc).const_mul _).intervalIntegrable _ _)
      ((hauxc.const_smul (thirdKindPiCoeff m h)).intervalIntegrable.congr
        (fun ψ _ => by simp [smul_eq_mul])),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, ← ellipticF, ← ellipticPiAux,
    integral_thirdKindMaster hc Φ hne]

/-! #### P-constructibility of the pieces -/

theorem twelve_Pconstructible : PConstructible (12 : ℝ) := by
  have h := nat_Pconstructible 12
  norm_num at h
  exact h

@[pconstructible]
theorem quarticArcAnti_Pconstructible {q4 q3 q2 q1 q0 t : ℝ}
    (h4 : PConstructible q4) (h3 : PConstructible q3) (h2 : PConstructible q2)
    (h1 : PConstructible q1) (h0 : PConstructible q0) (ht : PConstructible t) :
    PConstructible (quarticArcAnti q4 q3 q2 q1 q0 t) := by
  unfold quarticArcAnti quartic
  refine PConstructible.mul (PConstructible.add
    (PConstructible.div h3 (PConstructible.mul twelve_Pconstructible h4))
    (PConstructible.div ht three_Pconstructible)) (sqrt_Pconstructible ?_)
  pconstructible

theorem thirdKindQs_Pconstructible {m h : ℝ} (hmP : PConstructible m)
    (hhP : PConstructible h) :
    PConstructible (thirdKindQ4 m h) ∧ PConstructible (thirdKindQ3 m h)
      ∧ PConstructible (thirdKindQ2 m h) ∧ PConstructible (thirdKindQ1 h) := by
  have h2 := sq_Pconstructible hhP
  have hm2 := sq_Pconstructible hmP
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact PConstructible.mul (PConstructible.add h2 PConstructible.base_one)
      (PConstructible.add h2 hm2)
  · exact PConstructible.mul (PConstructible.mul (neg_Pconstructible two_Pconstructible) hhP)
      (PConstructible.add (PConstructible.add
        (PConstructible.mul two_Pconstructible h2) PConstructible.base_one) hm2)
  · exact PConstructible.add (PConstructible.add
      (PConstructible.mul (nat_six) h2) PConstructible.base_one) hm2
  · exact PConstructible.mul (neg_Pconstructible (nat_four)) hhP
where
  nat_six : PConstructible (6 : ℝ) := by
    have h := nat_Pconstructible 6; norm_num at h; exact h
  nat_four : PConstructible (4 : ℝ) := by
    have h := nat_Pconstructible 4; norm_num at h; exact h

@[pconstructible]
theorem thirdKindTan_Pconstructible {h Φ : ℝ} (hhP : PConstructible h)
    (hΦP : PConstructible Φ) : PConstructible (thirdKindTan h Φ) := by
  rw [thirdKindTan, thirdKindDen]
  pconstructible

@[pconstructible]
theorem thirdKindAnti_Pconstructible {c n Φ : ℝ} (hcP : PConstructible c)
    (hnP : PConstructible n) (hΦP : PConstructible Φ) :
    PConstructible (thirdKindAnti c n Φ) := by
  rw [thirdKindAnti]
  pconstructible

theorem eight_Pconstructible : PConstructible (8 : ℝ) := by
  have h := nat_Pconstructible 8; norm_num at h; exact h
theorem twentyfour_Pconstructible : PConstructible (24 : ℝ) := by
  have h := nat_Pconstructible 24; norm_num at h; exact h

@[pconstructible]
theorem thirdKindAlpha_Pconstructible {m h : ℝ} (hmP : PConstructible m)
    (hhP : PConstructible h) : PConstructible (thirdKindAlpha m h) := by
  obtain ⟨h4, h3, h2, h1⟩ := thirdKindQs_Pconstructible hmP hhP
  rw [thirdKindAlpha]
  pconstructible

@[pconstructible]
theorem thirdKindGamma_Pconstructible {m h : ℝ} (hmP : PConstructible m)
    (hhP : PConstructible h) : PConstructible (thirdKindGamma m h) := by
  obtain ⟨h4, h3, h2, h1⟩ := thirdKindQs_Pconstructible hmP hhP
  rw [thirdKindGamma]
  pconstructible

@[pconstructible]
theorem thirdKindPiCoeff_Pconstructible {m h : ℝ} (hmP : PConstructible m)
    (hhP : PConstructible h) : PConstructible (thirdKindPiCoeff m h) := by
  have h2 := sq_Pconstructible hhP
  have hm2 := sq_Pconstructible hmP
  have h4 : PConstructible (h ^ 4) := pow_Pconstructible hhP 4
  rw [thirdKindPiCoeff]
  pconstructible

theorem thirdKindPiCoeff_ne_zero {m h : ℝ} (hm0 : m ≠ 0) (hh0 : h ≠ 0)
    (hne4 : h ^ 4 ≠ m ^ 2) (hm1 : m ^ 2 ≠ 1) : thirdKindPiCoeff m h ≠ 0 := by
  have hpos : (0 : ℝ) < h ^ 2 + m ^ 2 := by positivity
  rw [thirdKindPiCoeff]
  refine div_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hh0)
    (sub_ne_zero.mpr hne4)) (pow_ne_zero 2 (sub_ne_zero.mpr hm1))) ?_
  exact mul_ne_zero (pow_ne_zero 2 (by positivity)) (pow_ne_zero 2 hpos.ne')

/-! ### The incomplete third kind, for `n > 1`

Solving the symmetrised identity for the auxiliary integral. Every other term in it is
P-constructible — two Bézier arc lengths, an algebraic term, `F`, `E`, and the elementary
boundary term of the master identity — so the auxiliary integral is, and with it `Π`. -/

theorem ellipticPiAux_Pconstructible_gt_one {c m h Φ : ℝ}
    (hm : m ^ 2 = 1 - c) (hc : c < 1) (hc0 : 0 < c) (hmpos : 0 < m)
    (hcP : PConstructible c) (hmP : PConstructible m) (hhP : PConstructible h)
    (hΦP : PConstructible Φ) (h0 : 0 < Φ) (hlt : Φ < Real.pi / 2)
    (hp : (1 + h ^ 2) * Real.sin Φ ^ 2 < 1) (hh0 : h ≠ 0) (hne4 : h ^ 4 ≠ m ^ 2) :
    PConstructible (ellipticPiAux c (1 + h ^ 2) Φ) := by
  have hm0 : m ≠ 0 := hmpos.ne'
  have hm1 : m ^ 2 ≠ 1 := by rw [hm]; intro hx; linarith
  have hcoeff := thirdKindPiCoeff_ne_zero hm0 hh0 hne4 hm1
  have hcoeffP := thirdKindPiCoeff_Pconstructible hmP hhP
  have hpn : (1 + (-h) ^ 2) * Real.sin Φ ^ 2 < 1 := by
    rw [show (-h) ^ 2 = h ^ 2 from by ring]; exact hp
  have hkey := thirdKind_sum_key hm hc hm0 h0.le hlt hp
  obtain ⟨hQ4, hQ3, hQ2, hQ1⟩ := thirdKindQs_Pconstructible hmP hhP
  obtain ⟨hQ4', hQ3', hQ2', hQ1'⟩ := thirdKindQs_Pconstructible hmP (neg_Pconstructible hhP)
  have hnP : PConstructible (1 + h ^ 2) :=
    PConstructible.add PConstructible.base_one (sq_Pconstructible hhP)
  have hFP : PConstructible (ellipticF c Φ) := ellipticF_Pconstructible hcP hΦP hc
  have hEP : PConstructible (ellipticE c Φ) := ellipticE_Pconstructible hcP hΦP hc
  have hArc : PConstructible (arcLengthOf (thirdKindTanParam m h) 0 Φ) :=
    arcLength_thirdKind_Pconstructible hm hc hmpos hmP hhP hΦP h0 hlt hp
  have hArc' : PConstructible (arcLengthOf (thirdKindTanParam m (-h)) 0 Φ) :=
    arcLength_thirdKind_Pconstructible hm hc hmpos hmP (neg_Pconstructible hhP) hΦP h0 hlt hpn
  have hone : PConstructible (1 : ℝ) := PConstructible.base_one
  have hzero : PConstructible (0 : ℝ) := zero_Pconstructible
  have hRHS : PConstructible
      ((arcLengthOf (thirdKindTanParam m h) 0 Φ
          + arcLengthOf (thirdKindTanParam m (-h)) 0 Φ)
        - ((quarticArcAnti (thirdKindQ4 m h) (thirdKindQ3 m h) (thirdKindQ2 m h)
              (thirdKindQ1 h) 1 (thirdKindTan h Φ)
            - quarticArcAnti (thirdKindQ4 m h) (thirdKindQ3 m h) (thirdKindQ2 m h)
              (thirdKindQ1 h) 1 0)
          + (quarticArcAnti (thirdKindQ4 m (-h)) (thirdKindQ3 m (-h)) (thirdKindQ2 m (-h))
              (thirdKindQ1 (-h)) 1 (thirdKindTan (-h) Φ)
            - quarticArcAnti (thirdKindQ4 m (-h)) (thirdKindQ3 m (-h)) (thirdKindQ2 m (-h))
              (thirdKindQ1 (-h)) 1 0))
        - 2 * thirdKindAlpha m h * ellipticF c Φ
        - 2 * thirdKindGamma m h / thirdKindQ4 m h
          * ((1 - (1 + h ^ 2)) * ellipticF c Φ - ellipticE c Φ
            + thirdKindAnti c (1 + h ^ 2) Φ)) := by
    refine PConstructible.sub (PConstructible.sub (PConstructible.sub
      (PConstructible.add hArc hArc') (PConstructible.add
        (PConstructible.sub
          (quarticArcAnti_Pconstructible hQ4 hQ3 hQ2 hQ1 hone
            (thirdKindTan_Pconstructible hhP hΦP))
          (quarticArcAnti_Pconstructible hQ4 hQ3 hQ2 hQ1 hone hzero))
        (PConstructible.sub
          (quarticArcAnti_Pconstructible hQ4' hQ3' hQ2' hQ1' hone
            (thirdKindTan_Pconstructible (neg_Pconstructible hhP) hΦP))
          (quarticArcAnti_Pconstructible hQ4' hQ3' hQ2' hQ1' hone hzero))))
      (PConstructible.mul (PConstructible.mul two_Pconstructible
        (thirdKindAlpha_Pconstructible hmP hhP)) hFP)) ?_
    pconstructible
  have heq : thirdKindPiCoeff m h * ellipticPiAux c (1 + h ^ 2) Φ
      = (arcLengthOf (thirdKindTanParam m h) 0 Φ
          + arcLengthOf (thirdKindTanParam m (-h)) 0 Φ)
        - ((quarticArcAnti (thirdKindQ4 m h) (thirdKindQ3 m h) (thirdKindQ2 m h)
              (thirdKindQ1 h) 1 (thirdKindTan h Φ)
            - quarticArcAnti (thirdKindQ4 m h) (thirdKindQ3 m h) (thirdKindQ2 m h)
              (thirdKindQ1 h) 1 0)
          + (quarticArcAnti (thirdKindQ4 m (-h)) (thirdKindQ3 m (-h)) (thirdKindQ2 m (-h))
              (thirdKindQ1 (-h)) 1 (thirdKindTan (-h) Φ)
            - quarticArcAnti (thirdKindQ4 m (-h)) (thirdKindQ3 m (-h)) (thirdKindQ2 m (-h))
              (thirdKindQ1 (-h)) 1 0))
        - 2 * thirdKindAlpha m h * ellipticF c Φ
        - 2 * thirdKindGamma m h / thirdKindQ4 m h
          * ((1 - (1 + h ^ 2)) * ellipticF c Φ - ellipticE c Φ
            + thirdKindAnti c (1 + h ^ 2) Φ) := by
    linear_combination -hkey
  have hdiv := PConstructible.div (heq ▸ hRHS) hcoeffP
  rwa [mul_div_cancel_left₀ _ hcoeff] at hdiv

theorem continuousOn_ellipticPiAuxIntegrand {c n : ℝ} (hc : c < 1) {s : Set ℝ}
    (hne : ∀ θ ∈ s, 1 - n * Real.sin θ ^ 2 ≠ 0) :
    ContinuousOn (fun θ : ℝ =>
      Real.sin θ ^ 2 / ((1 - n * Real.sin θ ^ 2) * ellipticEIntegrand c θ)) s :=
  (Continuous.continuousOn (by fun_prop)).div
    ((Continuous.continuousOn (by fun_prop)).mul
      (continuous_ellipticEIntegrand c).continuousOn)
    fun θ hθ => mul_ne_zero (hne θ hθ) (ellipticEIntegrand_pos hc θ).ne'

-- Theorem: `Π = F + n·A` on any interval avoiding the pole, so the restriction `n < 1` of
-- `ellipticPiInc_eq_aux` was only ever about integrability.
theorem ellipticPiInc_eq_aux_of_ne {c n φ : ℝ} (hc : c < 1)
    (hne : ∀ θ ∈ Set.uIcc (0 : ℝ) φ, 1 - n * Real.sin θ ^ 2 ≠ 0) :
    ellipticPiInc c n φ = ellipticF c φ + n * ellipticPiAux c n φ := by
  have hpt : ∀ θ ∈ Set.uIcc (0 : ℝ) φ, ellipticPiIntegrand c n θ
      = ellipticFIntegrand c θ
        + n * (Real.sin θ ^ 2 / ((1 - n * Real.sin θ ^ 2) * ellipticEIntegrand c θ)) := by
    intro θ hθ
    have h1 := hne θ hθ
    have h2 := (ellipticEIntegrand_pos hc θ).ne'
    simp only [ellipticPiIntegrand, ellipticFIntegrand]
    field_simp
    ring
  unfold ellipticPiInc ellipticF ellipticPiAux
  rw [← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add ((continuous_ellipticFIntegrand hc).intervalIntegrable _ _)
      (((continuousOn_ellipticPiAuxIntegrand hc hne).const_smul n).intervalIntegrable.congr
        (fun ψ _ => by simp [smul_eq_mul]))]
  exact intervalIntegral.integral_congr hpt

/-! ### The headline

For a genuine modulus `0 < c < 1` and a characteristic `n > 1`, the incomplete elliptic
integral of the third kind is P-constructible, on the whole of its natural domain — up to
the exceptional locus `(n - 1)² = 1 - c`, where the two Legendre reductions of the Bézier
coincide and the coefficient with which `Π` survives the symmetrisation vanishes. -/

-- Theorem: **the incomplete elliptic integral of the third kind is P-constructible for
-- `n > 1`.** The upper limit ranges over the whole interval on which the integral converges,
-- namely up to the pole at `sin Φ = 1/√n`.
theorem ellipticPiInc_Pconstructible_gt_one {c n Φ : ℝ}
    (hcP : PConstructible c) (hnP : PConstructible n) (hΦP : PConstructible Φ)
    (hc0 : 0 < c) (hc : c < 1) (hn : 1 < n) (h0 : 0 < Φ) (hlt : Φ < Real.pi / 2)
    (hp : n * Real.sin Φ ^ 2 < 1) (hgen : (n - 1) ^ 2 ≠ 1 - c) :
    PConstructible (ellipticPiInc c n Φ) := by
  set h := Real.sqrt (n - 1) with hhdef
  set m := Real.sqrt (1 - c) with hmdef
  have hh2 : h ^ 2 = n - 1 := Real.sq_sqrt (by linarith)
  have hm2 : m ^ 2 = 1 - c := Real.sq_sqrt (by linarith)
  have hn' : (1 : ℝ) + h ^ 2 = n := by rw [hh2]; ring
  have hmpos : 0 < m := Real.sqrt_pos.mpr (by linarith)
  have hh0 : h ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
  have hne4 : h ^ 4 ≠ m ^ 2 := by
    rw [show h ^ 4 = (h ^ 2) ^ 2 from by ring, hh2, hm2]; exact hgen
  have hhP : PConstructible h :=
    sqrt_Pconstructible (PConstructible.sub hnP PConstructible.base_one)
  have hmP : PConstructible m :=
    sqrt_Pconstructible (PConstructible.sub PConstructible.base_one hcP)
  have hp' : (1 + h ^ 2) * Real.sin Φ ^ 2 < 1 := by rw [hn']; exact hp
  have hne : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ, 1 - n * Real.sin θ ^ 2 ≠ 0 := by
    intro θ hθ
    have := thirdKindPole_ne_zero_of_mem (h := h) h0.le hlt hp' hθ
    rwa [hn'] at this
  rw [ellipticPiInc_eq_aux_of_ne hc hne, ← hn']
  refine PConstructible.add (ellipticF_Pconstructible hcP hΦP hc)
    (PConstructible.mul (hn' ▸ hnP) ?_)
  exact ellipticPiAux_Pconstructible_gt_one hm2 hc hc0 hmpos hcP hmP hhP hΦP h0 hlt hp'
    hh0 hne4

end Pconstructible
