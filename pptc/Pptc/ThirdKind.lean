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
  to `F`, `E` and elementary terms — for *every* `φ`. Those three families are proved
  P-constructible here. (`n = 1` turns out not to need the master identity at all: its
  antiderivative is `F(φ) + (tan φ Δ(φ) - E(φ))/(1 - c)`, one line of calculus.)
* For general `n` the surviving term is itself an incomplete `Π` with the parameter and
  the argument *interchanged*, so the system does not close. What comes out instead is
  Legendre's interchange relation, `ellipticPiAux_interchange`. It is antisymmetric under
  swapping the two angles, hence vacuous on the diagonal, and so gives no value of `Π`.

That is the honest boundary: the incomplete third kind is Legendre's irreducible case, and
no reduction to `F` and `E` exists. Reaching it would need a genuinely new construction.
The last section records what the search for one has turned up. -/

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
  have hkey := integral_thirdKindMaster hc hc φ
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
  exact PConstructible.div
    (PConstructible.sub (ellipticE_Pconstructible hcP hφP hc)
      (PConstructible.div (PConstructible.mul (PConstructible.mul hcP (sin_Pconstructible hφP))
        (cos_Pconstructible hφP)) (ellipticEIntegrand_Pconstructible hcP hφP)))
    (PConstructible.sub PConstructible.base_one hcP)

-- Theorem: `Π(1, φ, c)` is P-constructible for `|φ| < π/2`.
theorem ellipticPiInc_one_Pconstructible {c φ : ℝ} (hcP : PConstructible c)
    (hφP : PConstructible φ) (hc : c < 1) (hφ : |φ| < Real.pi / 2) :
    PConstructible (ellipticPiInc c 1 φ) := by
  rw [ellipticPiInc_one hc hφ]
  exact PConstructible.add (ellipticF_Pconstructible hcP hφP hc)
    (PConstructible.div
      (PConstructible.sub
        (PConstructible.mul (tan_Pconstructible hφP)
          (ellipticEIntegrand_Pconstructible hcP hφP))
        (ellipticE_Pconstructible hcP hφP hc))
      (PConstructible.sub PConstructible.base_one hcP))

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

end Pconstructible
