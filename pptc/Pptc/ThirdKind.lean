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

end Pconstructible
