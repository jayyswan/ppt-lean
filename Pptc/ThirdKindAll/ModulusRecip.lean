/-
Copyright (c) 2024 Lean Community. All rights reserved.

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

import Pptc.ThirdKindAll.Standard

/-! # Pptc.ThirdKindAll.ModulusRecip

The reciprocal-modulus transformation. For `c > 1` the substitution

  `sin ψ = √c · sin θ`

carries the third-kind integrand at `(c, n)` to the one at `(1/c, n/c)`:

  `Π(c, n, θ) = (1/√c) · Π(1/c, n/c, ψ)`.

Since `1/c ∈ (0, 1)`, this reduces the whole range `c > 1` to the standard case. The
substitution is only a diffeomorphism up to the branch point `θ = arcsin (1/√c)`, which is
exactly what the modulus no-pole hypothesis excludes. -/

namespace Pconstructible

/-- The square root of the modulus. -/
noncomputable def recipMu (c : ℝ) : ℝ := Real.sqrt c

/-- The reciprocal modulus, in `(0, 1)` for `c > 1`. -/
noncomputable def recipC (c : ℝ) : ℝ := 1 / c

/-- The transformed characteristic. -/
noncomputable def recipN (c n : ℝ) : ℝ := n / c

/-- The transformed angle, `arcsin (√c sin θ)`. -/
noncomputable def recipPsi (c θ : ℝ) : ℝ := Real.arcsin (recipMu c * Real.sin θ)

theorem recipMu_sq {c : ℝ} (hc : 1 < c) : recipMu c ^ 2 = c := by
  rw [recipMu, Real.sq_sqrt (by linarith)]

theorem recipMu_pos {c : ℝ} (hc : 1 < c) : 0 < recipMu c :=
  Real.sqrt_pos.mpr (by linarith)

theorem one_lt_recipMu {c : ℝ} (hc : 1 < c) : 1 < recipMu c := by
  rw [recipMu, show (1 : ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)

theorem recipMu_ne_zero {c : ℝ} (hc : 1 < c) : recipMu c ≠ 0 := (recipMu_pos hc).ne'

theorem recipC_pos {c : ℝ} (hc : 1 < c) : 0 < recipC c := by
  rw [recipC]
  positivity

theorem recipC_lt_one {c : ℝ} (hc : 1 < c) : recipC c < 1 := by
  rw [recipC, div_lt_one (by linarith)]
  linarith

theorem recipPsi_zero (c : ℝ) : recipPsi c 0 = 0 := by
  simp [recipPsi]

/-- On the path, `1 - c sin²θ` is not merely nonzero but positive: it is `1` at `0`, and
a sign change would produce a zero. -/
theorem one_sub_mul_sin_sq_pos_of_hmod {c Φ : ℝ} (hc : 1 < c)
    (hmod : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ, 1 - c * Real.sin θ ^ 2 ≠ 0) :
    ∀ θ ∈ Set.uIcc (0 : ℝ) Φ, 0 < 1 - c * Real.sin θ ^ 2 := by
  intro θ hθ
  rcases lt_trichotomy (1 - c * Real.sin θ ^ 2) 0 with hneg | hzero | hpos
  · exfalso
    have hcont : ContinuousOn (fun x : ℝ => 1 - c * Real.sin x ^ 2)
        (Set.uIcc (0 : ℝ) θ) := by fun_prop
    have hmem : (0 : ℝ) ∈ Set.uIcc (1 - c * Real.sin 0 ^ 2)
        (1 - c * Real.sin θ ^ 2) := by
      rw [show 1 - c * Real.sin 0 ^ 2 = 1 by simp]
      rw [Set.mem_uIcc]
      exact Or.inr ⟨le_of_lt hneg, by norm_num⟩
    obtain ⟨ζ, hζ, hζzero⟩ := intermediate_value_uIcc hcont hmem
    have hsub : Set.uIcc (0 : ℝ) θ ⊆ Set.uIcc (0 : ℝ) Φ := by
      rw [Set.uIcc_subset_uIcc_iff_mem]
      exact ⟨Set.left_mem_uIcc, hθ⟩
    exact hmod ζ (hsub hζ) hζzero
  · exact absurd hzero (hmod θ hθ)
  · exact hpos

/-- The branch point `arcsin (1/√c)`. -/
noncomputable def recipBranch (c : ℝ) : ℝ := Real.arcsin (1 / recipMu c)

theorem recipBranch_pos {c : ℝ} (hc : 1 < c) : 0 < recipBranch c := by
  rw [recipBranch, Real.arcsin_pos]
  exact div_pos one_pos (recipMu_pos hc)

theorem recipBranch_lt_pi_div_two {c : ℝ} (hc : 1 < c) : recipBranch c < Real.pi / 2 := by
  rw [recipBranch, Real.arcsin_lt_pi_div_two]
  rw [div_lt_one (recipMu_pos hc)]
  exact one_lt_recipMu hc

theorem sin_recipBranch {c : ℝ} (hc : 1 < c) :
    Real.sin (recipBranch c) = 1 / recipMu c := by
  rw [recipBranch, Real.sin_arcsin (by linarith [div_pos one_pos (recipMu_pos hc)]) (by
    exact ((div_lt_one (recipMu_pos hc)).mpr (one_lt_recipMu hc)).le)]

theorem one_sub_mul_sin_sq_recipBranch {c : ℝ} (hc : 1 < c) :
    1 - c * Real.sin (recipBranch c) ^ 2 = 0 := by
  rw [sin_recipBranch hc, div_pow, recipMu_sq hc]
  field_simp [(recipMu_pos hc).ne']
  ring

/-- The modulus no-pole hypothesis keeps the path strictly inside the branch segment. -/
theorem abs_lt_recipBranch {c Φ : ℝ} (hc : 1 < c)
    (hmod : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ, 1 - c * Real.sin θ ^ 2 ≠ 0) :
    |Φ| < recipBranch c := by
  rw [abs_lt]
  constructor
  · by_contra h
    have hle : Φ ≤ -recipBranch c := le_of_not_gt h
    have hmem : -recipBranch c ∈ Set.uIcc (0 : ℝ) Φ := by
      rw [Set.mem_uIcc]
      exact Or.inr ⟨hle, by linarith [recipBranch_pos hc]⟩
    have hzero := hmod (-recipBranch c) hmem
    rw [Real.sin_neg, neg_sq, one_sub_mul_sin_sq_recipBranch hc] at hzero
    exact hzero rfl
  · by_contra h
    have hle : recipBranch c ≤ Φ := le_of_not_gt h
    have hmem : recipBranch c ∈ Set.uIcc (0 : ℝ) Φ := by
      rw [Set.mem_uIcc]
      exact Or.inl ⟨(recipBranch_pos hc).le, hle⟩
    exact hmod (recipBranch c) hmem (one_sub_mul_sin_sq_recipBranch hc)

/-- On the path, `|√c sin θ| < 1`, so `arcsin` is applied inside its domain. -/
theorem abs_recipMu_mul_sin_lt_one {c Φ θ : ℝ} (hc : 1 < c)
    (hmod : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ, 1 - c * Real.sin θ ^ 2 ≠ 0)
    (hθ : θ ∈ Set.uIcc (0 : ℝ) Φ) :
    |recipMu c * Real.sin θ| < 1 := by
  have hpos := one_sub_mul_sin_sq_pos_of_hmod hc hmod θ hθ
  have hsq : (recipMu c * Real.sin θ) ^ 2 < 1 := by
    rw [mul_pow, recipMu_sq hc]
    nlinarith
  have hsq' : (recipMu c * Real.sin θ) ^ 2 < (1 : ℝ) ^ 2 := by simpa using hsq
  rwa [sq_lt_sq, abs_one] at hsq'

/-- The transformed angle stays in `(-π/2, π/2)`. -/
theorem abs_recipPsi_lt_pi_div_two {c Φ θ : ℝ} (hc : 1 < c)
    (hmod : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ, 1 - c * Real.sin θ ^ 2 ≠ 0)
    (hθ : θ ∈ Set.uIcc (0 : ℝ) Φ) :
    |recipPsi c θ| < Real.pi / 2 := by
  have h := abs_recipMu_mul_sin_lt_one hc hmod hθ
  rw [abs_lt] at h
  rw [recipPsi, abs_lt]
  exact ⟨(Real.neg_pi_div_two_lt_arcsin).mpr h.1, (Real.arcsin_lt_pi_div_two).mpr h.2⟩

/-- Squaring kills the `arcsin`. -/
theorem sin_recipPsi_sq {c Φ θ : ℝ} (hc : 1 < c)
    (hmod : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ, 1 - c * Real.sin θ ^ 2 ≠ 0)
    (hθ : θ ∈ Set.uIcc (0 : ℝ) Φ) :
    Real.sin (recipPsi c θ) ^ 2 = c * Real.sin θ ^ 2 := by
  have h := abs_recipMu_mul_sin_lt_one hc hmod hθ
  rw [abs_lt] at h
  rw [recipPsi, Real.sin_arcsin h.1.le h.2.le, mul_pow, recipMu_sq hc]

/-- The characteristic numerator transforms exactly. -/
theorem one_sub_recipN_mul_sin_sq {c n Φ θ : ℝ} (hc : 1 < c)
    (hmod : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ, 1 - c * Real.sin θ ^ 2 ≠ 0)
    (hθ : θ ∈ Set.uIcc (0 : ℝ) Φ) :
    1 - recipN c n * Real.sin (recipPsi c θ) ^ 2 = 1 - n * Real.sin θ ^ 2 := by
  rw [sin_recipPsi_sq hc hmod hθ, recipN]
  field_simp

/-- The modulus numerator transforms to `cos²θ`. -/
theorem one_sub_recipC_mul_sin_sq {c Φ θ : ℝ} (hc : 1 < c)
    (hmod : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ, 1 - c * Real.sin θ ^ 2 ≠ 0)
    (hθ : θ ∈ Set.uIcc (0 : ℝ) Φ) :
    1 - recipC c * Real.sin (recipPsi c θ) ^ 2 = Real.cos θ ^ 2 := by
  rw [sin_recipPsi_sq hc hmod hθ, recipC]
  field_simp
  linear_combination -Real.sin_sq_add_cos_sq θ

/-- The transformed `Δ` is `cos θ` on the path. -/
theorem ellipticEIntegrand_recipC_recipPsi {c Φ θ : ℝ} (hc : 1 < c)
    (hmod : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ, 1 - c * Real.sin θ ^ 2 ≠ 0)
    (hθ : θ ∈ Set.uIcc (0 : ℝ) Φ) (hcos : 0 < Real.cos θ) :
    ellipticEIntegrand (recipC c) (recipPsi c θ) = Real.cos θ := by
  rw [ellipticEIntegrand, one_sub_recipC_mul_sin_sq hc hmod hθ, Real.sqrt_sq hcos.le]

/-- The derivative of the transformed angle. -/
theorem hasDerivAt_recipPsi {c Φ θ : ℝ} (hc : 1 < c)
    (hmod : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ, 1 - c * Real.sin θ ^ 2 ≠ 0)
    (hθ : θ ∈ Set.uIcc (0 : ℝ) Φ) :
    HasDerivAt (recipPsi c) (recipMu c * Real.cos θ / ellipticEIntegrand c θ) θ := by
  have habs := abs_recipMu_mul_sin_lt_one hc hmod hθ
  rw [abs_lt] at habs
  have harg : HasDerivAt (fun x : ℝ => recipMu c * Real.sin x)
      (recipMu c * Real.cos θ) θ :=
    (Real.hasDerivAt_sin θ).const_mul (recipMu c)
  have harc := (Real.hasDerivAt_arcsin (ne_of_gt habs.1) (ne_of_lt habs.2)).comp θ harg
  refine harc.congr_deriv ?_
  have hpos := one_sub_mul_sin_sq_pos_of_hmod hc hmod θ hθ
  have hEpos : 0 < ellipticEIntegrand c θ := Real.sqrt_pos.mpr hpos
  have hsq : 1 - (recipMu c * Real.sin θ) ^ 2 = ellipticEIntegrand c θ ^ 2 := by
    rw [mul_pow, recipMu_sq hc]
    rw [ellipticEIntegrand]
    rw [Real.sq_sqrt hpos.le]
  rw [hsq, Real.sqrt_sq hEpos.le]
  field_simp

/-- Pointwise, the substituted integrand is `√c` times the original one. -/
theorem recip_transfer {c n Φ θ : ℝ} (hc : 1 < c)
    (hmod : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ, 1 - c * Real.sin θ ^ 2 ≠ 0)
    (hne : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ, 1 - n * Real.sin θ ^ 2 ≠ 0)
    (hθ : θ ∈ Set.uIcc (0 : ℝ) Φ) (hcos : 0 < Real.cos θ) :
    (recipMu c * Real.cos θ / ellipticEIntegrand c θ)
        * ellipticPiIntegrand (recipC c) (recipN c n) (recipPsi c θ)
      = recipMu c * ellipticPiIntegrand c n θ := by
  have hpos := one_sub_mul_sin_sq_pos_of_hmod hc hmod θ hθ
  have hEpos : 0 < ellipticEIntegrand c θ := Real.sqrt_pos.mpr hpos
  rw [ellipticPiIntegrand, ellipticPiIntegrand,
    one_sub_recipN_mul_sin_sq hc hmod hθ,
    ellipticEIntegrand_recipC_recipPsi hc hmod hθ hcos]
  field_simp [hEpos.ne', hne θ hθ, hcos.ne']

/-- **The reciprocal-modulus transformation.** For `c > 1`, on the branch segment,
`Π(c, n, θ) = (1/√c) Π(1/c, n/c, arcsin (√c sin θ))`. -/
theorem ellipticPiInc_recip {c n Φ : ℝ} (hc : 1 < c)
    (hmod : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ, 1 - c * Real.sin θ ^ 2 ≠ 0)
    (hne : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ, 1 - n * Real.sin θ ^ 2 ≠ 0) :
    ellipticPiInc c n Φ
      = (1 / recipMu c) * ellipticPiInc (recipC c) (recipN c n) (recipPsi c Φ) := by
  have hbranch := abs_lt_recipBranch hc hmod
  have hΦ : |Φ| < Real.pi / 2 := by
    have := recipBranch_lt_pi_div_two hc
    rw [abs_lt] at hbranch ⊢
    constructor <;> linarith
  have hcos : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ, 0 < Real.cos θ :=
    fun θ hθ => cos_pos_of_mem_uIcc hΦ hθ
  have hderiv : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ,
      HasDerivAt (recipPsi c) (recipMu c * Real.cos θ / ellipticEIntegrand c θ) θ :=
    fun θ hθ => hasDerivAt_recipPsi hc hmod hθ
  have hcont : ContinuousOn (fun θ : ℝ => recipMu c * Real.cos θ / ellipticEIntegrand c θ)
      (Set.uIcc (0 : ℝ) Φ) := by
    refine ContinuousOn.div (by fun_prop) (continuous_ellipticEIntegrand c).continuousOn ?_
    intro θ hθ
    exact (Real.sqrt_pos.mpr (one_sub_mul_sin_sq_pos_of_hmod hc hmod θ hθ)).ne'
  have hg : ContinuousOn (ellipticPiIntegrand (recipC c) (recipN c n))
      (recipPsi c '' Set.uIcc (0 : ℝ) Φ) := by
    rintro σ ⟨θ, hθ, rfl⟩
    refine ContinuousAt.continuousWithinAt (ContinuousAt.div continuousAt_const ?_ ?_)
    · exact ((by fun_prop : ContinuousAt
          (fun x : ℝ => 1 - recipN c n * Real.sin x ^ 2) _)).mul
        (continuous_ellipticEIntegrand (recipC c)).continuousAt
    · refine mul_ne_zero ?_ ?_
      · rw [one_sub_recipN_mul_sin_sq hc hmod hθ]
        exact hne θ hθ
      · rw [ellipticEIntegrand]
        exact (Real.sqrt_pos.mpr (by
          rw [one_sub_recipC_mul_sin_sq hc hmod hθ]
          exact pow_pos (hcos θ hθ) 2)).ne'
  have hsub := intervalIntegral.integral_deriv_smul_comp' (a := (0 : ℝ)) (b := Φ)
    (f := recipPsi c) (f' := fun θ : ℝ => recipMu c * Real.cos θ / ellipticEIntegrand c θ)
    (g := ellipticPiIntegrand (recipC c) (recipN c n)) hderiv hcont hg
  have hsub' : (∫ x in (0 : ℝ)..Φ, (recipMu c * Real.cos x / ellipticEIntegrand c x)
      * ellipticPiIntegrand (recipC c) (recipN c n) (recipPsi c x))
      = ∫ x in (0 : ℝ)..recipPsi c Φ,
        ellipticPiIntegrand (recipC c) (recipN c n) x := by
    simpa [recipPsi_zero, Function.comp_apply, smul_eq_mul] using hsub
  have hcongr : (∫ x in (0 : ℝ)..Φ, (recipMu c * Real.cos x / ellipticEIntegrand c x)
      * ellipticPiIntegrand (recipC c) (recipN c n) (recipPsi c x))
      = ∫ x in (0 : ℝ)..Φ, recipMu c * ellipticPiIntegrand c n x :=
    intervalIntegral.integral_congr fun x hx =>
      recip_transfer hc hmod hne hx (hcos x hx)
  rw [ellipticPiInc, eq_comm]
  calc (1 / recipMu c) * ellipticPiInc (recipC c) (recipN c n) (recipPsi c Φ)
      = (1 / recipMu c) * ∫ x in (0 : ℝ)..recipPsi c Φ,
          ellipticPiIntegrand (recipC c) (recipN c n) x := rfl
    _ = (1 / recipMu c) * ∫ x in (0 : ℝ)..Φ, (recipMu c * Real.cos x
          / ellipticEIntegrand c x) * ellipticPiIntegrand (recipC c) (recipN c n)
            (recipPsi c x) := by rw [hsub']
    _ = (1 / recipMu c) * ∫ x in (0 : ℝ)..Φ, recipMu c * ellipticPiIntegrand c n x := by
          rw [hcongr]
    _ = ∫ x in (0 : ℝ)..Φ, ellipticPiIntegrand c n x := by
          rw [intervalIntegral.integral_const_mul]
          field_simp [(recipMu_ne_zero hc)]

/-- **The reciprocal-modulus case of the headline theorem.** -/
theorem ellipticPiInc_Pconstructible_recip {c n Φ : ℝ}
    (hcP : PConstructible c) (hnP : PConstructible n) (hΦP : PConstructible Φ)
    (hc : 1 < c)
    (hmod : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ, 1 - c * Real.sin θ ^ 2 ≠ 0)
    (hne : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ, 1 - n * Real.sin θ ^ 2 ≠ 0) :
    PConstructible (ellipticPiInc c n Φ) := by
  have hbranch := abs_lt_recipBranch hc hmod
  have hΦ : |Φ| < Real.pi / 2 := by
    have := recipBranch_lt_pi_div_two hc
    rw [abs_lt] at hbranch ⊢
    constructor <;> linarith
  have hcos : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ, 0 < Real.cos θ :=
    fun θ hθ => cos_pos_of_mem_uIcc hΦ hθ
  have hmono : MonotoneOn (recipPsi c) (Set.uIcc (0 : ℝ) Φ) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun x : ℝ =>
      recipMu c * Real.cos x / ellipticEIntegrand c x) (convex_uIcc (0 : ℝ) Φ)
      (by unfold recipPsi; fun_prop) ?_ ?_
    · intro x hx
      exact (hasDerivAt_recipPsi hc hmod (interior_subset hx)).hasDerivWithinAt
    · intro x hx
      have hx' : x ∈ Set.uIcc (0 : ℝ) Φ := interior_subset hx
      have hpos := one_sub_mul_sin_sq_pos_of_hmod hc hmod x hx'
      have hEpos : 0 < ellipticEIntegrand c x := Real.sqrt_pos.mpr hpos
      exact div_nonneg (mul_nonneg (recipMu_pos hc).le (hcos x hx').le) hEpos.le
  have himage : recipPsi c '' Set.uIcc (0 : ℝ) Φ = Set.uIcc 0 (recipPsi c Φ) := by
    have hcont : ContinuousOn (recipPsi c) (Set.uIcc (0 : ℝ) Φ) := by
      unfold recipPsi
      fun_prop
    simpa [recipPsi_zero] using hcont.image_uIcc_of_monotoneOn hmono
  have hne' : ∀ σ ∈ Set.uIcc (0 : ℝ) (recipPsi c Φ),
      1 - recipN c n * Real.sin σ ^ 2 ≠ 0 := by
    intro σ hσ
    rw [← himage] at hσ
    obtain ⟨θ, hθ, rfl⟩ := hσ
    rw [one_sub_recipN_mul_sin_sq hc hmod hθ]
    exact hne θ hθ
  rw [ellipticPiInc_recip hc hmod hne]
  have hcP' : PConstructible (recipC c) := by
    rw [recipC]
    pconstructible
  have hnP' : PConstructible (recipN c n) := by
    rw [recipN]
    pconstructible
  have hψP : PConstructible (recipPsi c Φ) := by
    rw [recipPsi, recipMu]
    pconstructible
  have hμP : PConstructible (recipMu c) := by
    rw [recipMu]
    pconstructible
  exact PConstructible.mul (by simpa [one_div] using inv_Pconstructible hμP)
    (ellipticPiInc_Pconstructible_standard hcP' hnP' hψP (recipC_pos hc) (recipC_lt_one hc) hne')

end Pconstructible
