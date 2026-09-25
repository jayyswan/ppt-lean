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

-- Targeted imports rather than `import Mathlib`; see the note in `Pptc.Defs`.
import Pptc.GammaFunctional

/-! # The half-shift and doubling ratios

The analytic half of the development delivers the *products* `Γ(ρ) Γ(1/2 - ρ)` for rational
`ρ ∈ (0, 1/2)` (the hypothesis `HalfProducts` below). This file converts those products into
the two ratios the arithmetic half needs, working multiplicatively modulo `PConstructible`.

**Half-shift.** `H(x) = Γ(x) / Γ(x + 1/2)` is P-constructible for every rational `x > 0`:

* for `ρ ∈ (0, 1/2)`, `H(ρ) = Γ(ρ) Γ(1/2 - ρ) / (Γ(1/2 - ρ) Γ(1/2 + ρ))`, a half-product
  over the reflection product `Γ(y) Γ(1 - y)` at `y = 1/2 - ρ`, which is P-constructible and
  nonzero;
* for `x ∈ ½ℤ` both values are P-constructible outright;
* the step `H(x) H(x + 1/2) = Γ(x) / Γ(x + 1) = 1/x` gives `H(x + 1/2) = 1 / (x H(x))`, so
  induction on `k` settles `x = ρ + k/2`.

**Doubling.** Legendre's duplication formula gives `D(x) = Γ(x)² / Γ(2x) = dupFactor x · H(x)`,
again P-constructible. `Pptc.GammaRational.Doubling` takes these ratios as hypotheses and
finishes the job. -/

namespace Pconstructible

/-- The hypothesis the analytic half delivers: products `Γ(ρ) Γ(1/2 - ρ)` for rational
`ρ ∈ (0, 1/2)` are P-constructible. -/
def HalfProducts : Prop :=
  ∀ ρ : ℚ, 0 < ρ → ρ < 1 / 2 →
    PConstructible (Real.Gamma (ρ : ℝ) * Real.Gamma (1 / 2 - (ρ : ℝ)))

/-! ### The half-shift ratio

Write `H(x) = Γ(x) / Γ(x + 1/2)`. Three pieces build it:

* the base `H(ρ)` for `ρ ∈ (0, 1/2)`: the half-product `Γ(ρ) Γ(1/2 - ρ)` from `«hΠ»` divided
  by the reflection product `Γ(1/2 - ρ) Γ(1/2 + ρ)` at `y = 1/2 - ρ`, whose second factor is
  `Γ(1 - y) = Γ(ρ + 1/2)`;
* the half-integer base `H(m/2)`: both `Γ(m/2)` and `Γ((m+1)/2)` are
  `Gamma_intCast_div_two_Pconstructible`;
* the recurrence `H(y) H(y + 1/2) = Γ(y) / Γ(y + 1) = 1 / y`, so
  `H(y + 1/2) = (1 / y) / H(y)` — division carries no side condition.

Any positive rational is `ρ + k/2` with `ρ ∈ [0, 1/2)`, obtained from the floor of `2x`. -/

-- Lemma: the recurrence step `H(y + 1/2) = (1 / y) / H(y)` of the half-shift ratio.
private theorem half_shift_step {y : ℚ} (hy : 0 < y)
    (h : PConstructible (Real.Gamma (y : ℝ) / Real.Gamma ((y : ℝ) + 1 / 2))) :
    PConstructible (Real.Gamma ((y : ℝ) + 1 / 2) / Real.Gamma ((y : ℝ) + 1)) := by
  have hyr : (0 : ℝ) < (y : ℝ) := by exact_mod_cast hy
  have hyne : (y : ℝ) ≠ 0 := ne_of_gt hyr
  have hGy : Real.Gamma (y : ℝ) ≠ 0 := (Real.Gamma_pos_of_pos hyr).ne'
  have hGyh : Real.Gamma ((y : ℝ) + 1 / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith)).ne'
  have h1 : PConstructible ((1 : ℝ) / (y : ℝ)) :=
    PConstructible.div PConstructible.base_one (ratval_Pconstructible y rfl)
  have h2 : PConstructible
      ((1 : ℝ) / (y : ℝ) / (Real.Gamma (y : ℝ) / Real.Gamma ((y : ℝ) + 1 / 2))) :=
    PConstructible.div h1 h
  convert h2 using 1
  rw [Real.Gamma_add_one hyne]
  field_simp

-- Lemma: the base case `H(ρ)` for `ρ ∈ (0, 1/2)`, from the half-product `«hΠ» ρ`.
private theorem half_shift_base_Ioo («hΠ» : HalfProducts) (ρ : ℚ) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1 / 2) :
    PConstructible (Real.Gamma (ρ : ℝ) / Real.Gamma ((ρ : ℝ) + 1 / 2)) := by
  have hy : PConstructible ((1 : ℝ) / 2 - (ρ : ℝ)) := by
    refine ratval_Pconstructible (1 / 2 - ρ) ?_
    push_cast
    ring
  have hrefl := Gamma_mul_Gamma_one_sub_Pconstructible hy
  have hden : (1 : ℝ) - (1 / 2 - (ρ : ℝ)) = (ρ : ℝ) + 1 / 2 := by ring
  rw [hden] at hrefl
  have hdiv := PConstructible.div («hΠ» ρ hρ0 hρ1) hrefl
  have hρ1r : (ρ : ℝ) < 1 / 2 := by
    rw [show (1 : ℝ) / 2 = ((1 / 2 : ℚ) : ℝ) by norm_num]
    exact_mod_cast hρ1
  have hρ0r : (0 : ℝ) < (ρ : ℝ) := by
    rw [← Rat.cast_zero]
    exact_mod_cast hρ0
  have hb : Real.Gamma ((1 : ℝ) / 2 - (ρ : ℝ)) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hc : Real.Gamma ((ρ : ℝ) + 1 / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hgoal : Real.Gamma (ρ : ℝ) / Real.Gamma ((ρ : ℝ) + 1 / 2)
      = (Real.Gamma (ρ : ℝ) * Real.Gamma ((1 : ℝ) / 2 - (ρ : ℝ)))
        / (Real.Gamma ((1 : ℝ) / 2 - (ρ : ℝ)) * Real.Gamma ((ρ : ℝ) + 1 / 2)) := by
    rw [eq_comm, mul_comm (Real.Gamma ((1 : ℝ) / 2 - (ρ : ℝ))) (Real.Gamma ((ρ : ℝ) + 1 / 2))]
    exact mul_div_mul_right _ _ hb
  rw [hgoal]
  exact hdiv

-- Lemma: the half-integer base `H(m/2)`, both `Γ` values being elementary.
private theorem half_shift_halfInt (m : ℤ) :
    PConstructible (Real.Gamma ((m : ℝ) / 2) / Real.Gamma ((m : ℝ) / 2 + 1 / 2)) := by
  have h1 : PConstructible (Real.Gamma ((m : ℝ) / 2)) :=
    Gamma_intCast_div_two_Pconstructible m
  have h2 : PConstructible (Real.Gamma (((m + 1 : ℤ) : ℝ) / 2)) :=
    Gamma_intCast_div_two_Pconstructible (m + 1)
  have hcast : (((m + 1 : ℤ) : ℝ) / 2) = (m : ℝ) / 2 + 1 / 2 := by push_cast; ring
  rw [hcast] at h2
  exact PConstructible.div h1 h2

-- Lemma: iterate the recurrence from a base point `ρ ∈ (0, 1/2)`.
private theorem half_shift_iter («hΠ» : HalfProducts) (ρ : ℚ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) :
    ∀ k : ℕ, PConstructible
      (Real.Gamma ((ρ : ℝ) + (k : ℝ) / 2) / Real.Gamma ((ρ : ℝ) + (k : ℝ) / 2 + 1 / 2)) := by
  intro k
  induction k with
  | zero => simpa using half_shift_base_Ioo «hΠ» ρ hρ0 hρ1
  | succ k ih =>
    have hy : (0 : ℚ) < ρ + (k : ℚ) / 2 := by
      have hk : (0 : ℚ) ≤ (k : ℚ) / 2 := by positivity
      linarith
    have h' : PConstructible
        (Real.Gamma (((ρ + (k : ℚ) / 2 : ℚ) : ℝ))
          / Real.Gamma ((((ρ + (k : ℚ) / 2 : ℚ) : ℝ)) + 1 / 2)) := by
      have hc : ((ρ + (k : ℚ) / 2 : ℚ) : ℝ) = (ρ : ℝ) + (k : ℝ) / 2 := by
        push_cast
        ring
      rw [hc]
      exact ih
    have hstep := half_shift_step hy h'
    have hcast1 : (((ρ + (k : ℚ) / 2 : ℚ) : ℝ)) + 1 / 2
        = (ρ : ℝ) + ((k + 1 : ℕ) : ℝ) / 2 := by push_cast; ring
    have hcast2 : (((ρ + (k : ℚ) / 2 : ℚ) : ℝ)) + 1
        = (ρ : ℝ) + ((k + 1 : ℕ) : ℝ) / 2 + 1 / 2 := by push_cast; ring
    rw [hcast1, hcast2] at hstep
    exact hstep

-- Theorem: the half-shift ratio `Γ(x) / Γ(x + 1/2)` is P-constructible for rational `x > 0`.
theorem Gamma_div_Gamma_add_half_Pconstructible («hΠ» : HalfProducts) (x : ℚ) (hx : 0 < x) :
    PConstructible (Real.Gamma (x : ℝ) / Real.Gamma ((x : ℝ) + 1 / 2)) := by
  set q : ℚ := 2 * x with hq
  set m : ℤ := ⌊q⌋ with hm
  set f : ℚ := Int.fract q with hf
  have hf0 : 0 ≤ f := by rw [hf]; exact Int.fract_nonneg q
  have hf1 : f < 1 := by rw [hf]; exact Int.fract_lt_one q
  have hdecomp : (m : ℚ) + f = q := by
    rw [hm, hf]
    exact Int.floor_add_fract q
  have hmnonneg : 0 ≤ m := by
    rw [hm]
    exact Int.floor_nonneg.mpr (by rw [hq]; linarith)
  have hxeq : x = (m : ℚ) / 2 + f / 2 := by
    have h2 : (m : ℚ) + f = 2 * x := by rw [hdecomp, hq]
    linarith
  rcases eq_or_ne f 0 with hfz | hfz
  · -- `f = 0`: `x = m/2` is a half-integer, the elementary base case.
    have hxhalf : x = (m : ℚ) / 2 := by
      rw [hfz] at hxeq
      simpa using hxeq
    have hxcast : (x : ℝ) = (m : ℝ) / 2 := by
      rw [hxhalf]; push_cast; ring
    rw [hxcast]
    exact half_shift_halfInt m
  · -- `0 < f`: the base point `ρ = f/2` lies in `(0, 1/2)`.
    have hfpos : 0 < f := lt_of_le_of_ne hf0 (Ne.symm hfz)
    set ρ : ℚ := f / 2 with hρdef
    have hρ0 : 0 < ρ := by rw [hρdef]; linarith
    have hρ1 : ρ < 1 / 2 := by rw [hρdef]; linarith
    have hmcast : (m : ℚ) = (m.toNat : ℚ) := by
      exact_mod_cast (Int.toNat_of_nonneg hmnonneg).symm
    have hxρ : x = ρ + (m.toNat : ℚ) / 2 := by
      rw [hxeq, hρdef, hmcast]
      ring
    have hxcast : (x : ℝ) = (ρ : ℝ) + (m.toNat : ℝ) / 2 := by
      rw [hxρ]; push_cast; ring
    rw [hxcast]
    exact half_shift_iter «hΠ» ρ hρ0 hρ1 m.toNat

/-! ### The doubling ratio

Legendre's duplication formula `Γ(x) Γ(x + 1/2) = Γ(2x) · dupFactor x` rearranges to
`D(x) = Γ(x)² / Γ(2x) = dupFactor x · H(x)`, a product of two P-constructible numbers. -/

-- Theorem: the doubling ratio `Γ(x)² / Γ(2x)` is P-constructible for rational `x > 0`.
theorem Gamma_sq_div_Gamma_two_mul_Pconstructible («hΠ» : HalfProducts) (x : ℚ) (hx : 0 < x) :
    PConstructible (Real.Gamma (x : ℝ) ^ 2 / Real.Gamma (2 * (x : ℝ))) := by
  have hxr : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
  have hGx : Real.Gamma (x : ℝ) ≠ 0 := (Real.Gamma_pos_of_pos hxr).ne'
  have hGxh : Real.Gamma ((x : ℝ) + 1 / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hG2 : Real.Gamma (2 * (x : ℝ)) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hdu : dupFactor (x : ℝ)
      = Real.Gamma (x : ℝ) * Real.Gamma ((x : ℝ) + 1 / 2) / Real.Gamma (2 * (x : ℝ)) := by
    rw [eq_div_iff hG2, mul_comm (dupFactor (x : ℝ)) (Real.Gamma (2 * (x : ℝ)))]
    exact (Gamma_mul_Gamma_add_half' (x : ℝ)).symm
  have hfinal : dupFactor (x : ℝ) * (Real.Gamma (x : ℝ) / Real.Gamma ((x : ℝ) + 1 / 2))
      = Real.Gamma (x : ℝ) ^ 2 / Real.Gamma (2 * (x : ℝ)) := by
    rw [hdu]
    field_simp
  have hmul : PConstructible
      (dupFactor (x : ℝ) * (Real.Gamma (x : ℝ) / Real.Gamma ((x : ℝ) + 1 / 2))) :=
    PConstructible.mul (dupFactor_Pconstructible (rat_Pconstructible x))
      (Gamma_div_Gamma_add_half_Pconstructible «hΠ» x hx)
  convert hmul using 1
  exact hfinal.symm

end Pconstructible
