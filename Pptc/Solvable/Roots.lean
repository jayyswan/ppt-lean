/-
Copyright (c) 2024 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pptc contributors
-/

import Pptc.Solvable.Basic
import Mathlib.FieldTheory.AbelRuffini
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Complex roots of P-constructible numbers

The main result here is that `PComplex`, the field of complex numbers with
P-constructible real and imaginary parts, is closed under `n`-th roots.  Combined with
`solvableByRad_le`, this gives the unconditional inclusion
`solvableByRad ℚ ℂ ≤ PComplex`.

The construction of a root is the usual polar one:

`z = r (cos θ + i sin θ)`, so `w = r^(1/n) (cos (θ/n) + i sin (θ/n))`

satisfies `w^n = z`.  The angle `θ` is built from `arccos` and the sign of the imaginary
part, so `r`, `θ`, `cos (θ/n)` and `sin (θ/n)` are all P-constructible by
`Pptc.Basic`.  The remaining `n`-th roots differ from `w` by roots of unity, which are
`exp (2π i k/n)` and hence also have P-constructible coordinates.
-/

namespace Pconstructible

open Complex

/-- Polar-angle representation of a nonzero complex number with P-constructible
coordinates. -/
theorem exists_P_angle {a b : ℝ} (ha : PConstructible a) (hb : PConstructible b)
    (hne : a ≠ 0 ∨ b ≠ 0) :
    ∃ θ : ℝ, PConstructible θ ∧
      Real.cos θ = a / Real.sqrt (a ^ 2 + b ^ 2) ∧
      Real.sin θ = b / Real.sqrt (a ^ 2 + b ^ 2) := by
  set r : ℝ := Real.sqrt (a ^ 2 + b ^ 2) with hr
  have hsq : 0 < a ^ 2 + b ^ 2 := by
    rcases hne with ha' | hb'
    · nlinarith [sq_pos_of_ne_zero ha', sq_nonneg b]
    · nlinarith [sq_pos_of_ne_zero hb', sq_nonneg a]
  have hrpos : 0 < r := Real.sqrt_pos.mpr hsq
  have hPr : PConstructible r :=
    sqrt_Pconstructible (PConstructible.add (sq_Pconstructible ha) (sq_Pconstructible hb))
  set u : ℝ := a / r with hu
  have hPu : PConstructible u := PConstructible.div ha hPr
  have habs : |a| ≤ r := Real.abs_le_sqrt (by nlinarith [sq_nonneg b])
  obtain ⟨hlo, hhi⟩ := abs_le.mp habs
  have hu_le : u ≤ 1 := by
    rw [hu, div_le_one hrpos]
    exact hhi
  have hu_ge : -1 ≤ u := by
    rw [hu, le_div_iff₀ hrpos]
    simpa using hlo
  have hParc : PConstructible (Real.arccos u) :=
    arccos_Pconstructible_of_mem_Icc hPu hu_ge hu_le
  have hcos_u : Real.cos (Real.arccos u) = u := Real.cos_arccos hu_ge hu_le
  have hr_sq : r ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt hsq.le
  have hsin_u : Real.sin (Real.arccos u) = |b| / r := by
    rw [Real.sin_arccos]
    have hsub : 1 - u ^ 2 = (b / r) ^ 2 := by
      rw [hu, div_pow, div_pow]
      field_simp [hrpos.ne']
      nlinarith [hr_sq]
    rw [hsub, Real.sqrt_sq_eq_abs, abs_div, abs_of_pos hrpos]
  refine ⟨if 0 ≤ b then Real.arccos u else -Real.arccos u, ?_, ?_, ?_⟩
  · by_cases hb' : 0 ≤ b
    · simpa [hb'] using hParc
    · simpa [hb'] using neg_Pconstructible hParc
  · by_cases hb' : 0 ≤ b
    · simp only [hb', if_true]
      rw [hcos_u, hu]
    · simp only [hb', if_false]
      rw [Real.cos_neg, hcos_u, hu]
  · by_cases hb' : 0 ≤ b
    · simp only [hb', if_true]
      rw [hsin_u, abs_of_nonneg hb']
    · have hbneg : b < 0 := lt_of_not_ge hb'
      simp only [hb', if_false]
      rw [Real.sin_neg, hsin_u, abs_of_neg hbneg]
      ring

/-- Given `z ∈ PComplex`, there is an `n`-th root also in `PComplex`. -/
theorem exists_PComplex_nth_root {z : ℂ} (hz : z ∈ PComplex) {n : ℕ} (hn : n ≠ 0) :
    ∃ w : ℂ, w ∈ PComplex ∧ w ^ n = z := by
  by_cases hz0 : z = 0
  · subst z
    exact ⟨0, PComplex.zero_mem, by rw [zero_pow hn]⟩
  · have hne : z.re ≠ 0 ∨ z.im ≠ 0 := by
      rcases eq_or_ne z.re 0 with hre | hre
      · right
        intro him
        exact hz0 (Complex.ext hre him)
      · exact Or.inl hre
    obtain ⟨θ, hθP, hcos, hsin⟩ :=
      exists_P_angle (a := z.re) (b := z.im) hz.1 hz.2 hne
    set r : ℝ := Real.sqrt (z.re ^ 2 + z.im ^ 2) with hr
    have hsq : 0 < z.re ^ 2 + z.im ^ 2 := by
      rcases hne with hre | him
      · nlinarith [sq_pos_of_ne_zero hre, sq_nonneg z.im]
      · nlinarith [sq_pos_of_ne_zero him, sq_nonneg z.re]
    have hrpos : 0 < r := Real.sqrt_pos.mpr hsq
    have hPr : PConstructible r :=
      sqrt_Pconstructible
        (PConstructible.add (sq_Pconstructible hz.1) (sq_Pconstructible hz.2))
    set φ : ℝ := θ / n with hφ
    have hPφ : PConstructible φ := PConstructible.div hθP (nat_Pconstructible n)
    set ρ : ℝ := r ^ ((n : ℝ)⁻¹) with hρ
    have hPρ : PConstructible ρ :=
      rpow_Pconstructible hPr (inv_Pconstructible (nat_Pconstructible n)) hrpos
    have hPcos : PConstructible (Real.cos φ) := cos_Pconstructible hPφ
    have hPsin : PConstructible (Real.sin φ) := sin_Pconstructible hPφ
    let w : ℂ := (ρ : ℂ) * ((Real.cos φ : ℂ) + (Real.sin φ : ℂ) * I)
    have hwP : w ∈ PComplex := by
      apply mem_PComplex_of_PConstructibleC
      dsimp [w]
      exact PConstructibleC.mul (PConstructibleC.ofReal hPρ)
        (PConstructibleC.add (PConstructibleC.ofReal hPcos)
          (PConstructibleC.mul (PConstructibleC.ofReal hPsin) PConstructibleC.I))
    refine ⟨w, hwP, ?_⟩
    dsimp [w]
    rw [mul_pow]
    have hpow_r : ((ρ : ℂ) ^ n) = (r : ℂ) := by
      rw [hρ, ← Complex.ofReal_pow, Real.rpow_inv_natCast_pow hrpos.le hn]
    have hφn : (n : ℂ) * (φ : ℂ) = (θ : ℂ) := by
      rw [hφ]
      push_cast
      field_simp [show (n : ℂ) ≠ 0 by exact_mod_cast hn]
    have hdeMoivre :
        ((Real.cos φ : ℂ) + (Real.sin φ : ℂ) * I) ^ n =
          (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I := by
      have h := Complex.cos_add_sin_mul_I_pow n (φ : ℂ)
      simpa [Complex.ofReal_cos, Complex.ofReal_sin, hφn] using h
    rw [hpow_r, hdeMoivre]
    have hz_decomp : z = (z.re : ℂ) + (z.im : ℂ) * I := by
      apply Complex.ext <;> simp
    rw [hz_decomp]
    have hdist : (r : ℂ) * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I) =
        (r * Real.cos θ : ℝ) + (r * Real.sin θ : ℝ) * I := by
      push_cast
      ring
    rw [hdist, hcos, hsin]
    apply Complex.ext <;> simp [Complex.ofReal_div]
    · field_simp [hrpos.ne']
    · field_simp [hrpos.ne']

/-- `PComplex` is closed under extracting `n`-th roots. -/
theorem PComplex.mem_of_pow_mem {z : ℂ} {n : ℕ} (hn : n ≠ 0)
    (hz : z ^ n ∈ PComplex) : z ∈ PComplex := by
  by_cases hz0 : z = 0
  · subst z
    exact PComplex.zero_mem
  · obtain ⟨w, hwP, hw⟩ := exists_PComplex_nth_root hz hn
    have hwn : w ≠ 0 := by
      intro hw0
      have hzero : z ^ n = 0 := by rw [← hw, hw0, zero_pow hn]
      exact (pow_ne_zero n hz0) hzero
    have hζne : z / w ≠ 0 := div_ne_zero hz0 hwn
    have hζpow : (z / w) ^ n = 1 := by
      rw [div_pow, hw]
      exact div_self (pow_ne_zero n hz0)
    have hζP : PConstructibleC (z / w) := by
      let u : ℂˣ := Units.mk0 (z / w) hζne
      have hu : u ∈ rootsOfUnity n ℂ := by
        rw [mem_rootsOfUnity']
        simpa [u] using hζpow
      haveI : NeZero n := ⟨hn⟩
      obtain ⟨i, hi, hζexp⟩ := (Complex.mem_rootsOfUnity n u).mp hu
      change PConstructibleC (↑u)
      rw [← hζexp]
      have harg : (2 * (Real.pi : ℂ) * I * ((i : ℂ) / (n : ℂ))) =
          ((2 * Real.pi * (i : ℝ) / (n : ℝ) : ℝ) : ℂ) * I := by
        push_cast
        ring
      rw [harg, Complex.exp_ofReal_mul_I]
      have hParg : PConstructible (2 * Real.pi * (i : ℝ) / (n : ℝ)) :=
        PConstructible.div
          (PConstructible.mul (PConstructible.mul (nat_Pconstructible 2) pi_Pconstructible)
            (nat_Pconstructible i))
          (nat_Pconstructible n)
      exact PConstructibleC.add (PConstructibleC.ofReal (cos_Pconstructible hParg))
        (PConstructibleC.mul (PConstructibleC.ofReal (sin_Pconstructible hParg))
          PConstructibleC.I)
    have hz_eq : z = w * (z / w) := by
      field_simp [hwn]
    rw [hz_eq]
    exact PConstructibleC.mul hwP hζP

/-- Every element of the radical closure of `ℚ` in `ℂ` has P-constructible
real and imaginary parts. -/
theorem mem_PComplex_of_mem_solvableByRad {z : ℂ}
    (hz : z ∈ solvableByRad ℚ ℂ) : z ∈ PComplex := by
  refine solvableByRad_le (s := PComplex) ?_ hz
  intro x n hn hx
  exact PComplex.mem_of_pow_mem hn hx

end Pconstructible
