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
import Mathlib.FieldTheory.Finite.Basic

open scoped BigOperators

/-! # From the doubling ratio to every rational argument

Taking the doubling ratio `D(x) = Γ(x)² / Γ(2x)` as a hypothesis (it is proved from the
analytic half-products in `Pptc.GammaRational.HalfShift`), this file reaches `Γ(q)` for every
rational `q`. Four steps, all multiplicative modulo `PConstructible`:

1. `Γ(x) ^ (2 ^ k) / Γ(2 ^ k x) ∈ P` by induction on `k`, squaring the `D`-relation at
   `x, 2x, 4x, …`.
2. *Odd denominator* `x = p/N` with `N` odd: `ℓ = φ(N) ≥ 1` satisfies `N ∣ 2 ^ ℓ - 1`, so
   `2 ^ ℓ x = x + m` with `m ∈ ℕ`; the Pochhammer ratio `Γ(x + m)/Γ(x) = ∏_{i<m} (x + i)`
   is P-constructible, hence `Γ(x) ^ (2 ^ ℓ - 1) ∈ P` is positive and `rpow` with exponent
   `1/(2 ^ ℓ - 1)` recovers `Γ(x)`.
3. *General `q > 0`*: write `q = p / (2 ^ j N)` with `N` odd and induct on `j`, using
   `Γ(q)² = D(q) Γ(2q)` and a square root.
4. *`q ≤ 0`*: shift by an integer with `Gamma_add_intCast_Pconstructible`.

No coprimality of the numerator is needed. -/

namespace Pconstructible

/-! ### Pochhammer shifts

`Γ` satisfies `Γ(x + n) = Γ(x) ∏_{i<n} (x + i)` for `x > 0`. The product on the right is
built from the arithmetic constructors, and it is exactly the ratio the odd-denominator
argument needs. -/

-- Theorem: for `x > 0` and natural `n`, `Γ(x + n) = Γ(x) · ∏_{i<n} (x + i)`.
private lemma Gamma_add_nat_eq_Gamma_mul_prod {x : ℝ} (hx : 0 < x) (n : ℕ) :
    Real.Gamma (x + n) = Real.Gamma x * ∏ i ∈ Finset.range n, (x + i) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hx' : (0 : ℝ) < x + n := by positivity
      rw [Finset.prod_range_succ]
      rw [show x + ((n : ℕ) + 1 : ℕ) = (x + n) + 1 by push_cast; ring]
      rw [Real.Gamma_add_one hx'.ne', ih]
      ring

-- Theorem: the Pochhammer product `∏_{i<n} (x + i)` is P-constructible when `x` is.
private lemma pochhammer_Pconstructible {x : ℝ} (hx : PConstructible x) (n : ℕ) :
    PConstructible (∏ i ∈ Finset.range n, (x + i)) := by
  refine Finset.prod_induction (s := Finset.range n) (fun i => x + i) PConstructible
    (fun a b ha hb => PConstructible.mul ha hb) PConstructible.base_one ?_
  intro i _
  exact PConstructible.add hx (nat_Pconstructible i)

/-! ### Step 3: the iterated doubling relation -/

-- Theorem: `Γ(x) ^ (2 ^ (j + 1)) / Γ(2 ^ (j + 1) x) ∈ P` for rational `x > 0`, by
-- induction on `j`: the step squares the previous relation and multiplies in `D` at
-- `2 ^ (j + 1) x`.
private lemma Gamma_pow_two_pow_div_Pconstructible
    (hdup : ∀ x : ℚ, 0 < x →
      PConstructible (Real.Gamma (x : ℝ) ^ 2 / Real.Gamma (2 * (x : ℝ))))
    (x : ℚ) (hx : 0 < x) (j : ℕ) :
    PConstructible ((Real.Gamma (x : ℝ)) ^ (2 ^ (j + 1)) /
      Real.Gamma ((((2 : ℚ) ^ (j + 1)) * x : ℚ) : ℝ)) := by
  induction j with
  | zero =>
      have h := hdup x hx
      convert h using 1
      push_cast
      norm_num
  | succ j ih =>
      set z : ℚ := (2 : ℚ) ^ (j + 1) * x with hzdef
      have hz : 0 < z := by rw [hzdef]; positivity
      have hzR : 0 < (z : ℝ) := by exact_mod_cast hz
      have hB : Real.Gamma (z : ℝ) ≠ 0 := (Real.Gamma_pos_of_pos hzR).ne'
      have hC : Real.Gamma (2 * (z : ℝ)) ≠ 0 :=
        (Real.Gamma_pos_of_pos (by positivity)).ne'
      have hmul : PConstructible
          ((Real.Gamma (x : ℝ) ^ 2 ^ (j + 1) / Real.Gamma (z : ℝ)) ^ 2 *
            (Real.Gamma (z : ℝ) ^ 2 / Real.Gamma (2 * (z : ℝ)))) :=
        PConstructible.mul (sq_Pconstructible ih) (hdup z hz)
      convert hmul using 1
      have hzc : ((((2 : ℚ) ^ (j + 2)) * x : ℚ) : ℝ) = 2 * (z : ℝ) := by
        rw [hzdef]
        push_cast
        rw [show (2 : ℝ) ^ (j + 2) = (2 : ℝ) ^ (j + 1) * 2 by
              rw [show j + 2 = (j + 1) + 1 by omega, pow_succ]]
        ring
      rw [hzc]
      rw [show (2 : ℕ) ^ (j + 2) = 2 ^ (j + 1) * 2 by
            rw [show j + 2 = (j + 1) + 1 by omega, pow_succ]]
      rw [pow_mul]
      field_simp [hB, hC]

/-! ### Step 4: odd denominators -/

-- Theorem: `Γ(p / N) ∈ P` for every `p` and every odd `N`.
private lemma Gamma_nat_div_odd_Pconstructible
    (hdup : ∀ x : ℚ, 0 < x →
      PConstructible (Real.Gamma (x : ℝ) ^ 2 / Real.Gamma (2 * (x : ℝ))))
    (p N : ℕ) (hN : Odd N) :
    PConstructible (Real.Gamma ((p : ℝ) / (N : ℝ))) := by
  by_cases hp : p = 0
  · subst hp
    rw [Nat.cast_zero, zero_div, Real.Gamma_zero]
    exact zero_Pconstructible
  · have hNpos : 0 < N := hN.pos
    have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast hNpos.ne'
    set q : ℚ := (p : ℚ) / (N : ℚ) with hqdef
    have hqpos : 0 < q := by rw [hqdef]; positivity
    have hqnn : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
    have hqcast : (q : ℝ) = (p : ℝ) / (N : ℝ) := by
      rw [hqdef]; push_cast; ring
    have hℓpos : 0 < Nat.totient N := Nat.totient_pos.mpr hNpos
    have hmod : 2 ^ Nat.totient N ≡ 1 [MOD N] :=
      Nat.ModEq.pow_totient (Nat.coprime_two_left.mpr hN)
    obtain ⟨m, hm⟩ := hmod.symm.dvd'
    have hpow : 2 ^ Nat.totient N = N * m + 1 := by
      have h1 : 1 ≤ 2 ^ Nat.totient N := Nat.one_le_two_pow
      omega
    -- the shift `2 ^ ℓ · q = q + m * p`
    have hshift : (((2 : ℚ) ^ Nat.totient N * q : ℚ) : ℝ) =
        (q : ℝ) + ((m * p : ℕ) : ℝ) := by
      push_cast
      rw [hqcast]
      have hpowR : (2 : ℝ) ^ Nat.totient N = (N : ℝ) * (m : ℝ) + 1 := by
        exact_mod_cast hpow
      rw [hpowR]
      field_simp
      ring
    have hL1 := Gamma_pow_two_pow_div_Pconstructible hdup q hqpos (Nat.totient N - 1)
    rw [Nat.sub_add_cancel hℓpos] at hL1
    rw [hshift] at hL1
    have hProd : PConstructible (∏ i ∈ Finset.range (m * p), ((q : ℝ) + i)) :=
      pochhammer_Pconstructible (rat_Pconstructible q) (m * p)
    have hProdne : (∏ i ∈ Finset.range (m * p), ((q : ℝ) + i)) ≠ 0 :=
      (Finset.prod_pos (fun i _ => by positivity)).ne'
    have hΓne : Real.Gamma (q : ℝ) ≠ 0 := (Real.Gamma_pos_of_pos hqnn).ne'
    have hrec : Real.Gamma ((q : ℝ) + ((m * p : ℕ) : ℝ)) =
        Real.Gamma (q : ℝ) * ∏ i ∈ Finset.range (m * p), ((q : ℝ) + i) :=
      Gamma_add_nat_eq_Gamma_mul_prod hqnn (m * p)
    have hsq : PConstructible (Real.Gamma (q : ℝ) ^ (2 ^ Nat.totient N - 1)) := by
      have hmul := PConstructible.mul hL1 hProd
      convert hmul using 1
      rw [hrec]
      have hpow2 : 2 ^ Nat.totient N = (2 ^ Nat.totient N - 1) + 1 :=
        (Nat.sub_add_cancel (Nat.one_le_two_pow : 1 ≤ 2 ^ Nat.totient N)).symm
      rw [hpow2, pow_succ]
      field_simp [hΓne, hProdne]
      rw [Nat.add_sub_cancel]
    have hnpos : 0 < 2 ^ Nat.totient N - 1 := by
      have h1 : 1 < 2 ^ Nat.totient N := Nat.one_lt_two_pow hℓpos.ne'
      omega
    have hroot := rpow_Pconstructible (a := Real.Gamma (q : ℝ) ^ (2 ^ Nat.totient N - 1))
      (b := (1 : ℝ) / ((2 ^ Nat.totient N - 1 : ℕ) : ℝ)) hsq
      (PConstructible.div PConstructible.base_one (nat_Pconstructible _))
      (pow_pos (Real.Gamma_pos_of_pos hqnn) _)
    rw [← hqcast]
    rw [← Real.rpow_natCast (Real.Gamma (q : ℝ)) (2 ^ Nat.totient N - 1),
      ← Real.rpow_mul (Real.Gamma_pos_of_pos hqnn).le,
      show (((2 ^ Nat.totient N - 1 : ℕ) : ℝ)) *
          ((1 : ℝ) / ((2 ^ Nat.totient N - 1 : ℕ) : ℝ)) = 1 by
        rw [mul_one_div, div_self]
        exact_mod_cast hnpos.ne',
      Real.rpow_one] at hroot
    exact hroot

/-! ### Step 5: general positive rank

Writing `q = p / (2 ^ j N)` with `N` odd, `Γ(q)² = D(q) Γ(2q)` expresses `Γ(q)²` through
`Γ` at one lower power of two; a square root (`Γ(q) > 0`) recovers `Γ(q)`. -/

-- Theorem: `Γ(p / (2 ^ j · N)) ∈ P` for every `p`, every odd `N` and every `j`.
private lemma Gamma_nat_div_two_pow_mul_Pconstructible
    (hdup : ∀ x : ℚ, 0 < x →
      PConstructible (Real.Gamma (x : ℝ) ^ 2 / Real.Gamma (2 * (x : ℝ))))
    (p N : ℕ) (hN : Odd N) (j : ℕ) :
    PConstructible (Real.Gamma ((p : ℝ) / ((2 : ℝ) ^ j * (N : ℝ)))) := by
  induction j with
  | zero =>
      simpa using Gamma_nat_div_odd_Pconstructible hdup p N hN
  | succ j ih =>
      by_cases hp : p = 0
      · subst hp
        rw [Nat.cast_zero, zero_div, Real.Gamma_zero]
        exact zero_Pconstructible
      · have hNpos : 0 < N := hN.pos
        set q : ℚ := (p : ℚ) / ((2 : ℚ) ^ (j + 1) * (N : ℚ)) with hqdef
        have hqpos : 0 < q := by rw [hqdef]; positivity
        have hqnn : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
        have hqcast : (q : ℝ) = (p : ℝ) / ((2 : ℝ) ^ (j + 1) * (N : ℝ)) := by
          rw [hqdef]; push_cast; ring
        have hd := hdup q hqpos
        have h2q : (2 : ℝ) * (q : ℝ) = (p : ℝ) / ((2 : ℝ) ^ j * (N : ℝ)) := by
          rw [hqcast]
          rw [show (2 : ℝ) ^ (j + 1) = (2 : ℝ) ^ j * 2 by rw [pow_succ]]
          field_simp
        have hih : PConstructible (Real.Gamma (2 * (q : ℝ))) := by
          rw [h2q]; exact ih
        have hsq : PConstructible (Real.Gamma (q : ℝ) ^ 2) := by
          have hm := PConstructible.mul hd hih
          convert hm using 1
          exact (div_mul_cancel₀ _ (Real.Gamma_pos_of_pos (by positivity)).ne').symm
        have hsqr := sqrt_Pconstructible hsq
        rw [← hqcast]
        rwa [Real.sqrt_sq (Real.Gamma_pos_of_pos hqnn).le] at hsqr

/-! ### Step 6: positive rationals, then the integer shift -/

-- Theorem: `Γ(q) ∈ P` for every positive rational `q`.
private lemma Gamma_rat_pos_Pconstructible
    (hdup : ∀ x : ℚ, 0 < x →
      PConstructible (Real.Gamma (x : ℝ) ^ 2 / Real.Gamma (2 * (x : ℝ))))
    (q : ℚ) (hq : 0 < q) :
    PConstructible (Real.Gamma (q : ℝ)) := by
  obtain ⟨j, N, hNodd, hden⟩ := Nat.exists_eq_two_pow_mul_odd q.den_nz
  have hp : ((q.num.toNat : ℤ) = q.num) := Int.toNat_of_nonneg (Rat.num_pos.mpr hq).le
  have hcast : (q : ℝ) = (q.num.toNat : ℝ) / ((2 : ℝ) ^ j * (N : ℝ)) := by
    rw [Rat.cast_def, hden,
      show (((2 ^ j * N : ℕ)) : ℝ) = (2 : ℝ) ^ j * (N : ℝ) by push_cast; ring,
      show (q.num.toNat : ℝ) = (q.num : ℝ) by exact_mod_cast hp]
  rw [hcast]
  exact Gamma_nat_div_two_pow_mul_Pconstructible hdup q.num.toNat N hNodd j

-- Theorem: `Γ` is P-constructible at every rational, given the doubling ratio.
theorem Gamma_rat_Pconstructible_of_dup
    (hdup : ∀ x : ℚ, 0 < x → PConstructible (Real.Gamma (x : ℝ) ^ 2 / Real.Gamma (2 * (x : ℝ))))
    (q : ℚ) : PConstructible (Real.Gamma (q : ℝ)) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 - q : ℚ)
  have hpos : 0 < q + (N : ℚ) := by linarith
  have hΓ : PConstructible (Real.Gamma (((q + (N : ℚ) : ℚ) : ℝ))) :=
    Gamma_rat_pos_Pconstructible hdup (q + N) hpos
  have hx : PConstructible (((q + (N : ℚ) : ℚ) : ℝ)) := rat_Pconstructible _
  have hshift := Gamma_add_intCast_Pconstructible hx hΓ (-(N : ℤ))
  have harg : (((q + (N : ℚ) : ℚ) : ℝ) + (((-(N : ℤ)) : ℤ) : ℝ)) = (q : ℝ) := by
    push_cast; ring
  rw [harg] at hshift
  exact hshift

end Pconstructible
