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
import Mathlib.RingTheory.Polynomial.Vieta
import Pptc.DegreeSeven
import Pptc.TotallyReal.Engines

/-! # Pptc.TotallyReal.Newton

**Lemma N of `TotallyReal/PLAN.md` §2.1**: vanishing *odd* power sums force vanishing
*odd* elementary symmetric functions, `e₁ = e₃ = e₅ = 0`, with no sign obstruction.

This is the whole reason the totally real degree-7 and degree-8 cases work. `DegreeSeven`
already kills `p₁, p₂, p₃` to get `e₁, e₂, e₃` away, but for real roots `p₂ = Σβᵢ² > 0`
is a hard obstruction: a totally real septic has no `e₂ = 0`, and the "xⁿ = cubic"
engines are correspondingly out of reach. Going to odd indices instead dodges that:
`Σyᵢ³` and `Σyᵢ⁵` carry no sign constraint for real `yᵢ`.

## Why the polynomial shape follows

For `y : Fin n → ℝ` the characteristic polynomial of the Tschirnhaus image is
`prodSubY y = ∏ᵢ (X − yᵢ)`, a *monic* polynomial of degree `n` with

    (prodSubY y).coeff (n − k) = (−1)^k · e_k(y).

Killing `e₁`, `e₃`, `e₅` therefore kills `coeff (n−1)`, `coeff (n−3)`, `coeff (n−5)`, and

- for `n = 7` only the odd powers `t⁷, t⁵, t³, t` survive, so
  `χ(t) = t·(t⁶ + r₂t⁴ + r₁t² + r₀) − e₇ = t·R(t²) − e₇` with `R` a monic cubic;
- for `n = 8` only the even powers survive, so
  `χ(t) = t⁸ + q₃t⁶ + q₂t⁴ + q₁t² + q₀ − e₇t = Q(t²) − e₇·t` with `Q` a monic quartic.

Those two factorisations are what `Engines.lean` then inverts. The two `exists_…` theorems
below are the shape lemmas; the engine is stated directly on them.
-/

namespace Pconstructible

open Polynomial

/-! ### The remaining Newton identities -/

/-- Newton's identity for `k = 4`, in the same shape as `two_mul_esymm_two` and
`three_mul_esymm_three`:

    k · e_k = Σᵢ₌₁..ₖ (−1)^(i−1) · e_{k−i} · p_i. -/
theorem four_mul_esymm_four (s : Multiset ℂ) :
    4 * s.esymm 4 = s.esymm 3 * s.sum - s.esymm 2 * (s.map (fun z => z ^ 2)).sum
      + s.esymm 1 * (s.map (fun z => z ^ 3)).sum - (s.map (fun z => z ^ 4)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [Multiset.esymm, Multiset.powersetCard_zero_right]
  | cons a s ih =>
      rw [show (a ::ₘ s).esymm 4 = s.esymm 4 + a * s.esymm 3 from esymm_cons a s 3,
        show (a ::ₘ s).esymm 3 = s.esymm 3 + a * s.esymm 2 from esymm_cons a s 2,
        show (a ::ₘ s).esymm 2 = s.esymm 2 + a * s.esymm 1 from esymm_cons a s 1,
        show (a ::ₘ s).esymm 1 = s.esymm 1 + a * s.esymm 0 from esymm_cons a s 0,
        esymm_zero, mul_one]
      rw [Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons, Multiset.map_cons,
        Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons]
      have h1 := esymm_one_eq_sum s
      have h3 := three_mul_esymm_three s
      rw [h1] at ih h3 ⊢
      linear_combination ih + a * h3

/-- Newton's identity for `k = 5`. -/
theorem five_mul_esymm_five (s : Multiset ℂ) :
    5 * s.esymm 5 = s.esymm 4 * s.sum - s.esymm 3 * (s.map (fun z => z ^ 2)).sum
      + s.esymm 2 * (s.map (fun z => z ^ 3)).sum
      - s.esymm 1 * (s.map (fun z => z ^ 4)).sum
      + (s.map (fun z => z ^ 5)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [Multiset.esymm, Multiset.powersetCard_zero_right]
  | cons a s ih =>
      rw [show (a ::ₘ s).esymm 5 = s.esymm 5 + a * s.esymm 4 from esymm_cons a s 4,
        show (a ::ₘ s).esymm 4 = s.esymm 4 + a * s.esymm 3 from esymm_cons a s 3,
        show (a ::ₘ s).esymm 3 = s.esymm 3 + a * s.esymm 2 from esymm_cons a s 2,
        show (a ::ₘ s).esymm 2 = s.esymm 2 + a * s.esymm 1 from esymm_cons a s 1,
        show (a ::ₘ s).esymm 1 = s.esymm 1 + a * s.esymm 0 from esymm_cons a s 0,
        esymm_zero, mul_one]
      rw [Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons, Multiset.map_cons,
        Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons, Multiset.map_cons,
        Multiset.sum_cons]
      have h1 := esymm_one_eq_sum s
      have h4 := four_mul_esymm_four s
      rw [h1] at ih h4 ⊢
      linear_combination ih + a * h4

/-- **Lemma N.** Vanishing odd power sums force vanishing odd elementary symmetric
functions. -/
theorem esymm_odd_eq_zero_of_psum_odd_zero (s : Multiset ℂ)
    (h1 : s.sum = 0) (h3 : (s.map (fun z => z ^ 3)).sum = 0)
    (h5 : (s.map (fun z => z ^ 5)).sum = 0) :
    s.esymm 1 = 0 ∧ s.esymm 3 = 0 ∧ s.esymm 5 = 0 := by
  have e1 : s.esymm 1 = 0 := by rw [esymm_one_eq_sum, h1]
  have e3 : s.esymm 3 = 0 := by
    have h := three_mul_esymm_three s
    rw [e1, h1, h3] at h
    simpa using h
  have e5 : s.esymm 5 = 0 := by
    have h := five_mul_esymm_five s
    rw [e1, e3, h1, h3, h5] at h
    simpa using h
  exact ⟨e1, e3, e5⟩

/-! ### The same identities in an arbitrary commutative ring

`Multiset.esymm` only needs a commutative semiring, and none of the proofs divide, so the
whole development goes through verbatim for `R` instead of `ℂ`.  This is the form the
finite-vector argument below needs. -/

/-- `e₀ = 1` in any commutative ring. -/
theorem esymm_zero' {R : Type*} [CommRing R] (s : Multiset R) : s.esymm 0 = 1 := by
  simp [Multiset.esymm, Multiset.powersetCard_zero_left]

/-- The recurrence `e_{n+1}(a :: s) = e_{n+1}(s) + a · e_n(s)` in any commutative ring. -/
theorem esymm_cons' {R : Type*} [CommRing R] (a : R) (s : Multiset R) (n : ℕ) :
    (a ::ₘ s).esymm (n + 1) = s.esymm (n + 1) + a * s.esymm n := by
  simp only [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_add, Multiset.sum_add,
    Multiset.map_map, Multiset.prod_cons, Function.comp_apply, Multiset.sum_map_mul_left]

/-- `e₁ = p₁` in any commutative ring. -/
theorem esymm_one_eq_sum' {R : Type*} [CommRing R] (s : Multiset R) : s.esymm 1 = s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp [Multiset.esymm, Multiset.powersetCard_zero_right]
  | cons a s ih =>
      rw [show (a ::ₘ s).esymm 1 = s.esymm 1 + a * s.esymm 0 from esymm_cons' a s 0,
        esymm_zero', mul_one]
      rw [ih, Multiset.sum_cons]
      ring

/-- `2 e₂ = e₁ p₁ − p₂` in any commutative ring. -/
theorem two_mul_esymm_two' {R : Type*} [CommRing R] (s : Multiset R) :
    2 * s.esymm 2 = s.esymm 1 * s.sum - (s.map (fun z => z ^ 2)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [Multiset.esymm, Multiset.powersetCard_zero_right]
  | cons a s ih =>
      rw [show (a ::ₘ s).esymm 2 = s.esymm 2 + a * s.esymm 1 from esymm_cons' a s 1,
        show (a ::ₘ s).esymm 1 = s.esymm 1 + a * s.esymm 0 from esymm_cons' a s 0,
        esymm_zero', mul_one]
      rw [Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons]
      have h1 := esymm_one_eq_sum' s
      rw [h1] at ih ⊢
      linear_combination ih

/-- `3 e₃ = p₃ − e₁ p₂ + e₂ p₁` in any commutative ring. -/
theorem three_mul_esymm_three' {R : Type*} [CommRing R] (s : Multiset R) :
    3 * s.esymm 3 = (s.map (fun z => z ^ 3)).sum - s.esymm 1 * (s.map (fun z => z ^ 2)).sum
      + s.esymm 2 * s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp [Multiset.esymm, Multiset.powersetCard_zero_right]
  | cons a s ih =>
      rw [show (a ::ₘ s).esymm 3 = s.esymm 3 + a * s.esymm 2 from esymm_cons' a s 2,
        show (a ::ₘ s).esymm 2 = s.esymm 2 + a * s.esymm 1 from esymm_cons' a s 1,
        show (a ::ₘ s).esymm 1 = s.esymm 1 + a * s.esymm 0 from esymm_cons' a s 0,
        esymm_zero', mul_one]
      rw [Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons, Multiset.map_cons,
        Multiset.sum_cons]
      have h1 := esymm_one_eq_sum' s
      have h2 := two_mul_esymm_two' s
      rw [h1] at ih h2 ⊢
      linear_combination ih + a * h2

/-- `4 e₄ = e₃ p₁ − e₂ p₂ + e₁ p₃ − p₄` in any commutative ring. -/
theorem four_mul_esymm_four' {R : Type*} [CommRing R] (s : Multiset R) :
    4 * s.esymm 4 = s.esymm 3 * s.sum - s.esymm 2 * (s.map (fun z => z ^ 2)).sum
      + s.esymm 1 * (s.map (fun z => z ^ 3)).sum - (s.map (fun z => z ^ 4)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [Multiset.esymm, Multiset.powersetCard_zero_right]
  | cons a s ih =>
      rw [show (a ::ₘ s).esymm 4 = s.esymm 4 + a * s.esymm 3 from esymm_cons' a s 3,
        show (a ::ₘ s).esymm 3 = s.esymm 3 + a * s.esymm 2 from esymm_cons' a s 2,
        show (a ::ₘ s).esymm 2 = s.esymm 2 + a * s.esymm 1 from esymm_cons' a s 1,
        show (a ::ₘ s).esymm 1 = s.esymm 1 + a * s.esymm 0 from esymm_cons' a s 0,
        esymm_zero', mul_one]
      rw [Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons, Multiset.map_cons,
        Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons]
      have h1 := esymm_one_eq_sum' s
      have h3 := three_mul_esymm_three' s
      rw [h1] at ih h3 ⊢
      linear_combination ih + a * h3

/-- `5 e₅ = e₄ p₁ − e₃ p₂ + e₂ p₃ − e₁ p₄ + p₅` in any commutative ring. -/
theorem five_mul_esymm_five' {R : Type*} [CommRing R] (s : Multiset R) :
    5 * s.esymm 5 = s.esymm 4 * s.sum - s.esymm 3 * (s.map (fun z => z ^ 2)).sum
      + s.esymm 2 * (s.map (fun z => z ^ 3)).sum
      - s.esymm 1 * (s.map (fun z => z ^ 4)).sum
      + (s.map (fun z => z ^ 5)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [Multiset.esymm, Multiset.powersetCard_zero_right]
  | cons a s ih =>
      rw [show (a ::ₘ s).esymm 5 = s.esymm 5 + a * s.esymm 4 from esymm_cons' a s 4,
        show (a ::ₘ s).esymm 4 = s.esymm 4 + a * s.esymm 3 from esymm_cons' a s 3,
        show (a ::ₘ s).esymm 3 = s.esymm 3 + a * s.esymm 2 from esymm_cons' a s 2,
        show (a ::ₘ s).esymm 2 = s.esymm 2 + a * s.esymm 1 from esymm_cons' a s 1,
        show (a ::ₘ s).esymm 1 = s.esymm 1 + a * s.esymm 0 from esymm_cons' a s 0,
        esymm_zero', mul_one]
      rw [Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons, Multiset.map_cons,
        Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons, Multiset.map_cons,
        Multiset.sum_cons]
      have h1 := esymm_one_eq_sum' s
      have h4 := four_mul_esymm_four' s
      rw [h1] at ih h4 ⊢
      linear_combination ih + a * h4

/-- **Lemma N, in an arbitrary commutative ring.** Vanishing odd power sums force vanishing
odd elementary symmetric functions.  The `IsDomain` and `CharZero` hypotheses are exactly
what is needed to cancel the `3` and `5`; nothing else in the proof needs them. -/
theorem esymm_odd_eq_zero_of_psum_odd_zero' {R : Type*} [CommRing R] [CharZero R]
    [IsDomain R] (s : Multiset R) (h1 : s.sum = 0) (h3 : (s.map (fun z => z ^ 3)).sum = 0)
    (h5 : (s.map (fun z => z ^ 5)).sum = 0) :
    s.esymm 1 = 0 ∧ s.esymm 3 = 0 ∧ s.esymm 5 = 0 := by
  have e1 : s.esymm 1 = 0 := by rw [esymm_one_eq_sum', h1]
  have e3 : s.esymm 3 = 0 := by
    have h := three_mul_esymm_three' s
    rw [e1, h1, h3] at h
    have h3' : (3 : R) * s.esymm 3 = 0 := by linear_combination h
    exact (mul_eq_zero.mp h3').resolve_left (Nat.cast_ne_zero.mpr (by norm_num))
  have e5 : s.esymm 5 = 0 := by
    have h := five_mul_esymm_five' s
    rw [e1, e3, h1, h3, h5] at h
    have h5' : (5 : R) * s.esymm 5 = 0 := by linear_combination h
    exact (mul_eq_zero.mp h5').resolve_left (Nat.cast_ne_zero.mpr (by norm_num))
  exact ⟨e1, e3, e5⟩

/-- The real version of `esymm_odd_eq_zero_of_psum_odd_zero`, which is what the
finite-vector formulation below is actually derived from. -/
theorem esymm_odd_eq_zero_of_psum_odd_zero_real (s : Multiset ℝ)
    (h1 : s.sum = 0) (h3 : (s.map (fun z => z ^ 3)).sum = 0)
    (h5 : (s.map (fun z => z ^ 5)).sum = 0) :
    s.esymm 1 = 0 ∧ s.esymm 3 = 0 ∧ s.esymm 5 = 0 :=
  esymm_odd_eq_zero_of_psum_odd_zero' s h1 h3 h5

/-! ### From a multiset to a finite list of numbers -/

/-- The multiset of the entries of `y : Fin n → ℝ`, as a `Multiset ℝ`. Its `esymm k` is
the elementary symmetric function `e_k(y)`. -/
def multisetOfY {n : ℕ} (y : Fin n → ℝ) : Multiset ℝ :=
  ((List.finRange n).map y : List ℝ)

/-- The `m`-th power sum of the entries of `y : Fin n → ℝ`. -/
def psumFinY {n : ℕ} (y : Fin n → ℝ) (m : ℕ) : ℝ := ∑ i, y i ^ m

@[pconstructible]
theorem psumFinY_Pconstructible {n : ℕ} {y : Fin n → ℝ} (hy : ∀ i, PConstructible (y i))
    (m : ℕ) : PConstructible (psumFinY y m) := by
  simp only [psumFinY]
  refine Finset.sum_induction _ PConstructible (fun _ _ ha hb => PConstructible.add ha hb)
    zero_Pconstructible (fun i _ => ?_)
  exact pow_Pconstructible (hy i) m

/-- The power sum of the multiset of entries of `y` is the power sum over `Fin n`. -/
theorem psum_multisetOfY {n : ℕ} (y : Fin n → ℝ) (m : ℕ) :
    ((multisetOfY y).map (fun z : ℝ => z ^ m)).sum = psumFinY y m := by
  calc ((multisetOfY y).map (fun z : ℝ => z ^ m)).sum
      = (((List.finRange n) : Multiset (Fin n)).map (fun i : Fin n => y i ^ m)).sum := by
        unfold multisetOfY
        rw [← Multiset.map_coe, Multiset.map_map]
        rfl
    _ = ∑ i : Fin n, y i ^ m :=
      Finset.sum_map_val (Finset.univ : Finset (Fin n)) (fun i : Fin n => y i ^ m)
    _ = psumFinY y m := rfl

/-! ### The characteristic polynomial of a finite list of numbers -/

/-- `∏ᵢ (X − yᵢ)`: the characteristic polynomial of a `y`-vector. Monic of degree `n`. -/
noncomputable def prodSubY {n : ℕ} (y : Fin n → ℝ) : ℝ[X] := ∏ i : Fin n, (X - C (y i))

theorem prodSubY_monic {n : ℕ} (y : Fin n → ℝ) : (prodSubY y).Monic := by
  have h : (∏ i : Fin n, (X - C (y i))).Monic := by
    classical
    refine Finset.prod_induction (fun i : Fin n => X - C (y i)) Monic
      (fun _ _ ha hb => ha.mul hb) Polynomial.monic_one (fun i _ => ?_)
    exact Polynomial.monic_X_sub_C _
  exact h

theorem prodSubY_natDegree {n : ℕ} (y : Fin n → ℝ) : (prodSubY y).natDegree = n := by
  have h : (∏ i : Fin n, (X - C (y i))).natDegree = n := by
    classical
    calc (∏ i : Fin n, (X - C (y i))).natDegree
        = ∑ i : Fin n, (X - C (y i)).natDegree :=
          Polynomial.natDegree_prod_of_monic (Finset.univ : Finset (Fin n))
            (fun i : Fin n => X - C (y i)) fun i _ => Polynomial.monic_X_sub_C _
      _ = n := by simp
  exact h

/-- Every entry of `y` is a root of `prodSubY y`. -/
theorem eval_prodSubY {n : ℕ} (y : Fin n → ℝ) (i : Fin n) : (prodSubY y).eval (y i) = 0 := by
  classical
  change ((∏ j : Fin n, (X - C (y j))) : ℝ[X]).eval (y i) = 0
  rw [eval_prod]
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  simp [eval_sub, eval_X, eval_C]

/-- The product over a `Finset` of linear factors vanishes at each of the points. -/
theorem eval_prodSubY_of_mem {n : ℕ} (y : Fin n → ℝ) {x : ℝ} (hx : x ∈ Set.range y) :
    (prodSubY y).eval x = 0 := by
  obtain ⟨i, rfl⟩ := hx
  exact eval_prodSubY y i

/-- `coeff (n − k) = (−1)^k e_k(y)`, the link between the elementary symmetric functions
and the coefficients of the characteristic polynomial. -/
theorem coeff_prodSubY {n : ℕ} (y : Fin n → ℝ) {k : ℕ} (hk : k ≤ n) :
    (prodSubY y).coeff (n - k) = if k % 2 = 0 then (multisetOfY y).esymm k
      else -((multisetOfY y).esymm k) := by
  have hkey : (prodSubY y).coeff (n - k) = (-1 : ℝ) ^ k * (multisetOfY y).esymm k := by
    have hv : ((∏ i : Fin n, (X + C (-y i))) : ℝ[X]).coeff (n - k)
        = ((Finset.univ : Finset (Fin n)).val.map (fun i : Fin n => -y i)).esymm
          ((Finset.univ : Finset (Fin n)).card - (n - k)) := by
      classical
      rw [Finset.prod_X_add_C_coeff (Finset.univ : Finset (Fin n))
        (fun i : Fin n => -y i) (by rw [Finset.card_univ, Fintype.card_fin]; omega)]
      exact (Finset.esymm_map_val (fun i : Fin n => -y i)
        (Finset.univ : Finset (Fin n)) _).symm
    have hms : (multisetOfY y).map (fun z : ℝ => -z)
        = ((Finset.univ : Finset (Fin n)).val.map (fun i : Fin n => -y i)) := by
      unfold multisetOfY
      rw [← Multiset.map_coe, Multiset.map_map]
      rfl
    have hsub : n - (n - k) = k := by omega
    change ((∏ i : Fin n, (X - C (y i))) : ℝ[X]).coeff (n - k)
      = (-1 : ℝ) ^ k * (multisetOfY y).esymm k
    rw [show (∏ i : Fin n, (X - C (y i))) = ∏ i : Fin n, (X + C (-y i)) by
      simp only [sub_eq_add_neg, map_neg], hv, Finset.card_univ, Fintype.card_fin, ← hms,
      Multiset.esymm_neg, hsub]
  rw [hkey]
  rcases Nat.mod_two_eq_zero_or_one k with hk0 | hk1
  · rw [if_pos hk0, Even.neg_one_pow (Nat.even_iff.mpr hk0), one_mul]
  · have hodd : Odd k := by
      by_contra h
      exact (by omega : ¬ k % 2 = 0) (Nat.not_odd_iff.mp h)
    rw [if_neg (by omega : ¬ k % 2 = 0), Odd.neg_one_pow hodd, neg_one_mul]

/-- **Lemma N, in `Fin n` form.** Odd power sums vanishing forces the odd-indexed
coefficients of the characteristic polynomial to vanish. -/
theorem prodSubY_coeff_odd_eq_zero {n : ℕ} (y : Fin n → ℝ)
    (h1 : psumFinY y 1 = 0) (h3 : psumFinY y 3 = 0) (h5 : psumFinY y 5 = 0)
    (h5n : 5 ≤ n) :
    (prodSubY y).coeff (n - 1) = 0 ∧ (prodSubY y).coeff (n - 3) = 0 ∧
      (prodSubY y).coeff (n - 5) = 0 := by
  have hs : (multisetOfY y).sum = 0 := by
    have h := psum_multisetOfY y 1
    rw [h1] at h
    simpa using h
  have hs3 : ((multisetOfY y).map (fun z : ℝ => z ^ 3)).sum = 0 := by
    have h := psum_multisetOfY y 3
    rw [h3] at h
    simpa using h
  have hs5 : ((multisetOfY y).map (fun z : ℝ => z ^ 5)).sum = 0 := by
    have h := psum_multisetOfY y 5
    rw [h5] at h
    simpa using h
  have hz := esymm_odd_eq_zero_of_psum_odd_zero_real (multisetOfY y) hs hs3 hs5
  refine ⟨?_, ?_, ?_⟩
  · rw [coeff_prodSubY y (by omega), if_neg (by omega), hz.1, neg_zero]
  · rw [coeff_prodSubY y (by omega), if_neg (by omega), hz.2.1, neg_zero]
  · rw [coeff_prodSubY y (by omega), if_neg (by omega), hz.2.2, neg_zero]

/-! ### The two shapes: `t · R(t²) − e₇` and `Q(t²) − e₇ · t` -/

/-- **Septic shape.** If seven reals have vanishing odd power sums then their
characteristic polynomial is `χ(t) = t · R(t²) − e₇` with `R` a monic cubic. -/
theorem exists_cubic_seven {y : Fin 7 → ℝ} (h1 : psumFinY y 1 = 0) (h3 : psumFinY y 3 = 0)
    (h5 : psumFinY y 5 = 0) :
    ∃ (e₇ : ℝ) (r₀ r₁ r₂ : ℝ), ∀ t : ℝ,
      (prodSubY y).eval t = t * cubicVal r₀ r₁ r₂ 1 (t ^ 2) - e₇ := by
  obtain ⟨hc6, hc4, hc2⟩ := prodSubY_coeff_odd_eq_zero y h1 h3 h5 (by norm_num)
  have hnd : (prodSubY y).natDegree = 7 := prodSubY_natDegree y
  refine ⟨-(prodSubY y).coeff 0, (prodSubY y).coeff 1, (prodSubY y).coeff 3,
    (prodSubY y).coeff 5, ?_⟩
  intro t
  have htop : (prodSubY y).coeff 7 = 1 := by
    simpa [hnd] using (prodSubY_monic y).coeff_natDegree
  have hc2' : (prodSubY y).coeff 2 = 0 := hc2
  have hc4' : (prodSubY y).coeff 4 = 0 := hc4
  have hc6' : (prodSubY y).coeff 6 = 0 := hc6
  have hsum : (Finset.range 8).sum (fun k => (prodSubY y).coeff k * t ^ k)
      = (prodSubY y).coeff 0 * t ^ 0 + (prodSubY y).coeff 1 * t ^ 1
        + (prodSubY y).coeff 3 * t ^ 3 + (prodSubY y).coeff 5 * t ^ 5
        + (prodSubY y).coeff 7 * t ^ 7 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [hc2', hc4', hc6']
    ring
  have key : (prodSubY y).eval t
      = (prodSubY y).coeff 0 + (prodSubY y).coeff 1 * t
        + (prodSubY y).coeff 3 * t ^ 3 + (prodSubY y).coeff 5 * t ^ 5 + t ^ 7 := by
    rw [eval_eq_sum_range, hnd, hsum, htop]
    ring
  rw [key]
  simp only [cubicVal]
  ring

/-- **Octic shape.** If eight reals have vanishing odd power sums then their
characteristic polynomial is `χ(t) = Q(t²) − e₇ · t` with `Q` a monic quartic. -/
theorem exists_quartic_eight {y : Fin 8 → ℝ} (h1 : psumFinY y 1 = 0)
    (h3 : psumFinY y 3 = 0) (h5 : psumFinY y 5 = 0) :
    ∃ (e₇ : ℝ) (q₀ q₁ q₂ q₃ : ℝ), ∀ t : ℝ,
      (prodSubY y).eval t = quarticVal q₀ q₁ q₂ q₃ 1 (t ^ 2) - e₇ * t := by
  obtain ⟨hc7, hc5, hc3⟩ := prodSubY_coeff_odd_eq_zero y h1 h3 h5 (by norm_num)
  have hnd : (prodSubY y).natDegree = 8 := prodSubY_natDegree y
  refine ⟨-(prodSubY y).coeff 1, (prodSubY y).coeff 0, (prodSubY y).coeff 2,
    (prodSubY y).coeff 4, (prodSubY y).coeff 6, ?_⟩
  intro t
  have htop : (prodSubY y).coeff 8 = 1 := by
    simpa [hnd] using (prodSubY_monic y).coeff_natDegree
  have hc3' : (prodSubY y).coeff 3 = 0 := hc3
  have hc5' : (prodSubY y).coeff 5 = 0 := hc5
  have hc7' : (prodSubY y).coeff 7 = 0 := hc7
  have hsum : (Finset.range 9).sum (fun k => (prodSubY y).coeff k * t ^ k)
      = (prodSubY y).coeff 0 * t ^ 0 + (prodSubY y).coeff 1 * t ^ 1
        + (prodSubY y).coeff 2 * t ^ 2 + (prodSubY y).coeff 4 * t ^ 4
        + (prodSubY y).coeff 6 * t ^ 6 + (prodSubY y).coeff 8 * t ^ 8 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [hc3', hc5', hc7']
    ring
  have key : (prodSubY y).eval t
      = (prodSubY y).coeff 0 + (prodSubY y).coeff 1 * t
        + (prodSubY y).coeff 2 * t ^ 2 + (prodSubY y).coeff 4 * t ^ 4
        + (prodSubY y).coeff 6 * t ^ 6 + t ^ 8 := by
    rw [eval_eq_sum_range, hnd, hsum, htop]
    ring
  rw [key]
  simp only [quarticVal]
  ring

end Pconstructible
