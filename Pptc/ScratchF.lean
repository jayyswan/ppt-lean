import Pptc.ScratchD
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly

open Polynomial Matrix

namespace Pconstructible

noncomputable section

/-- The standard basis vector `eₖ`. -/
def e7 (k : Fin 7) : Fin 7 → ℝ := Pi.single k 1

@[simp] theorem e7_apply_self (k : Fin 7) : e7 k k = 1 := Pi.single_eq_same k 1

theorem e7_apply_ne {i k : Fin 7} (h : i ≠ k) : e7 k i = 0 := Pi.single_eq_of_ne h 1

theorem e7_ext {k l : Fin 7} (h : k = l) : e7 k = e7 l := by rw [h]

/-- The same vector, totalized in the index, so it can appear in `Finset.range` sums. -/
def eb (i : ℕ) : Fin 7 → ℝ := if h : i < 7 then e7 ⟨i, h⟩ else 0

theorem eb_eq_e7 (i : ℕ) (h : i < 7) : eb i = e7 ⟨i, h⟩ := by rw [eb, dif_pos h]

theorem eb_val (j : Fin 7) : eb j.val = e7 j := by rw [eb_eq_e7 j.val j.isLt]

/-- The transpose of the companion matrix shifts the standard basis up. -/
theorem transpose_companion7_mulVec_e7_succ (q : ℝ[X]) (k : Fin 7) (hk : k.val < 6) :
    (companion7 q)ᵀ *ᵥ e7 k = e7 ⟨k.val + 1, by omega⟩ := by
  change (companion7 q)ᵀ *ᵥ Pi.single k 1 = e7 ⟨k.val + 1, by omega⟩
  rw [Matrix.mulVec_single_one]
  funext i
  rw [Matrix.col_apply, Matrix.transpose_apply, companion7_apply]
  have hk6 : k.val ≠ 6 := by omega
  rw [if_neg hk6]
  by_cases h : i = ⟨k.val + 1, by omega⟩
  · subst h; rw [if_pos rfl, e7_apply_self]
  · rw [e7_apply_ne h]
    have hne : i.val ≠ k.val + 1 := fun hv => h (Fin.ext hv)
    rw [if_neg hne]

/-- The transpose of the companion matrix on the last basis vector. -/
theorem transpose_companion7_mulVec_e7_last (q : ℝ[X]) :
    (companion7 q)ᵀ *ᵥ e7 ⟨6, by norm_num⟩ = fun i => -q.coeff i.val := by
  change (companion7 q)ᵀ *ᵥ Pi.single ⟨6, by norm_num⟩ 1 = fun i => -q.coeff i.val
  rw [Matrix.mulVec_single_one]
  funext i
  rw [Matrix.col_apply, Matrix.transpose_apply, companion7_apply, if_pos rfl]

/-- `e₀` is cyclic: powers of the transposed companion hit every basis vector. -/
theorem transpose_companion7_pow_mulVec_e7_zero (q : ℝ[X]) (k : ℕ) (hk : k ≤ 6) :
    ((companion7 q)ᵀ ^ k) *ᵥ e7 (0 : Fin 7) = e7 ⟨k, by omega⟩ := by
  induction k with
  | zero => rw [pow_zero, Matrix.one_mulVec]; rfl
  | succ k ih =>
      have hk6 : k < 6 := by omega
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih (by omega)]
      exact transpose_companion7_mulVec_e7_succ q ⟨k, by omega⟩ hk6

/-- The transposed companion applied to `e₀` seven times is the feedback vector. -/
theorem transpose_companion7_pow_seven_mulVec_e7_zero (q : ℝ[X]) :
    ((companion7 q)ᵀ ^ 7) *ᵥ e7 (0 : Fin 7) = -∑ j : Fin 7, q.coeff j.val • e7 j := by
  rw [pow_succ', ← Matrix.mulVec_mulVec,
    transpose_companion7_pow_mulVec_e7_zero q 6 (by norm_num),
    show e7 (⟨6, by omega⟩ : Fin 7) = e7 ⟨6, by norm_num⟩ from
      e7_ext (by rw [Fin.ext_iff]),
    transpose_companion7_mulVec_e7_last]
  funext i
  simp only [Pi.neg_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb; rw [e7_apply_ne (Ne.symm hb), mul_zero]
  · intro hi; exact absurd (Finset.mem_univ i) hi

/-- The sum `∑ i<7, cᵢ • eᵢ` agrees with the `Fin 7` sum. -/
theorem sum_range_seven_e7 (q : ℝ[X]) :
    (∑ i ∈ Finset.range 7, q.coeff i • eb i) = ∑ j : Fin 7, q.coeff j.val • e7 j := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => q.coeff i • eb i) 7]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [eb_val j]

/-- The first `7` powers kill `e₀` down to the feedback vector. -/
theorem sum_range_seven_pow_e7 (q : ℝ[X]) :
    (∑ i ∈ Finset.range 7, q.coeff i • ((companion7 q)ᵀ ^ i *ᵥ e7 (0 : Fin 7)))
      = ∑ j : Fin 7, q.coeff j.val • e7 j := by
  rw [show (∑ i ∈ Finset.range 7, q.coeff i • ((companion7 q)ᵀ ^ i *ᵥ e7 (0 : Fin 7)))
        = ∑ i ∈ Finset.range 7, q.coeff i • eb i from
      Finset.sum_congr rfl (fun i hi => by
        rw [Finset.mem_range] at hi
        rw [transpose_companion7_pow_mulVec_e7_zero q i (by omega), eb_eq_e7 i (by omega)])]
  exact sum_range_seven_e7 q

/-- `aeval T q` commutes with `T`. -/
theorem aeval_transpose_companion7_commute (q : ℝ[X]) (hqdeg : q.natDegree = 7) :
    (Polynomial.aeval (companion7 q)ᵀ q) * (companion7 q)ᵀ
      = (companion7 q)ᵀ * (Polynomial.aeval (companion7 q)ᵀ q) := by
  rw [Polynomial.aeval_eq_sum_range, hqdeg, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.smul_mul, Matrix.mul_smul, ← pow_succ, ← pow_succ']

/-- `(aeval T q)` kills the cyclic vector `e₀`. -/
theorem aeval_transpose_companion7_mulVec_e7_zero (q : ℝ[X]) (h7 : q.coeff 7 = 1)
    (hqdeg : q.natDegree = 7) :
    (Polynomial.aeval (companion7 q)ᵀ q) *ᵥ e7 (0 : Fin 7) = 0 := by
  rw [Polynomial.aeval_eq_sum_range, hqdeg, Matrix.sum_mulVec]
  simp_rw [Matrix.smul_mulVec]
  rw [Finset.sum_range_succ, sum_range_seven_pow_e7 q,
    transpose_companion7_pow_seven_mulVec_e7_zero q, h7]
  simp

/-- `q` annihilates the transposed companion matrix. -/
theorem aeval_transpose_companion7_eq_zero (q : ℝ[X]) (h7 : q.coeff 7 = 1)
    (hqdeg : q.natDegree = 7) :
    (Polynomial.aeval (companion7 q)ᵀ q) = 0 := by
  have hcomm := aeval_transpose_companion7_commute q hqdeg
  have hpow : ∀ k : ℕ,
      (Polynomial.aeval (companion7 q)ᵀ q) * (companion7 q)ᵀ ^ k
        = (companion7 q)ᵀ ^ k * (Polynomial.aeval (companion7 q)ᵀ q) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        calc (Polynomial.aeval (companion7 q)ᵀ q) * (companion7 q)ᵀ ^ (k + 1)
            = (Polynomial.aeval (companion7 q)ᵀ q) * ((companion7 q)ᵀ ^ k * (companion7 q)ᵀ) := by
              rw [pow_succ]
          _ = ((Polynomial.aeval (companion7 q)ᵀ q) * (companion7 q)ᵀ ^ k) * (companion7 q)ᵀ := by
              rw [← mul_assoc]
          _ = ((companion7 q)ᵀ ^ k * (Polynomial.aeval (companion7 q)ᵀ q)) * (companion7 q)ᵀ := by
              rw [ih]
          _ = (companion7 q)ᵀ ^ k * ((Polynomial.aeval (companion7 q)ᵀ q) * (companion7 q)ᵀ) := by
              rw [← mul_assoc]
          _ = (companion7 q)ᵀ ^ k * ((companion7 q)ᵀ * (Polynomial.aeval (companion7 q)ᵀ q)) := by
              rw [hcomm]
          _ = ((companion7 q)ᵀ ^ k * (companion7 q)ᵀ) * (Polynomial.aeval (companion7 q)ᵀ q) := by
              rw [mul_assoc]
          _ = (companion7 q)ᵀ ^ (k + 1) * (Polynomial.aeval (companion7 q)ᵀ q) := by
              rw [← pow_succ]
  apply Matrix.ext
  intro i j
  have h0 := aeval_transpose_companion7_mulVec_e7_zero q h7 hqdeg
  have hzero : (Polynomial.aeval (companion7 q)ᵀ q) *ᵥ e7 j = 0 := by
    rw [show e7 j = (companion7 q)ᵀ ^ j.val *ᵥ e7 (0 : Fin 7) from
        (e7_ext (Fin.ext rfl)).trans
          (transpose_companion7_pow_mulVec_e7_zero q j.val (by omega)).symm,
      Matrix.mulVec_mulVec, hpow, ← Matrix.mulVec_mulVec, h0]
    simp
  have hcoord : (Polynomial.aeval (companion7 q)ᵀ q) i j
      = ((Polynomial.aeval (companion7 q)ᵀ q) *ᵥ e7 j) i := by
    rw [show e7 j = Pi.single j 1 from rfl, Matrix.mulVec_single_one, Matrix.col_apply]
  rw [hcoord, hzero]
  rfl

/-- For monic `q` of degree at most `7`, the companion matrix has characteristic polynomial `q`. -/
theorem companion7_charpoly (q : ℝ[X]) (h7 : q.coeff 7 = 1) (hdeg : q.natDegree ≤ 7) :
    (companion7 q).charpoly = q := by
  have hqdeg : q.natDegree = 7 :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hdeg (by rw [h7]; norm_num)
  have hmonic : q.Monic := by
    unfold Polynomial.Monic
    rw [Polynomial.leadingCoeff, hqdeg, h7]
  have hnoann : ∀ p : ℝ[X], p.natDegree < 7 →
      (Polynomial.aeval (companion7 q)ᵀ p) = 0 → p = 0 := by
    intro p hp hpe
    have h1 : (∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i • eb i) = 0 := by
      have h := congrArg (fun (A : Matrix (Fin 7) (Fin 7) ℝ) => A *ᵥ e7 (0 : Fin 7)) hpe
      rw [Matrix.zero_mulVec, Polynomial.aeval_eq_sum_range, Matrix.sum_mulVec] at h
      simp_rw [Matrix.smul_mulVec] at h
      rw [← h]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [Finset.mem_range] at hi
      rw [transpose_companion7_pow_mulVec_e7_zero q i (by omega), eb_eq_e7 i (by omega)]
    have h2 : (∑ i ∈ Finset.range 7, p.coeff i • eb i) = 0 := by
      rw [← h1]
      exact (Finset.sum_subset (fun i hi => by rw [Finset.mem_range] at hi ⊢; omega)
        (fun i _ hni => by
          rw [Finset.mem_range] at hni
          rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_smul])).symm
    have h3 : (∑ i : Fin 7, p.coeff i.val • e7 i) = 0 := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => p.coeff i • eb i) 7] at h2
      simpa only [eb_val] using h2
    apply Polynomial.ext
    intro n
    by_cases hn : n < 7
    · have h4 : (∑ i : Fin 7, p.coeff i.val • e7 i) (⟨n, hn⟩ : Fin 7) = 0 := by
        rw [h3]; rfl
      rw [Finset.sum_apply] at h4
      simp only [Pi.smul_apply, smul_eq_mul] at h4
      rw [Finset.sum_eq_single (⟨n, hn⟩ : Fin 7)] at h4
      · simpa using h4
      · intro b _ hb; rw [e7_apply_ne (Ne.symm hb), mul_zero]
      · intro hmem; exact absurd (Finset.mem_univ (⟨n, hn⟩ : Fin 7)) hmem
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (show p.natDegree < n by omega)]
      rw [Polynomial.coeff_zero]
  set r := (companion7 q)ᵀ.charpoly %ₘ q with hr
  have hr0 : r = 0 := by
    refine hnoann r ?_ ?_
    · rcases eq_or_ne r 0 with h | h
      · rw [h]; norm_num
      · rw [Polynomial.natDegree_lt_iff_degree_lt h]
        have hlt := Polynomial.degree_modByMonic_lt (companion7 q)ᵀ.charpoly hmonic
        rwa [Polynomial.degree_eq_natDegree hmonic.ne_zero, hqdeg] at hlt
    · have hsplit := Polynomial.modByMonic_add_div (companion7 q)ᵀ.charpoly q
      rw [← hr] at hsplit
      have h := congrArg (Polynomial.aeval (companion7 q)ᵀ) hsplit
      simp only [map_add, map_mul] at h
      rw [Matrix.aeval_self_charpoly,
        aeval_transpose_companion7_eq_zero q h7 hqdeg, zero_mul, add_zero] at h
      exact h
  have hdvd_char : q ∣ (companion7 q)ᵀ.charpoly := by
    rw [← Polynomial.modByMonic_eq_zero_iff_dvd hmonic, ← hr]
    exact hr0
  have hchar_monic : (companion7 q)ᵀ.charpoly.Monic := Matrix.charpoly_monic _
  have hchar_deg : (companion7 q)ᵀ.charpoly.natDegree = 7 := Matrix.charpoly_natDegree_eq_dim _
  have hchar_eq : (companion7 q)ᵀ.charpoly = q :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmonic hchar_monic hdvd_char
      (by rw [hchar_deg, hqdeg])
  rw [← Matrix.charpoly_transpose]
  exact hchar_eq

/-- Cayley–Hamilton specialization: `q (companion7 q) = 0`. -/
theorem aeval_companion7_self (q : ℝ[X]) (h7 : q.coeff 7 = 1) (hdeg : q.natDegree ≤ 7) :
    (Polynomial.aeval (companion7 q)) q = 0 := by
  have h := Matrix.aeval_self_charpoly (companion7 q)
  rwa [companion7_charpoly q h7 hdeg] at h

end

end Pconstructible
