import Pptc.NonicResolvent

/-! # Pptc.NonicPowerLaw — the rational resolvent step for the nonic

If `q` is a rational polynomial with real root `β`, and the resolvent `φ (companion9 q)` has
a characteristic polynomial whose `X^8` and `X^7` coefficients vanish, then `y = φ β`
satisfies a degree-≤6 power law `y^9 = p y` with `p ∈ ℚ[X]`, and is P-constructible.
-/

open Polynomial Matrix

namespace Pconstructible

noncomputable section

/-! ### Mapping the degree-9 companion matrix along `ℚ → ℝ` -/

-- Theorem: mapping the generic companion matrix is the companion of the mapped polynomial.
theorem companion9'_map_eq {S : Type*} [CommRing S] (f : ℚ →+* S) (q : ℚ[X]) :
    (companion9' q).map f = companion9' (q.map f) := by
  ext i j
  simp only [Matrix.map_apply, companion9'_apply]
  by_cases h : i.val = 8 <;> simp [h, Polynomial.coeff_map, map_neg]

-- Theorem: `aeval` of the generic companion matrix commutes with mapping `ℚ → ℝ`.
theorem companion9_aeval_map_eq (q φ : ℚ[X]) :
    (aeval (companion9' q) φ).map (algebraMap ℚ ℝ)
      = aeval (companion9' (q.map (algebraMap ℚ ℝ))) (φ.map (algebraMap ℚ ℝ)) := by
  rw [show (aeval (companion9' q) φ).map (algebraMap ℚ ℝ)
        = RingHom.mapMatrix (algebraMap ℚ ℝ) (aeval (companion9' q) φ) from
      (RingHom.mapMatrix_apply _ _).symm,
    Polynomial.map_aeval_eq_aeval_map (R := ℚ)
      (S := Matrix (Fin 9) (Fin 9) ℚ) (T := ℝ) (U := Matrix (Fin 9) (Fin 9) ℝ)
      (φ := algebraMap ℚ ℝ) (ψ := RingHom.mapMatrix (algebraMap ℚ ℝ))
      (by ext r i j; by_cases h : i = j <;> simp [h, Matrix.algebraMap_matrix_apply])
      φ (companion9' q),
    RingHom.mapMatrix_apply, companion9'_map_eq]

/-! ### The rational resolvent step -/

-- Theorem: a vanishing `X^8`/`X^7` coefficient in the resolvent charpoly over `ℚ` yields a
-- degree-≤6 `p` with `(φ β)^9 = p (φ β)`.
theorem resolvent_powerLaw9 {q φ : Polynomial ℚ} {β : ℝ}
    (hβ : aeval β q = 0) (h9 : q.coeff 9 = 1) (hdeg : q.natDegree ≤ 9)
    (hkill : ((aeval (companion9' q) φ).charpoly).coeff 8 = 0 ∧
             ((aeval (companion9' q) φ).charpoly).coeff 7 = 0) :
    ∃ p : Polynomial ℚ, p.natDegree ≤ 6 ∧ (aeval β φ) ^ 9 = aeval (aeval β φ) p := by
  set qℝ : Polynomial ℝ := q.map (algebraMap ℚ ℝ) with hqℝ
  set φℝ : Polynomial ℝ := φ.map (algebraMap ℚ ℝ) with hφℝ
  set Rℚ : Polynomial ℚ := (aeval (companion9' q) φ).charpoly with hR
  have hβℝ : qℝ.eval β = 0 := by
    rw [hqℝ, Polynomial.eval_map, ← Polynomial.aeval_def]
    exact hβ
  have h9ℝ : qℝ.coeff 9 = 1 := by rw [hqℝ, Polynomial.coeff_map, h9, map_one]
  have hdegℝ : qℝ.natDegree ≤ 9 := by
    rw [hqℝ]
    exact le_trans Polynomial.natDegree_map_le hdeg
  have hrootℝ : ((aeval (companion9 qℝ) φℝ).charpoly).eval (φℝ.eval β) = 0 :=
    companion9_charpoly_aeval_isRoot hβℝ h9ℝ hdegℝ
  have hchar : (aeval (companion9 qℝ) φℝ).charpoly = Rℚ.map (algebraMap ℚ ℝ) := by
    rw [hR]
    have h := Matrix.charpoly_map (aeval (companion9' q) φ) (algebraMap ℚ ℝ)
    rw [companion9_aeval_map_eq] at h
    exact h
  have hroot2 : (Rℚ.map (algebraMap ℚ ℝ)).eval (aeval β φ) = 0 := by
    have h := hrootℝ
    rw [hchar] at h
    have hφ : φℝ.eval β = aeval β φ := by
      rw [hφℝ, Polynomial.eval_map, ← Polynomial.aeval_def]
    rw [hφ] at h
    exact h
  have hRnat : Rℚ.natDegree = 9 := by
    rw [hR, Matrix.charpoly_natDegree_eq_dim]
    simp
  have hRmonic : Rℚ.Monic := by rw [hR]; exact Matrix.charpoly_monic _
  have hR9 : Rℚ.coeff 9 = 1 := by rw [← hRnat]; exact hRmonic.coeff_natDegree
  have hk8 : Rℚ.coeff 8 = 0 := by rw [hR]; exact hkill.1
  have hk7 : Rℚ.coeff 7 = 0 := by rw [hR]; exact hkill.2
  have hpdeg : (X ^ 9 - Rℚ).natDegree ≤ 6 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow]
    rcases lt_trichotomy N 9 with h | h | h
    · interval_cases N <;> simp [hk7, hk8]
    · rw [h]; simp [hR9]
    · have hlt : Rℚ.natDegree < N := by rw [hRnat]; exact h
      rw [if_neg (by omega), Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
      simp
  refine ⟨X ^ 9 - Rℚ, hpdeg, ?_⟩
  have heval : aeval (aeval β φ) (X ^ 9 - Rℚ) = (aeval β φ) ^ 9 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_eq_eval_map, hroot2, sub_zero]
  exact heval.symm

-- Theorem: under the resolvent hypotheses, `φ β` is P-constructible.
theorem resolvent_y_Pconstructible9 {q φ : Polynomial ℚ} {β : ℝ}
    (hβ : aeval β q = 0) (h9 : q.coeff 9 = 1) (hdeg : q.natDegree ≤ 9)
    (hkill : ((aeval (companion9' q) φ).charpoly).coeff 8 = 0 ∧
             ((aeval (companion9' q) φ).charpoly).coeff 7 = 0) :
    PConstructible (aeval β φ) := by
  obtain ⟨p, hpdeg, heq⟩ := resolvent_powerLaw9 hβ h9 hdeg hkill
  by_cases h0 : aeval β φ = 0
  · rw [h0]; exact zero_Pconstructible
  · have heq' : ((1 : ℚ) : ℝ) * (aeval β φ) ^ 9 = aeval (aeval β φ) p := by
      simpa using heq
    exact powerLaw_root_Pconstructible (n := 9) (a := 1) (by norm_num) (by norm_num)
      hpdeg h0 heq'

end

end Pconstructible
