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

-- Targeted imports rather than `import Mathlib`; see the note in `Pptc.Defs`.
import Pptc.DegreeSevenOnePair

open Polynomial Matrix

namespace Pconstructible

noncomputable section

/-! ### Coefficient-closure helpers

`PConstructible` is closed under the polynomial operations used to assemble the
sextic, but Mathlib only provides the product and constant-multiple closures in
`Pptc.ScratchSep`.  The two `add`/`sub` helpers and the monomial closures below fill
the remaining gaps. -/

private theorem coeff_add_Pc {p r : ℝ[X]}
    (hp : ∀ k, PConstructible (p.coeff k)) (hr : ∀ k, PConstructible (r.coeff k)) :
    ∀ k, PConstructible ((p + r).coeff k) :=
  fun k => by rw [Polynomial.coeff_add]; exact PConstructible.add (hp k) (hr k)

private theorem coeff_sub_Pc {p r : ℝ[X]}
    (hp : ∀ k, PConstructible (p.coeff k)) (hr : ∀ k, PConstructible (r.coeff k)) :
    ∀ k, PConstructible ((p - r).coeff k) :=
  fun k => by rw [Polynomial.coeff_sub]; exact PConstructible.sub (hp k) (hr k)

private theorem coeff_X_Pc : ∀ k, PConstructible (((X : ℝ[X])).coeff k) := by
  intro k
  rw [Polynomial.coeff_X]
  split_ifs with h
  · exact PConstructible.base_one
  · exact zero_Pconstructible

private theorem coeff_X_sq_Pc : ∀ k, PConstructible (((X : ℝ[X]) ^ 2).coeff k) := by
  intro k
  rw [pow_two]
  exact coeff_mul_Pconstructible coeff_X_Pc coeff_X_Pc k

/-! ### Degree helpers for the line polynomials -/

private theorem natDegree_C_le' (a : ℝ) : (C a : ℝ[X]).natDegree ≤ 0 := by
  have h := Polynomial.natDegree_C_mul_le a (1 : ℝ[X])
  rwa [mul_one, Polynomial.natDegree_one] at h

private theorem natDegree_lin_le (a b : ℝ) :
    (C a + C b * X : ℝ[X]).natDegree ≤ 1 := by
  refine Polynomial.natDegree_add_le_of_degree_le ?_ ?_
  · exact le_trans (natDegree_C_le' a) (by norm_num)
  · have hX : (X : ℝ[X]).natDegree ≤ 1 := by
      rw [← pow_one (X : ℝ[X])]
      exact Polynomial.natDegree_X_pow_le 1
    exact le_trans (Polynomial.natDegree_C_mul_le b X) hX

private theorem natDegree_quad_le (a b c : ℝ) :
    (C a + C b * X + C c * X ^ 2 : ℝ[X]).natDegree ≤ 2 := by
  refine Polynomial.natDegree_add_le_of_degree_le ?_ ?_
  · exact le_trans (natDegree_lin_le a b) (by norm_num)
  · exact le_trans (Polynomial.natDegree_C_mul_le c (X ^ 2))
      (le_trans (Polynomial.natDegree_X_pow_le 2) (by norm_num))

/-! ### The sextic along the stereographic line

For a fixed P-constructible cone point `P₀` and directions `d`, `δ`, the parametrised
vector `v(m) = stereo (Gram q) P₀ (d + m • δ)` has each coordinate a polynomial of
degree `≤ 2` in `m`, and each `b`-coordinate of `Lcomb q v(m)` likewise.  Substituting
these into the triple-sum formula `p3vec_eq_sum` for the cubic produces a sextic `Ψ`
whose coefficients are P-constructible. -/

-- Theorem: along the stereographic line through a fixed P-constructible cone point,
-- the cubic `p3vec q ∘ Lcomb q ∘ stereo (Gram q) P₀` is a polynomial of degree at most
-- `6` in the line parameter, with P-constructible coefficients.
theorem exists_sextic_along_line (q : ℝ[X]) (hq : ∀ k, PConstructible (q.coeff k))
    {P₀ d δ : Fin 6 → ℝ} (hP₀ : ∀ i, PConstructible (P₀ i))
    (hd : ∀ i, PConstructible (d i)) (hδ : ∀ i, PConstructible (δ i)) :
    ∃ Ψ : ℝ[X], (∀ k, PConstructible (Ψ.coeff k)) ∧ Ψ.natDegree ≤ 6 ∧
      ∀ m : ℝ, Ψ.eval m = p3vec q (Lcomb q (stereo (Gram q) P₀ (d + m • δ))) := by
  have hA : (Gram q)ᵀ = Gram q := Gram_symm q
  have hApc : ∀ i j, PConstructible ((Gram q) i j) :=
    fun i j => Gram_Pconstructible q hq i j
  have hqd : PConstructible (qform (Gram q) d) := bilin_Pconstructible hApc hd hd
  have hqδ : PConstructible (qform (Gram q) δ) := bilin_Pconstructible hApc hδ hδ
  have hbd : PConstructible (bilin (Gram q) d δ) := bilin_Pconstructible hApc hd hδ
  have hBPd : PConstructible (bilin (Gram q) P₀ d) := bilin_Pconstructible hApc hP₀ hd
  have hBPδ : PConstructible (bilin (Gram q) P₀ δ) := bilin_Pconstructible hApc hP₀ hδ
  let lineQ : ℝ[X] := C (qform (Gram q) d) + C (2 * bilin (Gram q) d δ) * X
      + C (qform (Gram q) δ) * X ^ 2
  have hlineQdef : lineQ = C (qform (Gram q) d) + C (2 * bilin (Gram q) d δ) * X
      + C (qform (Gram q) δ) * X ^ 2 := rfl
  let lineB : ℝ[X] := C (bilin (Gram q) P₀ d) + C (bilin (Gram q) P₀ δ) * X
  have hlineBdef : lineB = C (bilin (Gram q) P₀ d)
      + C (bilin (Gram q) P₀ δ) * X := rfl
  let stComp : Fin 6 → ℝ[X] := fun i =>
      lineQ * C (P₀ i) - (C 2 * lineB) * (C (d i) + C (δ i) * X)
  have hstCompdef : ∀ i, stComp i = lineQ * C (P₀ i)
      - (C 2 * lineB) * (C (d i) + C (δ i) * X) := fun _ => rfl
  let lineVec : Fin 7 → ℝ[X] := fun i => ∑ j : Fin 6, stComp j * C (bvec q j i)
  have hlineVecdef : ∀ i, lineVec i = ∑ j : Fin 6, stComp j * C (bvec q j i) :=
    fun _ => rfl
  let Ψ : ℝ[X] := ∑ i : Fin 7, ∑ j : Fin 7, ∑ k : Fin 7,
      (lineVec i * lineVec j * lineVec k) *
        C (Matrix.trace ((companion7 q) ^ (i.val + j.val + k.val)))
  have hPsiedef : Ψ = ∑ i : Fin 7, ∑ j : Fin 7, ∑ k : Fin 7,
      (lineVec i * lineVec j * lineVec k) *
        C (Matrix.trace ((companion7 q) ^ (i.val + j.val + k.val))) := rfl
  -- Evaluation of the line polynomials.
  have hlineQ_eval : ∀ m : ℝ, (lineQ).eval m = qform (Gram q) (d + m • δ) := by
    intro m
    have hq' := qform_smul_add (Gram q) hA 1 m d δ
    rw [one_smul] at hq'
    rw [hlineQdef, hq']
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_pow, one_pow, one_mul]
    ring
  have hlineB_eval : ∀ m : ℝ, (lineB).eval m = bilin (Gram q) P₀ (d + m • δ) := by
    intro m
    rw [hlineBdef, bilin_add_right, bilin_smul_right]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
    ring
  have hstComp_eval : ∀ (i : Fin 6) (m : ℝ),
      (stComp i).eval m = stereo (Gram q) P₀ (d + m • δ) i := by
    intro i m
    rw [hstCompdef i]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_C, Polynomial.eval_X]
    rw [hlineQ_eval m, hlineB_eval m]
    simp only [stereo, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply]
    ring
  have hlineVec_eval : ∀ (i : Fin 7) (m : ℝ),
      (lineVec i).eval m = (Lcomb q (stereo (Gram q) P₀ (d + m • δ))) i := by
    intro i m
    rw [hlineVecdef i]
    simp only [Lcomb, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hstComp_eval j m]
  -- Coefficient closure.
  have hlineQ_c : ∀ k, PConstructible (lineQ.coeff k) := by
    rw [hlineQdef]
    exact coeff_add_Pc
      (coeff_add_Pc (coeff_C_Pconstructible hqd)
        (coeff_mul_Pconstructible
          (coeff_C_Pconstructible (PConstructible.mul two_Pconstructible hbd)) coeff_X_Pc))
      (coeff_mul_Pconstructible (coeff_C_Pconstructible hqδ) coeff_X_sq_Pc)
  have hlineB_c : ∀ k, PConstructible (lineB.coeff k) := by
    rw [hlineBdef]
    exact coeff_add_Pc (coeff_C_Pconstructible hBPd)
      (coeff_mul_Pconstructible (coeff_C_Pconstructible hBPδ) coeff_X_Pc)
  have hstComp_c : ∀ i k, PConstructible ((stComp i).coeff k) := by
    intro i k
    rw [hstCompdef i]
    refine coeff_sub_Pc ?_ ?_ k
    · exact coeff_mul_Pconstructible hlineQ_c (coeff_C_Pconstructible (hP₀ i))
    · exact coeff_mul_Pconstructible
        (coeff_mul_Pconstructible (coeff_C_Pconstructible two_Pconstructible) hlineB_c)
        (coeff_add_Pc (coeff_C_Pconstructible (hd i))
          (coeff_mul_Pconstructible (coeff_C_Pconstructible (hδ i)) coeff_X_Pc))
  have hlineVec_c : ∀ i k, PConstructible ((lineVec i).coeff k) := by
    intro i k
    rw [hlineVecdef i, coeff_finset_sum]
    refine Finset.sum_Pconstructible Finset.univ _ (fun j _ => ?_)
    exact coeff_mul_Pconstructible (hstComp_c j)
      (coeff_C_Pconstructible (bvec_Pconstructible q hq j i)) k
  have hPsi_c : ∀ n, PConstructible (Ψ.coeff n) := by
    intro n
    rw [hPsiedef, coeff_finset_sum]
    refine Finset.sum_Pconstructible Finset.univ _ (fun i _ => ?_)
    rw [coeff_finset_sum]
    refine Finset.sum_Pconstructible Finset.univ _ (fun j _ => ?_)
    rw [coeff_finset_sum]
    refine Finset.sum_Pconstructible Finset.univ _ (fun k _ => ?_)
    exact coeff_mul_Pconstructible
      (coeff_mul_Pconstructible
        (coeff_mul_Pconstructible (hlineVec_c i) (hlineVec_c j)) (hlineVec_c k))
      (coeff_C_Pconstructible
        (trace_pow_companion7_Pconstructible q hq (i.val + j.val + k.val))) n
  -- Degree bound.
  have hlineQ_deg : lineQ.natDegree ≤ 2 := by
    rw [hlineQdef]
    exact natDegree_quad_le _ _ _
  have hlineB_deg : lineB.natDegree ≤ 1 := by
    rw [hlineBdef]
    exact natDegree_lin_le _ _
  have hstComp_deg : ∀ i, (stComp i).natDegree ≤ 2 := by
    intro i
    rw [hstCompdef i]
    refine le_trans (Polynomial.natDegree_sub_le_of_le ?_ ?_) (le_of_eq (max_self 2))
    · exact le_trans (Polynomial.natDegree_mul_C_le lineQ (P₀ i)) hlineQ_deg
    · exact Polynomial.natDegree_mul_le_of_le
        (le_trans (Polynomial.natDegree_C_mul_le 2 lineB) hlineB_deg)
        (natDegree_lin_le (d i) (δ i))
  have hlineVec_deg : ∀ i, (lineVec i).natDegree ≤ 2 := by
    intro i
    rw [hlineVecdef i]
    refine Polynomial.natDegree_sum_le_of_forall_le (Finset.univ : Finset (Fin 6))
      (fun j => stComp j * C (bvec q j i)) (fun j _ => ?_)
    exact le_trans (Polynomial.natDegree_mul_C_le (stComp j) (bvec q j i))
      (hstComp_deg j)
  have hPsi_deg : Ψ.natDegree ≤ 6 := by
    rw [hPsiedef]
    refine Polynomial.natDegree_sum_le_of_forall_le (Finset.univ : Finset (Fin 7))
      (fun i => ∑ j : Fin 7, ∑ k : Fin 7,
        (lineVec i * lineVec j * lineVec k) *
          C (Matrix.trace ((companion7 q) ^ (i.val + j.val + k.val))))
      (fun i _ => ?_)
    refine Polynomial.natDegree_sum_le_of_forall_le (Finset.univ : Finset (Fin 7))
      (fun j => ∑ k : Fin 7,
        (lineVec i * lineVec j * lineVec k) *
          C (Matrix.trace ((companion7 q) ^ (i.val + j.val + k.val))))
      (fun j _ => ?_)
    refine Polynomial.natDegree_sum_le_of_forall_le (Finset.univ : Finset (Fin 7))
      (fun k =>
        (lineVec i * lineVec j * lineVec k) *
          C (Matrix.trace ((companion7 q) ^ (i.val + j.val + k.val))))
      (fun k _ => ?_)
    refine le_trans (Polynomial.natDegree_mul_C_le _ _) ?_
    exact Polynomial.natDegree_mul_le_of_le
      (Polynomial.natDegree_mul_le_of_le (hlineVec_deg i) (hlineVec_deg j))
      (hlineVec_deg k)
  -- Evaluation of the sextic.
  have hPsi_eval : ∀ m : ℝ,
      Ψ.eval m = p3vec q (Lcomb q (stereo (Gram q) P₀ (d + m • δ))) := by
    intro m
    rw [hPsiedef, p3vec_eq_sum]
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hlineVec_eval i m, hlineVec_eval j m, hlineVec_eval k m]
  exact ⟨Ψ, hPsi_c, hPsi_deg, hPsi_eval⟩

end

end Pconstructible
