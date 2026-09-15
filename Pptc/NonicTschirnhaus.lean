import Pptc.NonicMeyer
import Pptc.NonicWitness

/-! # Pptc.NonicTschirnhaus — WP4: `spread` is the Gram form, and the final datum

This file closes the link between the real quadratic form `spread` of `Pptc.NonicWitness`
and the algebraic Gram form `gramOf` of `Pptc.NonicMeyer`.

For rational `ψ : Fin 7 → ℚ` and `v : Fin 6 → ℚ` put `A = aeval (companion9' q) (polyOfVec9 ψ)`
and `p = ∑_k v_k X^{k+1}`.  Evaluating the inner function underlying `spread` at a complex
root `ρ` of `q` gives `g(ρ) = (aeval A p).eval ρ = (p.comp ψ).eval ρ`, and the two traces
`Tr (aeval A p)` and `Tr ((aeval A p)²)` are the sums of `g(ρ)` and `g(ρ)²` over the roots
(`companion9_trace_pow_aeval`).  `gram_eq_trace_shift` rewrites the Gram quadratic form as
`Tr ((aeval A p)²) - (Tr (aeval A p))²/9`, so the complex number inside `spread` is the
`ℚ → ℂ` cast of the rational Gram value; taking real parts gives `spread_rat_cast`.

`tschirnhausDatum_of_signs_rat` feeds rational sign information through
`tschirnhausDatum_of_signs`, and `exists_tschirnhaus9_of_real_signs` assembles the final
Tschirnhaus statement from real sign information via `exists_rat_signs`. -/

open Polynomial Matrix Module

namespace Pconstructible

noncomputable section

/-- Evaluation of `polyOfVec9 ψ` over `ℂ` is the explicit polynomial `∑_j ψ_j z^j`. -/
theorem polyOfVec9_map_eval (ψ : Fin 7 → ℚ) (z : ℂ) :
    ((polyOfVec9 ψ).map (algebraMap ℚ ℂ)).eval z
      = ∑ j : Fin 7, (ψ j : ℂ) * z ^ (j : ℕ) := by
  rw [polyOfVec9, Polynomial.map_sum, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Polynomial.map_monomial, Polynomial.eval_monomial]
  rfl

-- Theorem: `polyOfVec9 ψ` has degree at most six (its monomials are `X^i`, `i : Fin 7`).
theorem polyOfVec9_natDegree_le (ψ : Fin 7 → ℚ) : (polyOfVec9 ψ).natDegree ≤ 6 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro m hm
  rw [polyOfVec9, Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [Polynomial.coeff_monomial, if_neg (by rintro rfl; omega)]

-- Theorem: if a rational `c` casts to the complex value computed by `spreadCore`, then
-- `spreadCore` returns `c`.
theorem spreadCore_eq_of_algebraMap (R : Finset ℂ) (g : ℂ → ℂ) (c : ℚ)
    (h : algebraMap ℚ ℂ c = (∑ z ∈ R, g z ^ 2) - (∑ z ∈ R, g z) ^ 2 / 9) :
    spreadCore R g = (c : ℝ) := by
  unfold spreadCore
  rw [← h]
  change ((c : ℂ)).re = (c : ℝ)
  rw [← Complex.ofReal_ratCast]
  exact Complex.ofReal_re _

-- Theorem: for rational `ψ` and `v`, the real form `spread` is the `ℚ → ℝ` cast of the
-- Gram quadratic form `v ↦ ∑_{i,j} v_i (gramOf A)_{ij} v_j` with
-- `A = aeval (companion9' q) (polyOfVec9 ψ)`.
theorem spread_rat_cast {q : ℚ[X]} (hmon : q.Monic) (h9 : q.natDegree = 9)
    (hsep : q.Separable) (ψ : Fin 7 → ℚ) (v : Fin 6 → ℚ) :
    spread q (fun j => (ψ j : ℝ)) (fun k => (v k : ℝ))
      = ((∑ i, ∑ j, v i * gramOf (aeval (companion9' q) (polyOfVec9 ψ)) i j * v j
          : ℚ) : ℝ) := by
  classical
  set M : Matrix (Fin 9) (Fin 9) ℚ := companion9' q with hM
  set A : Matrix (Fin 9) (Fin 9) ℚ := aeval M (polyOfVec9 ψ) with hA
  set p : ℚ[X] := ∑ k : Fin 6, C (v k) * X ^ (k.val + 1) with hp
  set φ : ℚ[X] := p.comp (polyOfVec9 ψ) with hφ
  set R : Finset ℂ := (q.map (algebraMap ℚ ℂ)).roots.toFinset with hR
  set g : ℂ → ℂ := fun z => ∑ k : Fin 6, (v k : ℂ) *
      (∑ j : Fin 7, (ψ j : ℂ) * z ^ (j : ℕ)) ^ (k.val + 1) with hg
  -- `spread` with rational arguments is `spreadCore R g` (the casts agree).
  have hspread : spread q (fun j => (ψ j : ℝ)) (fun k => (v k : ℝ))
      = spreadCore R g := by
    have hg' : (fun z : ℂ => ∑ k : Fin 6, ((v k : ℝ) : ℂ) *
        (∑ j : Fin 7, ((ψ j : ℝ) : ℂ) * z ^ (j : ℕ)) ^ (k.val + 1)) = g := by
      funext z
      rw [hg]
      simp only [Complex.ofReal_ratCast]
    unfold spread
    rw [← hR, hg']
  -- The roots of `q` over `ℂ` are the values of `R`.
  have hRval : R.val = (q.map (algebraMap ℚ ℂ)).roots := by
    rw [hR, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr (roots_nodup hsep)]
  have hp_eval : ∀ w : ℂ, (p.map (algebraMap ℚ ℂ)).eval w
      = ∑ k : Fin 6, (v k : ℂ) * w ^ (k.val + 1) := by
    intro w
    rw [hp, Polynomial.map_sum, Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    rfl
  -- Evaluating `φ` over `ℂ` gives the inner function `g` of `spread`.
  have hφeval : ∀ z : ℂ, (φ.map (algebraMap ℚ ℂ)).eval z = g z := by
    intro z
    have h1 : (φ.map (algebraMap ℚ ℂ)).eval z
        = (p.map (algebraMap ℚ ℂ)).eval (((polyOfVec9 ψ).map (algebraMap ℚ ℂ)).eval z) := by
      rw [hφ, Polynomial.map_comp, Polynomial.eval_comp]
    rw [h1, hp_eval, polyOfVec9_map_eval, hg]
  -- `aeval A p = aeval M φ`, so the two trace power sums match.
  have hcomp : aeval M φ = aeval A p := by
    rw [hφ, Polynomial.aeval_comp, ← hA]
  -- Trace power sums evaluated at the roots.
  have hc1 := companion9_trace_pow_aeval q φ hmon h9 hsep 1
  have hc2 := companion9_trace_pow_aeval q φ hmon h9 hsep 2
  rw [← hM] at hc1 hc2
  simp only [pow_one] at hc1
  have e1 : algebraMap ℚ ℂ (Matrix.trace (aeval A p))
      = ((q.map (algebraMap ℚ ℂ)).roots.map
          (fun z => (φ.map (algebraMap ℚ ℂ)).eval z)).sum := by
    rw [← hcomp]
    exact hc1
  have e2 : algebraMap ℚ ℂ (Matrix.trace ((aeval A p) ^ 2))
      = ((q.map (algebraMap ℚ ℂ)).roots.map
          (fun z => ((φ.map (algebraMap ℚ ℂ)).eval z) ^ 2)).sum := by
    rw [← hcomp]
    exact hc2
  have hsum1 : ((q.map (algebraMap ℚ ℂ)).roots.map
        (fun z => (φ.map (algebraMap ℚ ℂ)).eval z)).sum = ∑ z ∈ R, g z := by
    rw [← hRval, ← Finset.sum_eq_multiset_sum]
    exact Finset.sum_congr rfl (fun z _ => hφeval z)
  have hsum2 : ((q.map (algebraMap ℚ ℂ)).roots.map
        (fun z => ((φ.map (algebraMap ℚ ℂ)).eval z) ^ 2)).sum = ∑ z ∈ R, g z ^ 2 := by
    rw [← hRval, ← Finset.sum_eq_multiset_sum]
    exact Finset.sum_congr rfl (fun z _ => by rw [hφeval z])
  -- `gram_eq_trace_shift` identifies the Gram form with the shifted trace form.
  have hgram : (∑ i, ∑ j, v i * gramOf A i j * v j)
      = Matrix.trace ((aeval A p) ^ 2) - (Matrix.trace (aeval A p)) ^ 2 / 9 := by
    have h := gram_eq_trace_shift A v
    rw [← hp] at h
    exact h
  -- Cast the rational identity to `ℂ`: the complex value under `.re` is a rational cast.
  have hgramC : algebraMap ℚ ℂ (∑ i, ∑ j, v i * gramOf A i j * v j)
      = ((∑ z ∈ R, g z ^ 2) - (∑ z ∈ R, g z) ^ 2 / 9) := by
    rw [hgram]
    rw [map_sub, map_div₀, map_pow]
    rw [e2, e1, hsum2, hsum1]
    norm_num
  have hfinal : spreadCore R g = ((∑ i, ∑ j, v i * gramOf A i j * v j : ℚ) : ℝ) :=
    spreadCore_eq_of_algebraMap R g _ hgramC
  rw [hspread]
  exact hfinal

-- Theorem: rational sign information for `spread` yields the Tschirnhaus datum for `q`.
theorem tschirnhausDatum_of_signs_rat {q : ℚ[X]} (hmon : q.Monic) (h9 : q.natDegree = 9)
    (hsep : q.Separable)
    (h : ∃ (ψ : Fin 7 → ℚ) (vm vp : Fin 6 → ℚ),
      spread q (fun j => (ψ j : ℝ)) (fun k => (vm k : ℝ)) < 0 ∧
      0 < spread q (fun j => (ψ j : ℝ)) (fun k => (vp k : ℝ))) :
    TschirnhausDatum q := by
  obtain ⟨ψ, vm, vp, hneg, hpos⟩ := h
  refine tschirnhausDatum_of_signs (polyOfVec9_natDegree_le ψ) ?_ ?_
  · refine ⟨vm, ?_⟩
    have h' := hneg
    rw [spread_rat_cast hmon h9 hsep ψ vm] at h'
    exact_mod_cast h'
  · refine ⟨vp, ?_⟩
    have h' := hpos
    rw [spread_rat_cast hmon h9 hsep ψ vp] at h'
    exact_mod_cast h'

-- Theorem: real sign information for `spread` (the outcome of `exists_real_signs`) gives the
-- Tschirnhaus pair with vanishing `X^8`/`X^7` resolvent coefficients.
theorem exists_tschirnhaus9_of_real_signs {q : ℚ[X]} (hmon : q.Monic) (h9 : q.natDegree = 9)
    (hsep : q.Separable)
    (hs : ∃ (ψ : Fin 7 → ℝ) (vm vp : Fin 6 → ℝ),
      spread q ψ vm < 0 ∧ 0 < spread q ψ vp) :
    ∃ ψ φ : ℚ[X], ψ.natDegree ≤ 6 ∧ 1 ≤ ψ.natDegree ∧
      φ.natDegree ≤ 6 ∧ 1 ≤ φ.natDegree ∧
      ((aeval (companion9' q) (φ.comp ψ)).charpoly).coeff 8 = 0 ∧
      ((aeval (companion9' q) (φ.comp ψ)).charpoly).coeff 7 = 0 :=
  exists_tschirnhaus9_of_datum hmon h9 hsep
    (tschirnhausDatum_of_signs_rat hmon h9 hsep (exists_rat_signs hs))

-- Theorem: a monic separable nonic over `ℚ` with a nonreal root has the Tschirnhaus datum.
-- (`exists_real_signs` supplies the real sign witnesses, `exists_rat_signs` rationalises them.)
theorem tschirnhausDatum_of_nonreal {q : ℚ[X]} (hmon : q.Monic) (h9 : q.natDegree = 9)
    (hsep : q.Separable)
    (hrel : ∃ z : ℂ, (q.map (algebraMap ℚ ℂ)).eval z = 0 ∧ z.im ≠ 0) :
    TschirnhausDatum q :=
  tschirnhausDatum_of_signs_rat hmon h9 hsep
    (exists_rat_signs (exists_real_signs hmon h9 hsep hrel))

end

end Pconstructible
