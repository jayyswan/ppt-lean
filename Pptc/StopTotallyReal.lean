import Pptc.ScratchN

/-!
### A stop theorem for Bring--Jerrard on a totally real septic

If `q` is a monic separable septic all of whose complex roots are real, then no polynomial
`φ` of degree at most six has resolvent with vanishing second power sum
`p₂ = trace (φ(M)²)`; that is, `p₂ = 0` forces `φ = 0`.  This records that the `s = 0`
Bring--Jerrard reduction is impossible.

The proof is spectral.  `companion7_trace_pow_aeval` identifies `trace (φ(M)²)` with the sum
of the squares of `φ` evaluated at the roots of `q`.  Because every root is real, each term is
the coercion of a nonnegative real square, so a vanishing sum forces every `φ` value to vanish
at the seven distinct real roots of `q` — more than the degree of `φ` permits.
-/

namespace Pconstructible

open Polynomial Matrix

/-- The sum of a multiset of reals, viewed in `ℂ`, is the multiset sum of the coerced terms. -/
private lemma ofReal_multiset_sum (s : Multiset ℝ) :
    (((s.sum : ℝ) : ℂ)) = (s.map (fun x : ℝ => (x : ℂ))).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      simp only [Multiset.sum_cons, Multiset.map_cons]
      push_cast
      rw [ih]

-- Theorem: a totally real separable septic has no degree `≤ 6` polynomial whose resolvent
-- has vanishing second power sum; equivalently `trace (φ(M)²) = 0` forces `φ = 0`.
theorem totallyReal_no_tschirnhaus {q φ : ℝ[X]} (hq : q.Monic) (hdeg : q.natDegree = 7)
    (hsplit : ∀ z : ℂ, (q.map (algebraMap ℝ ℂ)).IsRoot z → z.im = 0)
    (hsep : q.Separable) (hφ : φ.natDegree ≤ 6)
    (h : Matrix.trace (aeval (companion7 q) φ ^ 2) = 0) : φ = 0 := by
  have h2 := companion7_trace_pow_aeval q φ hq hdeg hsep 2
  rw [h, map_zero] at h2
  have hsum : ((q.map (algebraMap ℝ ℂ)).roots.map
      (fun z => ((φ.map (algebraMap ℝ ℂ)).eval z) ^ 2)).sum = 0 := h2.symm
  -- On the roots of `q`, each term is the coercion of a real square.
  have hpoint : ∀ z ∈ (q.map (algebraMap ℝ ℂ)).roots,
      ((φ.map (algebraMap ℝ ℂ)).eval z) ^ 2 = ((φ.eval z.re) ^ 2 : ℂ) := by
    intro z hz
    have hzroot : (q.map (algebraMap ℝ ℂ)).IsRoot z := Polynomial.isRoot_of_mem_roots hz
    have hzim : z.im = 0 := hsplit z hzroot
    have hzre : z = (z.re : ℂ) := by
      apply Complex.ext <;> simp [hzim]
    rw [hzre]
    have heval : (φ.map (algebraMap ℝ ℂ)).eval ((z.re : ℝ) : ℂ)
        = ((φ.eval z.re : ℝ) : ℂ) := by
      rw [Polynomial.eval_map]
      exact Polynomial.eval₂_at_apply (f := algebraMap ℝ ℂ) (r := z.re) (p := φ)
    rw [heval]
    simp only [Complex.ofReal_re]
  have hsum' : ((q.map (algebraMap ℝ ℂ)).roots.map
      (fun z => ((φ.eval z.re) ^ 2 : ℂ))).sum = 0 := by
    rw [← hsum]
    exact (congrArg Multiset.sum (Multiset.map_congr rfl (fun z hz => hpoint z hz))).symm
  have hreal : (((q.map (algebraMap ℝ ℂ)).roots.map
      (fun z => (φ.eval z.re) ^ 2))).sum = 0 := by
    have hcoe : ((((q.map (algebraMap ℝ ℂ)).roots.map
        (fun z => (φ.eval z.re) ^ 2)).sum : ℝ) : ℂ) = 0 := by
      rw [ofReal_multiset_sum, Multiset.map_map]
      simp only [Function.comp_apply]
      push_cast
      exact hsum'
    exact Complex.ofReal_eq_zero.mp hcoe
  have hzero : ∀ z ∈ (q.map (algebraMap ℝ ℂ)).roots, φ.eval z.re = 0 := by
    have hnn : ∀ x ∈ ((q.map (algebraMap ℝ ℂ)).roots.map
        (fun z => (φ.eval z.re) ^ 2)), (0 : ℝ) ≤ x := by
      intro x hx
      obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hx
      exact sq_nonneg _
    have hall := Multiset.all_zero_of_le_zero_le_of_sum_eq_zero hnn hreal
    intro z hz
    exact sq_eq_zero_iff.mp (hall ((φ.eval z.re) ^ 2) (Multiset.mem_map_of_mem _ hz))
  by_cases hφ0 : φ = 0
  · exact hφ0
  · exfalso
    have hsep' : (q.map (algebraMap ℝ ℂ)).Separable := hsep.map
    have hnodup : (q.map (algebraMap ℝ ℂ)).roots.Nodup := Polynomial.nodup_roots hsep'
    have hdegC : (q.map (algebraMap ℝ ℂ)).natDegree = 7 := by
      rw [Polynomial.natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective]
      exact hdeg
    have hcardC : (q.map (algebraMap ℝ ℂ)).roots.card = 7 := by
      rw [← (IsAlgClosed.splits (q.map (algebraMap ℝ ℂ))).natDegree_eq_card_roots, hdegC]
    have hRcard : ((q.map (algebraMap ℝ ℂ)).roots.toFinset).card = 7 := by
      rw [Multiset.toFinset_card_of_nodup hnodup]
      exact hcardC
    have hinj : Set.InjOn Complex.re (((q.map (algebraMap ℝ ℂ)).roots.toFinset : Finset ℂ)) := by
      intro z hz w hw hzw
      have hzroot : (q.map (algebraMap ℝ ℂ)).IsRoot z :=
        Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp hz)
      have hwroot : (q.map (algebraMap ℝ ℂ)).IsRoot w :=
        Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp hw)
      have hzi : z.im = 0 := hsplit z hzroot
      have hwi : w.im = 0 := hsplit w hwroot
      apply Complex.ext
      · exact hzw
      · rw [hzi, hwi]
    have hScard : (((q.map (algebraMap ℝ ℂ)).roots.toFinset.image Complex.re)).card = 7 := by
      rw [Finset.card_image_of_injOn hinj, hRcard]
    have hsub : ((q.map (algebraMap ℝ ℂ)).roots.toFinset.image Complex.re)
        ⊆ φ.roots.toFinset := by
      intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      have hzroot : z ∈ (q.map (algebraMap ℝ ℂ)).roots := Multiset.mem_toFinset.mp hz
      have hzx : φ.eval z.re = 0 := hzero z hzroot
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hφ0]
      exact hzx
    have h7 : 7 ≤ φ.natDegree := by
      have h1 : (((q.map (algebraMap ℝ ℂ)).roots.toFinset.image Complex.re)).card
          ≤ φ.roots.toFinset.card := Finset.card_le_card hsub
      have h2 : φ.roots.toFinset.card ≤ φ.roots.card := Multiset.toFinset_card_le φ.roots
      have h3 : φ.roots.card ≤ φ.natDegree := Polynomial.card_roots' φ
      omega
    omega

end Pconstructible
