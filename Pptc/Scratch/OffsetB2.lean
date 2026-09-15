/-
  Pptc/Scratch/OffsetB2.lean  —  scratch file for task B2 (offset research programme).

  Nothing imports this file.  It pins the *positivity half* of Hermite's trace-form
  obstruction used in `septicpaper_revised.tex` (Section 4, Lemma "Hermite"):
  for a totally real target the trace form `Q(φ) = Tr(φ²) = Σ φ(λᵢ)²` is a sum of
  squares, so it is positive definite; hence a real Tschirnhaus map cannot make
  both `p₁(φ) = Tr φ` and `p₂(φ) = Tr φ²` vanish.  The formal statement here is the
  elementary sum-of-squares fact underlying that step.
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic

open Finset

namespace OffsetB2

/-- **Hermite positivity (zero form).** A sum of squares of reals is zero only if
every term is zero.  With `a i = φ (λ i)` this says: if `Tr(φ²) = 0` for a totally
real `q`, then `φ` vanishes at every root — so `p₂(φ) = 0` forces `φ = 0`. -/
theorem sum_sq_eq_zero {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (h : ∑ i, (a i) ^ 2 = 0) : ∀ i, a i = 0 := by
  have hnonneg : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ (a i) ^ 2 := by
    intro i _
    exact sq_nonneg _
  have hall := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp h
  intro i
  exact sq_eq_zero_iff.mp (hall i (Finset.mem_univ i))

/-- **Hermite positivity (positive form).** If some `φ (λ i) ≠ 0` then
`Tr(φ²) = Σ φ(λᵢ)² > 0`.  Hence for a totally real target the only `φ` with
`p₁(φ) = p₂(φ) = 0` is `φ = 0`: a real Tschirnhaus map cannot kill two power sums. -/
theorem sum_sq_pos {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (h : ∃ i, a i ≠ 0) : 0 < ∑ i, (a i) ^ 2 := by
  obtain ⟨i, hi⟩ := h
  refine Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ i, ?_⟩
  exact sq_pos_of_ne_zero hi

/-- Contrapositive packaging of `sum_sq_eq_zero`, matching the paper's use:
`Tr(φ²) = 0` with a nonzero `φ` on the roots is impossible. -/
theorem no_kill_two_power_sums {ι : Type*} [Fintype ι] {a : ι → ℝ}
    (hne : ∃ i, a i ≠ 0) : (∑ i, (a i) ^ 2) ≠ 0 := by
  intro h
  exact hne.elim fun i hi => hi (sum_sq_eq_zero a h i)

end OffsetB2
