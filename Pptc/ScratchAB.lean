import Pptc.Basic
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Topology.Order.IntermediateValue

open Polynomial Filter

namespace Pconstructible

-- Theorem: a cubic `a + b x + c x² + d x³` with `0 < d` has a real root. Since the leading
-- coefficient is positive, the cubic tends to `+∞` at `+∞` and to `-∞` at `-∞`, so the
-- intermediate value theorem applied to it and the zero function produces a root.
theorem cubic_exists_root_of_pos {a b c d : ℝ} (hd : 0 < d) :
    ∃ x : ℝ, a + b * x + c * x ^ 2 + d * x ^ 3 = 0 := by
  set p : Polynomial ℝ := C a + C b * X + C c * X ^ 2 + C d * X ^ 3 with hp
  have heval : ∀ x, p.eval x = a + b * x + c * x ^ 2 + d * x ^ 3 := by
    intro x
    simp [hp]
  have hdeg3 : p.degree = 3 := by
    rw [hp]
    compute_degree!
    exact hd.ne'
  have hnat : p.natDegree = 3 := Polynomial.natDegree_eq_of_degree_eq_some hdeg3
  have hdeg : 0 < p.degree := by rw [hdeg3]; norm_num
  have hlc : p.leadingCoeff = d := by
    show p.coeff p.natDegree = d
    rw [hnat, hp]
    simp
  have hcont : Continuous (fun x : ℝ => p.eval x) := by
    convert (by fun_prop : Continuous (fun x : ℝ => a + b * x + c * x ^ 2 + d * x ^ 3))
      using 1
    funext x
    exact heval x
  have htop : Tendsto (fun x : ℝ => p.eval x) atTop atTop :=
    p.tendsto_atTop_of_leadingCoeff_nonneg hdeg (by rw [hlc]; exact hd.le)
  have hcomp_deg : 0 < (p.comp (-X)).degree := by
    rw [Polynomial.degree_comp_neg_X, hdeg3]
    norm_num
  have hcomp_lc : (p.comp (-X)).leadingCoeff ≤ 0 := by
    rw [Polynomial.comp_neg_X_leadingCoeff_eq, hnat, hlc]
    nlinarith [hd]
  have hcomp_tend : Tendsto (fun x : ℝ => (p.comp (-X)).eval x) atTop atBot :=
    (p.comp (-X)).tendsto_atBot_of_leadingCoeff_nonpos hcomp_deg hcomp_lc
  have hbot : Tendsto (fun x : ℝ => p.eval x) atBot atBot := by
    convert hcomp_tend.comp tendsto_neg_atBot_atTop using 1
    funext x
    simp [Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X]
  obtain ⟨x, hx⟩ :=
    intermediate_value_univ₂_eventually₂ (f := fun x : ℝ => p.eval x)
      (g := fun _ => (0 : ℝ)) (l₁ := atBot) (l₂ := atTop) hcont continuous_const
      (hbot.eventually_le_atBot 0) (htop.eventually_ge_atTop 0)
  exact ⟨x, by simpa [heval] using hx⟩

-- Theorem: every nonzero-degree cubic `a + b x + c x² + d x³` (with `d ≠ 0`) has a real
-- root. For `d < 0` we apply the positive case to the negated coefficients and negate back.
theorem cubic_exists_root {a b c d : ℝ} (hd : d ≠ 0) :
    ∃ x : ℝ, a + b * x + c * x ^ 2 + d * x ^ 3 = 0 := by
  rcases lt_or_gt_of_ne hd with hlt | hgt
  · obtain ⟨x, hx⟩ := cubic_exists_root_of_pos (a := -a) (b := -b) (c := -c) (d := -d)
      (by linarith)
    refine ⟨x, ?_⟩
    have hneg : a + b * x + c * x ^ 2 + d * x ^ 3 =
        -((-a) + (-b) * x + (-c) * x ^ 2 + (-d) * x ^ 3) := by ring
    rw [hneg, hx, neg_zero]
  · exact cubic_exists_root_of_pos hgt

-- Theorem: the binary cubic `a s³ + b s² t + c s t² + d t³` has a nonzero P-constructible
-- solution. It is homogeneous, so it suffices to set `s = 1` and solve the univariate cubic
-- in `t`; a root of a P-constructible cubic is P-constructible.
theorem binary_cubic_zero {a b c d : ℝ} (ha : PConstructible a) (hb : PConstructible b)
    (hc : PConstructible c) (hd : PConstructible d) :
    ∃ s t : ℝ, PConstructible s ∧ PConstructible t ∧ (s ≠ 0 ∨ t ≠ 0) ∧
      a * s ^ 3 + b * s ^ 2 * t + c * s * t ^ 2 + d * t ^ 3 = 0 := by
  by_cases hd0 : d = 0
  · refine ⟨0, 1, zero_Pconstructible, PConstructible.base_one, Or.inr one_ne_zero, ?_⟩
    rw [hd0]
    ring
  · obtain ⟨t, ht⟩ := cubic_exists_root (a := a) (b := b) (c := c) hd0
    have htP : PConstructible t :=
      cubicVal_root_Pconstructible ha hb hc hd (Or.inl hd0)
        (by rw [cubicVal]; linarith [ht])
    refine ⟨1, t, PConstructible.base_one, htP, Or.inl one_ne_zero, ?_⟩
    simpa using ht

end Pconstructible
