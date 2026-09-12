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
import Pptc.DegreeSeven
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Topology.NhdsWithin

open Polynomial Matrix

namespace Pconstructible

noncomputable section

/-! # The one-conjugate-pair case of degree 7 (issue #6)

Implementation of `PLAN-degree7-s1.md`.  The route parametrises the light cone
`{p₂ = 0}` stereographically from a P-constructible cone point `P₀`, uses the
conjugation symmetry `σ` (only in the proof, never as a construction) to certify that
the reduced cubic changes sign on the cone, then rounds the witnesses to rational
directions and reads off a root of the resulting sextic with the sextic engine.

Sections A–E1 below are the independent algebraic/analytic pieces. -/

/-! ### A. The Tschirnhaus tail, factored out

Once a degree-`≤ 6` Tschirnhaus map `φ` with P-constructible coefficients and vanishing
first three trace power sums is in hand, the root `β` follows from the resolvent power
law.  This is exactly the tail of `root_Pconstructible_of_two_conjugate_pairs_monic`,
isolated so the `s = 1` construction can reuse it. -/

-- Theorem: a real root `β` of a monic separable septic `q` with P-constructible
-- coefficients is P-constructible, provided there is a nonzero degree-`≤ 6` polynomial `φ`
-- with P-constructible coefficients whose first three trace power sums at `companion7 q`
-- vanish.
theorem root_Pconstructible_of_tschirnhaus {q φ : ℝ[X]} (hmon : q.Monic)
    (hnat : q.natDegree = 7) (hsep : q.Separable) (hq : ∀ k, PConstructible (q.coeff k))
    (hφc : ∀ k, PConstructible (φ.coeff k)) (hφdeg : φ.natDegree ≤ 6) (hφne : φ ≠ 0)
    (hp1 : Matrix.trace (aeval (companion7 q) φ) = 0)
    (hp2 : Matrix.trace ((aeval (companion7 q) φ) ^ 2) = 0)
    (hp3 : Matrix.trace ((aeval (companion7 q) φ) ^ 3) = 0)
    {β : ℝ} (hβ : q.eval β = 0) :
    PConstructible β := by
  have hkill := charpoly_aeval_coeff_6_5_4_eq_zero hmon hnat hsep hp1 hp2 hp3
  have h7 : q.coeff 7 = 1 := by rw [← hnat]; exact hmon.coeff_natDegree
  have hdeg : q.natDegree ≤ 7 := le_of_eq hnat
  obtain ⟨c₀, c₁, c₂, c₃, hc₀, hc₁, hc₂, hc₃, hpow⟩ :=
    resolvent_powerLaw hq hβ h7 hdeg hφc hkill
  exact root_Pconstructible_of_powerLaw hφc hφdeg
    (natDegree_ne_zero_of_trace_zero hp1 hφne) hc₀ hc₁ hc₂ hc₃ hpow

/-! ### C. The stereographic parametrisation of the light cone

For a vector `x` on the cone `{Q = 0}` through `P₀`, the second intersection of the line
`P₀ + t x` with the cone is `v x / Q x`, where
`v x = Q x • P₀ - 2 B P₀ x • x`.  No square root is needed because the `t = 0` root is
already known. -/

/-- The second intersection of the cone through `P₀` with the line `P₀ + t x`, scaled by
`Q x`: `Q x • P₀ - 2 B P₀ x • x`. -/
def stereo (A : Matrix (Fin 6) (Fin 6) ℝ) (P₀ x : Fin 6 → ℝ) : Fin 6 → ℝ :=
  qform A x • P₀ - (2 * bilin A P₀ x) • x

-- Theorem (S1): `stereo` always lands on the cone.
theorem qform_stereo_eq_zero {A : Matrix (Fin 6) (Fin 6) ℝ} (hA : Aᵀ = A)
    {P₀ : Fin 6 → ℝ} (hP₀ : qform A P₀ = 0) (x : Fin 6 → ℝ) :
    qform A (stereo A P₀ x) = 0 := by
  rw [show stereo A P₀ x = qform A x • P₀ + (-(2 * bilin A P₀ x)) • x by
    rw [stereo, sub_eq_add_neg, ← neg_smul]]
  rw [qform_smul_add A hA (qform A x) (-(2 * bilin A P₀ x)) P₀ x]
  simp only [hP₀, mul_zero, zero_add]
  ring

-- Theorem (S2): `stereo` vanishes to order two along the ray of `P₀`: shifting `δ` by any
-- multiple of `P₀` only rescales `stereo`.
theorem stereo_smul_add_smul {A : Matrix (Fin 6) (Fin 6) ℝ} (hA : Aᵀ = A)
    {P₀ : Fin 6 → ℝ} (hP₀ : qform A P₀ = 0) (c ε : ℝ) (δ : Fin 6 → ℝ) :
    stereo A P₀ (c • P₀ + ε • δ) = ε ^ 2 • stereo A P₀ δ := by
  have hBsym : bilin A P₀ P₀ = 0 := by
    rw [show bilin A P₀ P₀ = qform A P₀ from rfl, hP₀]
  have hQx : qform A (c • P₀ + ε • δ) = 2 * c * ε * bilin A P₀ δ + ε ^ 2 * qform A δ := by
    rw [qform_smul_add A hA c ε P₀ δ, hP₀]
    ring
  have hBx : bilin A P₀ (c • P₀ + ε • δ) = ε * bilin A P₀ δ := by
    rw [bilin_add_right, bilin_smul_right, bilin_smul_right, hBsym]
    ring
  rw [show stereo A P₀ (c • P₀ + ε • δ)
      = qform A (c • P₀ + ε • δ) • P₀
        + (-(2 * bilin A P₀ (c • P₀ + ε • δ))) • (c • P₀ + ε • δ) by
    rw [stereo, sub_eq_add_neg, ← neg_smul]]
  rw [hQx, hBx]
  rw [show stereo A P₀ δ
      = qform A δ • P₀ + (-(2 * bilin A P₀ δ)) • δ by
    rw [stereo, sub_eq_add_neg, ← neg_smul]]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

-- Theorem: `p3vec` is homogeneous of degree three.
theorem p3vec_smul (q : ℝ[X]) (c : ℝ) (x : Fin 7 → ℝ) :
    p3vec q (c • x) = c ^ 3 * p3vec q x := by
  rw [p3vec, p3vec]
  have h : aeval (companion7 q) (polyOfVec (c • x))
      = c • aeval (companion7 q) (polyOfVec x) := by
    have := aeval_polyOfVec_smul_add q c 0 x 0
    simpa using this
  rw [h, smul_pow, Matrix.trace_smul, smul_eq_mul]

-- Theorem (S3): on the cone, `stereo` is a scalar multiple of `x`, and the reduced cubic
-- scales by the cube of that multiple: `Cf (stereo x) = -8 (B P₀ x)^3 Cf x`.
theorem p3vec_Lcomb_stereo_of_qform_zero (q : ℝ[X]) {P₀ x : Fin 6 → ℝ}
    (hx : qform (Gram q) x = 0) :
    p3vec q (Lcomb q (stereo (Gram q) P₀ x))
      = -8 * (bilin (Gram q) P₀ x) ^ 3 * p3vec q (Lcomb q x) := by
  have hvec : stereo (Gram q) P₀ x = (-2 * bilin (Gram q) P₀ x) • x := by
    rw [stereo, hx]
    module
  rw [hvec, Lcomb_smul, p3vec_smul]
  ring

/-! ### B. The triple-sum formula and continuity of the cubic

`p3vec q w = trace ((aeval M (polyOfVec w)) ^ 3)` expands, in the monomial basis, into the
triple sum `∑ i j k wᵢ wⱼ wₖ trace (M ^ (i + j + k))`.  This makes `p3vec` a polynomial
function of `w`, hence continuous, and is the bridge that turns the parametrised cone into a
sextic in the line parameter. -/

-- Theorem: `p3vec` is the triple sum of `wᵢ wⱼ wₖ trace (M ^ (i + j + k))`.
theorem p3vec_eq_sum (q : ℝ[X]) (w : Fin 7 → ℝ) :
    p3vec q w = ∑ i, ∑ j, ∑ k,
      w i * w j * w k
        * Matrix.trace ((companion7 q) ^ (i.val + j.val + k.val)) := by
  have hcube : (aeval (companion7 q) (polyOfVec w)) ^ 3 =
      ∑ i, ∑ j, ∑ k, (w i * w j * w k) •
        (companion7 q) ^ (i.val + j.val + k.val) := by
    rw [pow_succ, aeval_polyOfVec_sq, aeval_polyOfVec]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_add]
  rw [p3vec, hcube, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Matrix.trace_smul, smul_eq_mul]

-- Theorem: `p3vec` is continuous in its vector argument.
theorem continuous_p3vec (q : ℝ[X]) : Continuous (p3vec q) := by
  rw [show p3vec q = fun w : Fin 7 → ℝ => ∑ i, ∑ j, ∑ k,
      w i * w j * w k
        * Matrix.trace ((companion7 q) ^ (i.val + j.val + k.val)) from
    funext (p3vec_eq_sum q)]
  fun_prop

/-! ### D. A P-constructible cone point

Given P-constructible directions `e` (negative) and `f` (positive) for the trace form,
the light cone meets the segment between them at a P-constructible point `P₀`. -/

-- Theorem: if `e` is P-constructible with `Q e < 0` and `f` is P-constructible with
-- `Q f > 0`, then the cone `{Q = 0}` contains a P-constructible nonzero point, namely the
-- second intersection of the line `e + t f` with the cone.
theorem exists_isotropic_Pconstructible (q : ℝ[X]) (hq : ∀ k, PConstructible (q.coeff k))
    {e f : Fin 6 → ℝ} (he : ∀ i, PConstructible (e i)) (hf : ∀ i, PConstructible (f i))
    (heQ : qform (Gram q) e < 0) (hfQ : 0 < qform (Gram q) f) :
    ∃ P₀ : Fin 6 → ℝ,
      (∀ i, PConstructible (P₀ i)) ∧ qform (Gram q) P₀ = 0 ∧ P₀ ≠ 0 := by
  have hG : ∀ i j, PConstructible (Gram q i j) := Gram_Pconstructible q hq
  have hQe : PConstructible (qform (Gram q) e) := bilin_Pconstructible hG he he
  have hQf : PConstructible (qform (Gram q) f) := bilin_Pconstructible hG hf hf
  have hB : PConstructible (bilin (Gram q) e f) := bilin_Pconstructible hG he hf
  obtain ⟨t, htP, htpos, htroot⟩ := exists_pos_quadratic_root hQf hB hQe hfQ heQ
  refine ⟨e + t • f, ?_, ?_, ?_⟩
  · intro i
    exact PConstructible.add (he i) (PConstructible.mul htP (hf i))
  · have hqform : qform (Gram q) (e + t • f) =
        qform (Gram q) e + 2 * t * bilin (Gram q) e f + t ^ 2 * qform (Gram q) f := by
      rw [show e + t • f = (1 : ℝ) • e + t • f by rw [one_smul]]
      rw [qform_smul_add (Gram q) (Gram_symm q) 1 t e f]
      ring
    rw [hqform]
    linear_combination htroot
  · intro h0
    have heq : e = -(t • f) := eq_neg_of_add_eq_zero_left h0
    have hQe' : qform (Gram q) (-(t • f)) < 0 := by rw [← heq]; exact heQ
    have hneg : qform (Gram q) (-(t • f)) = qform (Gram q) (t • f) := by
      rw [show -(t • f) = (-1 : ℝ) • (t • f) by rw [neg_one_smul], qform_smul]
      norm_num
    rw [hneg, qform_smul] at hQe'
    nlinarith [hfQ, sq_pos_of_pos htpos]

/-! ### E1. Rational witnesses by density

The sign certificate only shows that some direction gives `Φ` a given sign; density of
`ℚⁿ` in `ℝⁿ` then supplies a rational (hence P-constructible) direction with the same
strict sign. -/

-- Theorem: a continuous function positive at one point is positive at a rational vector.
theorem exists_rat_vec_pos (n : ℕ) {g : (Fin n → ℝ) → ℝ} (hg : Continuous g)
    {x : Fin n → ℝ} (hx : 0 < g x) :
    ∃ r : Fin n → ℚ, 0 < g (fun i => (r i : ℝ)) := by
  have hopen : IsOpen {y : Fin n → ℝ | 0 < g y} := isOpen_lt continuous_const hg
  have hne : ({y : Fin n → ℝ | 0 < g y}).Nonempty := ⟨x, hx⟩
  have hdense : Dense (Set.range (fun r : Fin n → ℚ => fun i => (r i : ℝ))) :=
    DenseRange.piMap (fun _ : Fin n => (Rat.denseRange_cast : DenseRange ((↑) : ℚ → ℝ)))
  obtain ⟨y, hys, hyU⟩ := hdense.exists_mem_open hopen hne
  obtain ⟨r, rfl⟩ := hys
  exact ⟨r, hyU⟩

end

end Pconstructible
