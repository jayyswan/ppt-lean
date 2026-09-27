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
import Pptc.TotallyReal.Certificate

/-! # Pptc.TotallyReal.Main

**Theorem 7 and Theorem 8 of `TotallyReal/PLAN.md`**: every real root of a totally real
septic (resp. octic) with P-constructible coefficients is P-constructible. For septics this
lifts to *every* real root of any septic whatsoever (`root_Pconstructible_deg7_coeffs`); for
octics the degree-8 result proved here is the totally real / splitting case
(`root_Pconstructible_totallyReal_eight`), and the nonreal-octic case is recorded as future
work in `PLAN.md` §5.

## The assembly

1. `exists_oddTschirnhaus` gives a P-constructible `b`-vector whose y-vector `y` has
   `S₁ = S₃ = S₅ = 0` and pairwise distinct entries.
2. By Lemma N (`TotallyReal/Newton.lean`), `χ = ∏ᵢ (X − yᵢ)` has the septic or octic
   shape, and its coefficients are P-constructible (`YSpace`).
3. `χ` is the characteristic polynomial of `Φ_b (companionN q)`, so `β = Φ_b (α)`, for a
   root `α` of `q`, is a real root of `χ`. By Lemma E7 (resp. E8) `β` is
   P-constructible.
4. `Φ_b(X) − β` is a nonzero polynomial of degree `≤ 6` (resp. `≤ 7`) with
   P-constructible coefficients having `α` as a root. Nonzero because the `yᵢ` are
   distinct and there are `n` of them, so `Φ_b` takes `n` distinct values and is
   nonconstant. `root_Pconstructible_le_six_coeffs` (resp. Theorem 7) then returns `α`.

Steps 1–4 do not depend on `n` being `7` or `8`, except through the shape of `χ` and
through the degree bound of step 4. Both are therefore passed in as hypotheses
(`hengine`, `hrec`) of the single lemma `root_Pconstructible_of_odd_shaped`, which is
what Theorems 7 and 8 below share.

## Why the non-totally-real cases are not needed here

`root_Pconstructible_of_nonreal_root` and `root_Pconstructible_of_nonSeparable` in
`Pptc/DegreeSeven` already settle a septic with a nonreal root, or a non-separable one.
So `root_Pconstructible_deg7_coeffs` below is a case split, and only one case is new.
Both of those lemmas are restricted to degree `7`. The non-separable one lifts to degree `8`
for free — it is `root_Pconstructible_of_nonSeparable_eight` below, the same `gcd q q'`
argument with Theorem 7 in place of the sextic engine — so the non-separable branch of the
octic case is closed as well, and `root_Pconstructible_totallyReal_eight` is proved outright.

The nonreal-root one does **not** lift for free: `root_Pconstructible_of_nonreal_root` is
the Bring–Jerrard reduction, and every ingredient of that reduction is dimension-fixed to
degree `7`. A separable octic that does not split over `ℝ` is therefore **not** covered by
this file. The missing statement is the degree-8 analogue of
`Pptc.DegreeSeven.root_Pconstructible_of_nonreal_root`:

```
∀ {q : ℝ[X]}, q.natDegree = 8 → (∀ k, PConstructible (q.coeff k)) →
  {z : ℂ} → (q.map (algebraMap ℝ ℂ)).eval z = 0 → z.im ≠ 0 →
  {β : ℝ} → q.eval β = 0 → PConstructible β
```

(the `z` is available from `exists_nonreal_root_of_not_splits` above). The septic proof is
`root_Pconstructible_of_one_conjugate_pair` / `root_Pconstructible_of_two_conjugate_pairs_monic`,
and *every* ingredient of that reduction is dimension-fixed to degree `7`: `Gram`, `stereo`,
`p1vec`, `p3vec`, `Lcomb`, `qform`, `Hmat`, `hermiteForm`, the `Fin 6` vectors and the sextic
`exists_sextic_along_line`. A degree-`8` version needs all of those rebuilt in dimension `7`,
and is a new result rather than a re-run of an existing proof. It is recorded as future work
in `PLAN.md` §5.
-/

namespace Pconstructible

open Polynomial

noncomputable section

/-! ### The recovery polynomial -/

/-- The polynomial `Φ_b(X) − β`, which has `α` as a root. It is nonzero precisely when
`β` is one of the values of `Φ_b` at the roots, and its degree is bounded by the number
of those values. -/
noncomputable def recoveryPoly {n : ℕ} (_αs : Fin n → ℝ) (b : Fin n → ℝ) (β : ℝ) : ℝ[X] :=
  bPoly b - C β

theorem recoveryPoly_eval_root {n : ℕ} {q : ℝ[X]} {αs : Fin n → ℝ} {b : Fin n → ℝ}
    (_hαs : ∀ i : Fin n, q.eval (αs i) = 0) (_hb : ∀ k, PConstructible (b k))
    {i : Fin n} (hβ : β = yvec αs b i) :
    (recoveryPoly αs b β).eval (αs i) = 0 := by
  simp only [recoveryPoly, eval_sub, eval_C, hβ, yvec_eq_bPoly_eval]
  ring

/-- The degree of the recovery polynomial is `< n` as soon as `n > 0`, i.e. `≤ n − 1` and
so `≤ 6` for `n = 7` and `≤ 7` for `n = 8`. This is the statement of
`recoveryPoly_degree_lt` below, which however omits `0 < n`. -/
theorem recoveryPoly_degree_lt_of_pos {n : ℕ} (h0 : 0 < n) (αs : Fin n → ℝ) (b : Fin n → ℝ)
    (β : ℝ) : (recoveryPoly αs b β).natDegree < n := by
  have h1 : (bPoly b).natDegree ≤ n - 1 := bPoly_natDegree_le b
  have hmax := Polynomial.natDegree_sub_le (bPoly b) (Polynomial.C β)
  rw [Polynomial.natDegree_C] at hmax
  have hsub : (recoveryPoly αs b β).natDegree ≤ n - 1 := by
    rw [recoveryPoly]
    exact hmax.trans (max_le h1 (Nat.zero_le _))
  omega

/-- **The degree of the recovery polynomial: `< n`.** For `n = 7` this is `≤ 6` and for
`n = 8` it is `≤ 7`.

The hypothesis `0 < n` is necessary, not cosmetic: at `n = 0` the sum defining `bPoly b`
is empty, so `bPoly b = 0` and `recoveryPoly αs b β = -C β` has `natDegree = 0 = n`. The
`≤ n − 1` form of the bound, which holds at `n = 0` as well, is
`YSpace.bPoly_natDegree_le`; the workhorse proof is
`recoveryPoly_degree_lt_of_pos`. -/
theorem recoveryPoly_degree_lt {n : ℕ} (h0 : 0 < n) (αs : Fin n → ℝ) (b : Fin n → ℝ)
    (β : ℝ) : (recoveryPoly αs b β).natDegree < n :=
  recoveryPoly_degree_lt_of_pos h0 αs b β

/-- The recovery polynomial is nonzero at any value of `Φ_b` when the values are distinct
and there are at least two of them: `Φ_b` then takes `n ≥ 2` distinct values, so it is
not the constant polynomial `β`. -/
theorem recoveryPoly_ne_of_mem {n : ℕ} (h0 : 0 < n) (hn : 2 ≤ n) {αs : Fin n → ℝ}
    {b : Fin n → ℝ} (hnd : Function.Injective (yvec αs b)) {β : ℝ}
    (_hβ : ∃ i : Fin n, yvec αs b i = β) : recoveryPoly αs b β ≠ 0 := by
  intro h
  have hb' : bPoly b = Polynomial.C β := sub_eq_zero.mp h
  have h1n : 1 < n := by omega
  have key : ∀ j : Fin n, yvec αs b j = β := by
    intro j
    simp only [← yvec_eq_bPoly_eval, hb', eval_C]
  have key2 : yvec αs b ⟨0, h0⟩ = yvec αs b ⟨1, h1n⟩ :=
    (key ⟨0, h0⟩).trans (key ⟨1, h1n⟩).symm
  have hfin : (⟨0, h0⟩ : Fin n) = ⟨1, h1n⟩ := hnd key2
  have hval := congrArg Fin.val hfin
  simp only at hval
  omega

/-- The recovery polynomial is nonzero when the y-entries are distinct, because then
`Φ_b` takes `n ≥ 2` distinct values and so is nonconstant. -/
theorem recoveryPoly_ne {n : ℕ} (h0 : 0 < n) (hn : 2 ≤ n) {q : ℝ[X]} {αs : Fin n → ℝ}
    {b : Fin n → ℝ} (_hαs : ∀ i : Fin n, q.eval (αs i) = 0)
    (hnd : Function.Injective (yvec αs b)) :
    recoveryPoly αs b (yvec αs b ⟨0, h0⟩) ≠ 0 :=
  recoveryPoly_ne_of_mem h0 hn hnd ⟨⟨0, h0⟩, rfl⟩

/-- The recovery polynomial has P-constructible coefficients as soon as `b` and `β` do. -/
theorem recoveryPoly_coeff_Pconstructible {n : ℕ} {αs : Fin n → ℝ} {b : Fin n → ℝ} {β : ℝ}
    (hb : ∀ k, PConstructible (b k)) (hβ : PConstructible β) (k : ℕ) :
    PConstructible ((recoveryPoly αs b β).coeff k) := by
  have hz : PConstructible (0 : ℝ) := zero_Pconstructible
  by_cases hk : k = 0
  · subst hk
    simp only [recoveryPoly, Polynomial.coeff_sub, Polynomial.coeff_C]
    exact PConstructible.sub (bPoly_coeffs_Pconstructible hb 0) hβ
  · have hz' : (Polynomial.C β).coeff k = 0 := Polynomial.coeff_C_of_ne_zero hk
    simp only [recoveryPoly, Polynomial.coeff_sub, hz']
    exact PConstructible.sub (bPoly_coeffs_Pconstructible hb k) hz

/-! ### Roots of `q`, and a non-real root when `q` does not split -/

/-- The algebra map `ℝ → ℂ` is the real embedding: `algebraMap ℝ ℂ r` is `r` read as a
complex number. -/
theorem algebraMap_real (r : ℝ) : algebraMap ℝ ℂ r = r := by
  norm_num [Algebra.smul_def, smul_eq_mul]

/-- **A nonzero real polynomial that does not split over `ℝ` has a non-real complex
root.** The real roots embed into the complex roots (`map_roots_le_of_injective`), and a
split polynomial over `ℂ` has as many complex roots as its degree, so a drop in the count
of real roots below the degree forces an extra, hence non-real, complex root.
Separability is what makes the extra root a new one rather than a repeat. -/
theorem exists_nonreal_root_of_not_splits {q : ℝ[X]} (hq0 : q ≠ 0) (hsep : q.Separable)
    (hns : ¬ q.Splits) :
    ∃ z : ℂ, (q.map (algebraMap ℝ ℂ)).eval z = 0 ∧ z.im ≠ 0 := by
  classical
  have hpnd : (q.map (algebraMap ℝ ℂ)).roots.Nodup := Polynomial.nodup_roots hsep.map
  have hpcard : (q.map (algebraMap ℝ ℂ)).roots.card = q.natDegree := by
    have h := (IsAlgClosed.splits (q.map (algebraMap ℝ ℂ))).natDegree_eq_card_roots
    rw [Polynomial.natDegree_map] at h
    exact h.symm
  have hle : q.roots.map (algebraMap ℝ ℂ) ≤ (q.map (algebraMap ℝ ℂ)).roots :=
    Polynomial.map_roots_le_of_injective q (algebraMap ℝ ℂ).injective
  have hcardeq : (q.roots.map (algebraMap ℝ ℂ)).card = q.roots.card :=
    Multiset.card_map _ _
  have hle'' : q.roots.card ≤ q.natDegree := by
    have h := Multiset.card_le_card hle
    rwa [hcardeq, hpcard] at h
  have hne : q.roots.card ≠ q.natDegree := fun h =>
    hns (Polynomial.splits_iff_card_roots.mpr h)
  have hcardlt : q.roots.card < (q.map (algebraMap ℝ ℂ)).roots.card := by omega
  obtain ⟨z, hz, hzt⟩ :
      ∃ z ∈ (q.map (algebraMap ℝ ℂ)).roots, z ∉ q.roots.map (algebraMap ℝ ℂ) := by
    by_contra hc
    push Not at hc
    have hle' : (q.map (algebraMap ℝ ℂ)).roots ≤ q.roots.map (algebraMap ℝ ℂ) :=
      Multiset.le_iff_subset hpnd |>.mpr hc
    have hcard := Multiset.card_le_card hle'
    omega
  refine ⟨z, (Polynomial.mem_roots'.mp hz).2, ?_⟩
  intro hzi
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = z.re := ⟨z.re, rfl⟩
  have hz1 : z = (w : ℂ) := by
    rw [hw, Complex.ext_iff]
    exact ⟨rfl, by simp [hzi]⟩
  have h1 : q.eval₂ (algebraMap ℝ ℂ) z = 0 := by
    rw [← Polynomial.eval_map]
    exact (Polynomial.mem_roots'.mp hz).2
  have hz1' : z = (algebraMap ℝ ℂ) w := hz1.trans (algebraMap_real w).symm
  have h3 : q.eval₂ (algebraMap ℝ ℂ) ((algebraMap ℝ ℂ) w) = 0 := by
    rw [← hz1']
    exact h1
  have h2 : (algebraMap ℝ ℂ) (q.eval w) = 0 := by
    rw [Polynomial.eval₂_at_apply] at h3
    exact h3
  have hroot : q.eval w = 0 := (algebraMap ℝ ℂ).injective h2
  have hmem : w ∈ q.roots := (Polynomial.mem_roots hq0).mpr hroot
  have hkey : (algebraMap ℝ ℂ) w = z := hz1'.symm
  exact hzt (Multiset.mem_map.mpr ⟨w, hmem, hkey⟩)

/-- **The `n` real roots of a separable `q` of degree `n` splitting over `ℝ`**, listed as a
`Fin n → ℝ`, together with the facts that they are pairwise distinct and that they
exhaust the real roots of `q`. The enumeration is `Finset.orderEmbOfFin` applied to
`q.roots.toFinset`, whose cardinality is the degree by `splits_iff_card_roots`; the
exhaustion is `Polynomial.mem_roots`. -/
theorem exists_αs_of_splits {n : ℕ} {q : ℝ[X]} (hq0 : q ≠ 0) (hsep : q.Separable)
    (hnat : q.natDegree = n) (hsplit : q.Splits) :
    ∃ αs : Fin n → ℝ, (∀ i : Fin n, q.eval (αs i) = 0) ∧ Function.Injective αs ∧
      (∀ β : ℝ, q.eval β = 0 → ∃ i : Fin n, αs i = β) := by
  classical
  have hcard : q.roots.toFinset.card = n := by
    have h1 := Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep)
    have h2 : q.roots.card = q.natDegree := Polynomial.splits_iff_card_roots.mp hsplit
    rw [h1, h2, hnat]
  refine ⟨fun i => q.roots.toFinset.orderEmbOfFin hcard i, ?_, ?_, ?_⟩
  · intro i
    have hmem : q.roots.toFinset.orderEmbOfFin hcard i ∈ (q.roots : Multiset ℝ) := by
      rw [← Multiset.mem_toFinset]
      exact q.roots.toFinset.orderEmbOfFin_mem hcard i
    exact (Polynomial.mem_roots'.mp hmem).2
  · exact q.roots.toFinset.orderEmbOfFin hcard |>.injective
  · intro β hβ
    have hmem : β ∈ q.roots.toFinset := by
      rw [Multiset.mem_toFinset]
      exact (Polynomial.mem_roots hq0).mpr hβ
    have hmem' : β ∈ Set.range (q.roots.toFinset.orderEmbOfFin hcard) := by
      rw [q.roots.toFinset.range_orderEmbOfFin hcard]
      exact hmem
    obtain ⟨i, hi⟩ := Set.mem_range.mp hmem'
    exact ⟨i, hi⟩

/-! ### The two shapes, and the two engines -/

/-- **The septic shape's data are the coefficients of the y-polynomial.** If
`(prodSubY y).eval t = t · cubicVal r₀ r₁ r₂ 1 (t²) − e₇` for all `t`, then the
polynomial identity `prodSubY y = X⁷ + r₂X⁵ + r₁X³ + r₀X − e₇` holds
(`Polynomial.funext`), so `e₇` is minus the constant coefficient and `rⱼ` is the
coefficient of `X^{2j+1}`. -/
theorem cubic_seven_coeff_agrees {y : Fin 7 → ℝ} {e₇ r₀ r₁ r₂ : ℝ}
    (h : ∀ t : ℝ, (prodSubY y).eval t = t * cubicVal r₀ r₁ r₂ 1 (t ^ 2) - e₇) :
    e₇ = -(prodSubY y).coeff 0 ∧ r₀ = (prodSubY y).coeff 1 ∧
      r₁ = (prodSubY y).coeff 3 ∧ r₂ = (prodSubY y).coeff 5 := by
  have heq : prodSubY y = X ^ 7 + C r₂ * X ^ 5 + C r₁ * X ^ 3 + X * C r₀ - C e₇ := by
    refine Polynomial.funext (fun t => ?_)
    rw [h]
    simp only [cubicVal, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C]
    ring
  have h0 := congrArg (fun f : ℝ[X] => f.coeff 0) heq
  have h1 := congrArg (fun f : ℝ[X] => f.coeff 1) heq
  have h3 := congrArg (fun f : ℝ[X] => f.coeff 3) heq
  have h5 := congrArg (fun f : ℝ[X] => f.coeff 5) heq
  constructor
  · rw [h0]; norm_num
  constructor
  · rw [h1]; norm_num
  constructor
  · rw [h3]; norm_num
  · rw [h5]; norm_num

/-- **The octic shape's data are the coefficients of the y-polynomial**, as in
`cubic_seven_coeff_agrees`: for `χ(t) = Q(t²) − e₇t` one gets `qⱼ` at the even indices and
`e₇` as minus the coefficient of `X`. -/
theorem quartic_eight_coeff_agrees {y : Fin 8 → ℝ} {e₇ q₀ q₁ q₂ q₃ : ℝ}
    (h : ∀ t : ℝ, (prodSubY y).eval t = quarticVal q₀ q₁ q₂ q₃ 1 (t ^ 2) - e₇ * t) :
    e₇ = -(prodSubY y).coeff 1 ∧ q₀ = (prodSubY y).coeff 0 ∧ q₁ = (prodSubY y).coeff 2 ∧
      q₂ = (prodSubY y).coeff 4 ∧ q₃ = (prodSubY y).coeff 6 := by
  have heq : prodSubY y = X ^ 8 + C q₃ * X ^ 6 + C q₂ * X ^ 4 + C q₁ * X ^ 2 + C q₀
      - X * C e₇ := by
    refine Polynomial.funext (fun t => ?_)
    rw [h]
    simp only [quarticVal, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C]
    ring
  have h0 := congrArg (fun f : ℝ[X] => f.coeff 0) heq
  have h1 := congrArg (fun f : ℝ[X] => f.coeff 1) heq
  have h2 := congrArg (fun f : ℝ[X] => f.coeff 2) heq
  have h4 := congrArg (fun f : ℝ[X] => f.coeff 4) heq
  have h6 := congrArg (fun f : ℝ[X] => f.coeff 6) heq
  constructor
  · rw [h1]; norm_num
  constructor
  · rw [h0]; norm_num
  constructor
  · rw [h2]; norm_num
  constructor
  · rw [h4]; norm_num
  · rw [h6]; norm_num

/-- **The septic engine.** A real root of `χ = prodSubY y` for a seven-tuple `y` with
vanishing `S₁, S₃, S₅` and P-constructible coefficients of `χ` is P-constructible: the
shape gives `β · R(β²) = e₇` with `R` a monic cubic of P-constructible coefficients, and
Lemma E7 applies. -/
theorem prodSubY_root_Pconstructible_seven {y : Fin 7 → ℝ}
    (hcoeff : ∀ k, PConstructible ((prodSubY y).coeff k)) (h1 : psumY y 1 = 0)
    (h3 : psumY y 3 = 0) (h5 : psumY y 5 = 0) {β : ℝ} (hβ : (prodSubY y).eval β = 0) :
    PConstructible β := by
  obtain ⟨e₇, r₀, r₁, r₂, hshape⟩ := exists_cubic_seven h1 h3 h5
  obtain ⟨he7, hr0, hr1, hr2⟩ := cubic_seven_coeff_agrees hshape
  have hd : PConstructible e₇ ∧ PConstructible r₀ ∧ PConstructible r₁ ∧
      PConstructible r₂ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [he7]; pconstructible
    · rw [hr0]; pconstructible
    · rw [hr1]; pconstructible
    · rw [hr2]; pconstructible
  obtain ⟨he7', hr0', hr1', hr2'⟩ := hd
  have hβ' : β * cubicVal r₀ r₁ r₂ 1 (β ^ 2) = e₇ := by
    have h := hshape β
    rw [hβ] at h
    linarith
  exact negHalf_cubic_root_Pconstructible hr0' hr1' hr2' he7' hβ'

/-- **The octic engine.** As `prodSubY_root_Pconstructible_seven`, with the quartic shape
`χ(t) = Q(t²) − e₇t` and Lemma E8. -/
theorem prodSubY_root_Pconstructible_eight {y : Fin 8 → ℝ}
    (hcoeff : ∀ k, PConstructible ((prodSubY y).coeff k)) (h1 : psumY y 1 = 0)
    (h3 : psumY y 3 = 0) (h5 : psumY y 5 = 0) {β : ℝ} (hβ : (prodSubY y).eval β = 0) :
    PConstructible β := by
  obtain ⟨e₇, q₀, q₁, q₂, q₃, hshape⟩ := exists_quartic_eight h1 h3 h5
  obtain ⟨he7, hq0, hq1, hq2, hq3⟩ := quartic_eight_coeff_agrees hshape
  have hd : PConstructible e₇ ∧ PConstructible q₀ ∧ PConstructible q₁ ∧ PConstructible q₂ ∧
      PConstructible q₃ := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [he7]; pconstructible
    · rw [hq0]; pconstructible
    · rw [hq1]; pconstructible
    · rw [hq2]; pconstructible
    · rw [hq3]; pconstructible
  obtain ⟨he7', hq0', hq1', hq2', hq3'⟩ := hd
  have hβ' : quarticVal q₀ q₁ q₂ q₃ 1 (β ^ 2) = e₇ * β := by
    have h := hshape β
    rw [hβ] at h
    ring_nf at h
    linarith
  exact half_quartic_root_Pconstructible hq0' hq1' hq2' hq3' he7' hβ'

/-! ### The common assembly, shared by Theorems 7 and 8 -/

/-- **Steps 1–4 of the module docstring, for `n ∈ {7, 8}`.** `hengine` is the shape
dependent step 3 (a real root of `χ = prodSubY y` is P-constructible) and `hrec` is the
degree dependent last step (a nonzero polynomial of degree `< n` with P-constructible
coefficients has P-constructible real roots — by `root_Pconstructible_le_six_coeffs` for
`n = 7`, and by `root_Pconstructible_deg7_coeffs` for `n = 8`, where the recovery
polynomial has degree `≤ 7`).

The four steps: `exists_oddTschirnhaus` supplies a P-constructible `b` whose y-vector `y`
has `S₁ = S₃ = S₅ = 0` and distinct entries; `companionN_charpoly_aeval_isRoot` together
with `prodSubY_yvec_eq_charpoly_aeval` makes `β = Φ_b(α)` a real root of `χ`, so `hengine`
makes it P-constructible; and `Φ_b − β` is then a nonzero polynomial of degree `< n` with
P-constructible coefficients and root `α`, which `hrec` settles. -/
theorem root_Pconstructible_of_odd_shaped {n : ℕ} (hn : n = 7 ∨ n = 8) {q : ℝ[X]}
    (hmon : q.Monic) (hsep : q.Separable) (hnat : q.natDegree = n)
    (hcoef : ∀ k, PConstructible (q.coeff k)) {αs : Fin n → ℝ}
    (hαs : ∀ i : Fin n, q.eval (αs i) = 0) (hndαs : Function.Injective αs)
    (hcover : ∀ β : ℝ, q.eval β = 0 → ∃ i : Fin n, αs i = β)
    (hengine : ∀ (y : Fin n → ℝ), (∀ k, PConstructible ((prodSubY y).coeff k)) →
      psumY y 1 = 0 → psumY y 3 = 0 → psumY y 5 = 0 →
      {β : ℝ} → (prodSubY y).eval β = 0 → PConstructible β)
    (hrec : ∀ (p : ℝ[X]), p ≠ 0 → p.natDegree < n →
      (∀ k, PConstructible (p.coeff k)) →
      {β : ℝ} → p.eval β = 0 → PConstructible β)
    {α : ℝ} (hα : q.eval α = 0) : PConstructible α := by
  obtain ⟨b, hb, hbinj, h1, h3, h5⟩ :=
    exists_oddTschirnhaus hn hmon hnat hsep hcoef hαs hndαs
  have hqn : q.coeff n = 1 := by
    rw [← hnat]
    exact hmon.coeff_natDegree
  have hβroot : (prodSubY (yvec αs b)).eval ((bPoly b).eval α) = 0 := by
    have hcp := companionN_charpoly_aeval_isRoot (n := n) (φ := bPoly b) hα
      (show 0 < n by omega) hqn (show q.natDegree ≤ n by omega)
    rw [← prodSubY_yvec_eq_charpoly_aeval hmon (show 0 < n by omega) hnat hsep hαs hndαs]
      at hcp
    exact hcp
  have hcoeffY : ∀ k, PConstructible ((prodSubY (yvec αs b)).coeff k) :=
    prodSubY_yvec_coeff_Pconstructible hmon (show 0 < n by omega) hnat hsep hcoef hαs hndαs hb
  have hβ : PConstructible ((bPoly b).eval α) := hengine _ hcoeffY h1 h3 h5 hβroot
  obtain ⟨i, hi⟩ := hcover α hα
  have hmem : ∃ j : Fin n, yvec αs b j = (bPoly b).eval α := by
    refine ⟨i, ?_⟩
    rw [← yvec_eq_bPoly_eval, hi]
  have hne : recoveryPoly αs b ((bPoly b).eval α) ≠ 0 :=
    recoveryPoly_ne_of_mem (show 0 < n by omega) (show 2 ≤ n by omega) hbinj hmem
  have hdeg : (recoveryPoly αs b ((bPoly b).eval α)).natDegree < n :=
    recoveryPoly_degree_lt (show 0 < n by omega) αs b ((bPoly b).eval α)
  have hcoeffR : ∀ k, PConstructible ((recoveryPoly αs b ((bPoly b).eval α)).coeff k) :=
    recoveryPoly_coeff_Pconstructible hb hβ
  have hroot : (recoveryPoly αs b ((bPoly b).eval α)).eval α = 0 := by
    have hkey : (bPoly b).eval α = yvec αs b i := by
      rw [← hi, yvec_eq_bPoly_eval]
    have hh := recoveryPoly_eval_root hαs hb hkey
    rwa [hi] at hh
  exact hrec _ hne hdeg hcoeffR hroot

/-! ### Theorem 7: the totally real septic case -/

/-- **Theorem 7 (totally real case).** Every real root of a monic totally real separable
septic with P-constructible coefficients is P-constructible. -/
theorem root_Pconstructible_totallyReal_seven {q : ℝ[X]} (hmon : q.Monic) (h7 : q.natDegree = 7)
    (hsplit : q.Splits)
    (hcoef : ∀ k, PConstructible (q.coeff k)) {α : ℝ} (hα : q.eval α = 0) :
    PConstructible α := by
  by_cases hsep : q.Separable
  · have hq0 : q ≠ 0 := by
      intro h
      have h' := h7
      rw [h] at h'
      norm_num at h'
    obtain ⟨αs, hαs, hndαs, hcover⟩ := exists_αs_of_splits hq0 hsep h7 hsplit
    have hengine : ∀ (y : Fin 7 → ℝ), (∀ k, PConstructible ((prodSubY y).coeff k)) →
        psumY y 1 = 0 → psumY y 3 = 0 → psumY y 5 = 0 →
        {β : ℝ} → (prodSubY y).eval β = 0 → PConstructible β := by
      intro y hcoeff h1' h3' h5' β hβ
      exact prodSubY_root_Pconstructible_seven hcoeff h1' h3' h5' hβ
    have hrec : ∀ (p : ℝ[X]), p ≠ 0 → p.natDegree < 7 →
        (∀ k, PConstructible (p.coeff k)) →
        {β : ℝ} → p.eval β = 0 → PConstructible β := by
      intro p hp hd hc β hroot
      exact root_Pconstructible_le_six_coeffs hp (by omega) hc hroot
    exact root_Pconstructible_of_odd_shaped (Or.inl rfl) hmon hsep h7 hcoef hαs hndαs
      hcover hengine hrec hα
  · exact root_Pconstructible_of_nonSeparable hmon hcoef (by omega) hsep hα

/-- **Theorem 7.** Every real root of a septic with P-constructible coefficients is
P-constructible. The three cases are: degree `≤ 6` (`root_Pconstructible_le_six_coeffs`),
non-separable (`root_Pconstructible_of_nonSeparable`), a nonreal root
(`root_Pconstructible_of_nonreal_root`), and the totally real case above. -/
theorem root_Pconstructible_deg7_coeffs {q : ℝ[X]} (hq : q ≠ 0) (h7 : q.natDegree ≤ 7)
    (hcoef : ∀ k, PConstructible (q.coeff k)) {α : ℝ} (hα : q.eval α = 0) :
    PConstructible α := by
  by_cases hdeg6 : q.natDegree ≤ 6
  · exact root_Pconstructible_le_six_coeffs hq hdeg6 hcoef hα
  · have hnat : q.natDegree = 7 := by omega
    have hlc : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq
    set q₀ : ℝ[X] := Polynomial.C q.leadingCoeff⁻¹ * q with hq₀
    have hq₀ne : q₀ ≠ 0 := by
      rw [hq₀]
      exact mul_ne_zero (Polynomial.C_ne_zero.mpr (inv_ne_zero hlc)) hq
    have hmon : q₀.Monic :=
      Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ hlc)
    have hnat₀ : q₀.natDegree = 7 := by
      rw [hq₀, Polynomial.natDegree_C_mul (inv_ne_zero hlc), hnat]
    have hcoef₀ : ∀ k, PConstructible (q₀.coeff k) :=
      C_mul_coeff_Pconstructible (inv_Pconstructible (hcoef q.natDegree)) hcoef
    have hα₀ : q₀.eval α = 0 := by simp [hq₀, hα]
    by_cases hsep : q₀.Separable
    · by_cases hsp : q₀.Splits
      · exact root_Pconstructible_totallyReal_seven hmon hnat₀ hsp hcoef₀ hα₀
      · obtain ⟨z, hz, hzim⟩ := exists_nonreal_root_of_not_splits hq₀ne hsep hsp
        exact root_Pconstructible_of_nonreal_root hnat₀ hcoef₀ hz hzim hα₀
    · exact root_Pconstructible_of_nonSeparable hmon hcoef₀ (by omega) hsep hα₀

/-! ### Theorem 8: the totally real octic case -/

/-- **The degree-`8` analogue of `Pptc.DegreeSeven.root_Pconstructible_of_nonSeparable`.**
The argument there is degree-agnostic apart from its engine: `d = gcd q q'` is nonconstant,
`d ∣ q'`, and every real root of `q` is a root of either `d` or of the quotient `q / d`.
All that changes from `≤ 7` to `≤ 8` is the budget — `q'.natDegree ≤ 7` gives
`d.natDegree ≤ 7`, and `q / d` has degree `≤ 8 − 1 = 7` because `d` is nonconstant. Both
polynomials are therefore within `root_Pconstructible_deg7_coeffs`, i.e. Theorem 7 above,
which replaces `root_Pconstructible_le_six_coeffs` as the engine. -/
theorem root_Pconstructible_of_nonSeparable_eight {q : ℝ[X]} (hmon : q.Monic)
    (hcoeff : ∀ k, PConstructible (q.coeff k)) (hdeg : q.natDegree ≤ 8)
    (hns : ¬ q.Separable) {β : ℝ} (hβ : q.eval β = 0) : PConstructible β := by
  have hq0 : q ≠ 0 := hmon.ne_zero
  have hnat_ne : q.natDegree ≠ 0 := by
    intro h0
    exact hns (by
      rw [Polynomial.eq_one_of_monic_natDegree_zero hmon h0]
      exact Polynomial.separable_one)
  have hderiv_ne : q.derivative ≠ 0 := Polynomial.derivative_ne_zero.mpr hnat_ne
  have hdcoeff : ∀ i, PConstructible (q.derivative.coeff i) := by
    intro i
    rw [Polynomial.coeff_derivative]
    exact PConstructible.mul (hcoeff (i + 1))
      (PConstructible.add (nat_Pconstructible i) PConstructible.base_one)
  set d : Polynomial ℝ := EuclideanDomain.gcd q q.derivative with hddef
  have hdcoeffd : ∀ i, PConstructible (d.coeff i) := by
    rw [hddef]
    exact gcd_coeff_Pconstructible q q.derivative hcoeff hdcoeff
  have hdvd_q : d ∣ q := by
    rw [hddef]; exact EuclideanDomain.gcd_dvd_left q q.derivative
  have hdne : d ≠ 0 := by
    rw [hddef]
    intro hzero
    exact hq0 ((EuclideanDomain.gcd_eq_zero_iff).mp hzero).1
  have hddeg : d.natDegree ≤ 7 := by
    have hderiv_deg : q.derivative.natDegree ≤ 7 := by
      have h := Polynomial.natDegree_derivative_le q
      omega
    rw [hddef]
    exact le_trans
      (Polynomial.natDegree_le_of_dvd (EuclideanDomain.gcd_dvd_right q q.derivative)
        hderiv_ne) hderiv_deg
  have hdpos : 0 < d.natDegree := by
    have hnotunit : ¬ IsUnit d := by
      intro hu
      rw [hddef] at hu
      exact hns ((Polynomial.separable_def q).mpr (EuclideanDomain.gcd_isUnit_iff.mp hu))
    rw [Polynomial.isUnit_iff_degree_eq_zero] at hnotunit
    apply Nat.pos_of_ne_zero
    intro h0
    exact hnotunit (by simp [Polynomial.degree_eq_natDegree hdne, h0])
  have hlc_ne : d.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hdne
  have hlc_inv_ne : d.leadingCoeff⁻¹ ≠ 0 := inv_ne_zero hlc_ne
  set d0 : Polynomial ℝ := d * Polynomial.C d.leadingCoeff⁻¹ with hd0def
  have hd0monic : d0.Monic := by
    rw [hd0def]; exact Polynomial.monic_mul_leadingCoeff_inv hdne
  have hd0coeff : ∀ i, PConstructible (d0.coeff i) := by
    intro i
    rw [hd0def]
    exact coeff_mul_Pconstructible hdcoeffd
      (fun j => coeff_C_Pconstructible (inv_Pconstructible (hdcoeffd d.natDegree)) j) i
  have hd0ne : d0 ≠ 0 := by
    rw [hd0def]
    exact mul_ne_zero hdne (Polynomial.C_ne_zero.mpr hlc_inv_ne)
  have hd0nat : d0.natDegree = d.natDegree := by
    rw [hd0def]
    exact Polynomial.natDegree_mul_C hlc_inv_ne
  have hd0deg : d0.natDegree ≤ 7 := by rw [hd0nat]; exact hddeg
  have hd0pos : 1 ≤ d0.natDegree := by rw [hd0nat]; omega
  by_cases hd0β : d0.eval β = 0
  · exact root_Pconstructible_deg7_coeffs hd0ne hd0deg hd0coeff hd0β
  · have h0dvd_d : d0 ∣ d := ⟨Polynomial.C d.leadingCoeff, by
        rw [hd0def, mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hlc_ne,
          Polynomial.C_1, mul_one]⟩
    have h0dvd_q : d0 ∣ q := dvd_trans h0dvd_d hdvd_q
    have hq_eq : d0 * (q /ₘ d0) = q := by
      have hmod0 : q %ₘ d0 = 0 :=
        (Polynomial.modByMonic_eq_zero_iff_dvd hd0monic).mpr h0dvd_q
      have h := Polynomial.modByMonic_add_div q d0
      rw [hmod0, zero_add] at h
      exact h
    have hrcoeff : ∀ i, PConstructible ((q /ₘ d0).coeff i) :=
      fun i => (divModByMonic_coeff_Pconstructible hd0monic hd0coeff q hcoeff).1 i
    have hrdeg : (q /ₘ d0).natDegree ≤ 7 := by
      rw [Polynomial.natDegree_divByMonic q hd0monic]
      omega
    have hrne : q /ₘ d0 ≠ 0 := by
      intro h0
      have hq0' : q = 0 := by rw [← hq_eq, h0, mul_zero]
      exact hq0 hq0'
    have hrβ : (q /ₘ d0).eval β = 0 := by
      have h := congrArg (fun p : Polynomial ℝ => p.eval β) hq_eq
      rw [Polynomial.eval_mul, hβ] at h
      exact (mul_eq_zero.mp h).resolve_left hd0β
    exact root_Pconstructible_deg7_coeffs hrne hrdeg hrcoeff hrβ

/-- **Theorem 8 (totally real case).** Every real root of a monic totally real separable
octic with P-constructible coefficients is P-constructible.

Two things differ from Theorem 7. The recovery step uses `root_Pconstructible_deg7_coeffs`,
since the recovery polynomial has degree `≤ 7` rather than `≤ 6`; and the non-separable
branch uses `root_Pconstructible_of_nonSeparable_eight`, since the septic
`root_Pconstructible_of_nonSeparable` is hard-wired to `natDegree ≤ 7`. -/
theorem root_Pconstructible_totallyReal_eight {q : ℝ[X]} (hmon : q.Monic)
    (h8 : q.natDegree = 8) (hsplit : q.Splits)
    (hcoef : ∀ k, PConstructible (q.coeff k)) {α : ℝ} (hα : q.eval α = 0) :
    PConstructible α := by
  by_cases hsep : q.Separable
  · have hq0 : q ≠ 0 := by
      intro h
      have h' := h8
      rw [h] at h'
      norm_num at h'
    obtain ⟨αs, hαs, hndαs, hcover⟩ := exists_αs_of_splits hq0 hsep h8 hsplit
    have hengine : ∀ (y : Fin 8 → ℝ), (∀ k, PConstructible ((prodSubY y).coeff k)) →
        psumY y 1 = 0 → psumY y 3 = 0 → psumY y 5 = 0 →
        {β : ℝ} → (prodSubY y).eval β = 0 → PConstructible β := by
      intro y hcoeff h1' h3' h5' β hβ
      exact prodSubY_root_Pconstructible_eight hcoeff h1' h3' h5' hβ
    have hrec : ∀ (p : ℝ[X]), p ≠ 0 → p.natDegree < 8 →
        (∀ k, PConstructible (p.coeff k)) →
        {β : ℝ} → p.eval β = 0 → PConstructible β := by
      intro p hp hd hc β hroot
      exact root_Pconstructible_deg7_coeffs hp (by omega) hc hroot
    exact root_Pconstructible_of_odd_shaped (Or.inr rfl) hmon hsep h8 hcoef hαs hndαs
      hcover hengine hrec hα
  · exact root_Pconstructible_of_nonSeparable_eight hmon hcoef (by omega) hsep hα

end
end Pconstructible
