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
import Pptc.Basic

/-! # Pptc.TotallyReal.Engines

The two "root extraction" engines of `TotallyReal/PLAN.md` §2.2 and §2.3, plus the
drawability of a quartic graph (PLAN §2.3, Lemma Q) that the second engine needs.

## The shape of the argument

After the odd Tschirnhaus reduction of `TotallyReal/Certificate.lean`, the resolvent of a
totally real septic has all its odd-indexed elementary symmetric functions killed, so it
factors as

    χ(t) = t · R(t²) − e₇          (R monic cubic)

and for an octic as

    χ(t) = Q(t²) − e₇ · t          (Q monic quartic).

The value we want is a *real root* of such a `χ`, i.e. a real `β` with

    β · R(β²) = c        (septic)          or        Q(β²) = c · β        (octic).

Putting `x = β² > 0` turns the first into `R(x) = c/β = sgn β · c · x^(−1/2)` and the
second into `Q(x) = sgn β · c · x^(1/2)`: a crossing of a drawable graph (cubic resp.
quartic) with a drawable power law. Isolating the crossing with `restrict` and
`exists_rat_isolating` and reading it off with `inter_x` gives `x`, and then
`β = sgn β · √x`.

## The quartic graph

`poly_graph` only draws polynomials of degree `≤ 6` with *rational* coefficients, and a
cubic Bézier cannot trace a quartic graph, so the quartic graph of Lemma Q is not
available directly. It is reached instead by depressing the quartic and rescaling: with
`z = x + c₃/4` the monic quartic becomes `z⁴ + a z² + b z + c`, and if `a ≠ 0` then with
`λ = √|a|` the substitution `z = λ w` turns `z⁴ + a z²` into `λ⁴ (w⁴ ± w²)`, which is
`poly_graph (X⁴ + X²)` or `poly_graph (X⁴ − X²)` pushed through `scale_x λ` and
`scale_y λ⁴`. The linear term is then a shear `(x, y) ↦ (x, y + b x)`, an instance of
`linearMap_PConstructibleCurve`. When `a = 0` the same construction works with
`poly_graph (X⁴)`. The graph is the *whole* real line, so no interval bookkeeping is
needed and `PConstructibleCurve` comes out with no `u < v` side condition.
-/

namespace Pconstructible

open Polynomial

/-! ### Quartic graphs (PLAN §2.3, Lemma Q) -/

/-- The quartic `c₄ x⁴ + c₃ x³ + c₂ x² + c₁ x + c₀`.

Kept in the same shape as `cubicVal`, with the leading coefficient last, so that
`quarticVal c₀ c₁ c₂ c₃ 1` is the monic quartic of Lemma Q. -/
def quarticVal (c₀ c₁ c₂ c₃ c₄ x : ℝ) : ℝ :=
  c₄ * x ^ 4 + c₃ * x ^ 3 + c₂ * x ^ 2 + c₁ * x + c₀

/-- The graph of `quarticVal c₀ c₁ c₂ c₃ c₄`, over the whole real line.

The domain is unrestricted (unlike `cubicGraph`, which is cut to an interval). That is
legitimate here because Lemma Q's construction ends in `scale_x λ` with `λ = √|a| > 0`
(or in no scaling at all, when `a = 0`), which already surjects onto all of `ℝ`. -/
def quarticGraph (c₀ c₁ c₂ c₃ c₄ : ℝ) : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | p.2 = quarticVal c₀ c₁ c₂ c₃ c₄ p.1}

/-- The depressed-quartic coefficients: with `z = x + c₃/4` the monic quartic
`x⁴ + c₃x³ + c₂x² + c₁x + c₀` becomes `z⁴ + a z² + b z + c` with

    a = c₂ − 3c₃²/8,   b = c₁ − c₂c₃/2 + c₃³/8,
    c = c₀ − c₁c₃/4 + c₂c₃²/16 − 3c₃⁴/256.

Stated as its own definition so the (long) `ring`-check of the expansion appears once
rather than in every use. -/
noncomputable def depressedQuartic (c₀ c₁ c₂ c₃ : ℝ) : ℝ × ℝ × ℝ :=
  (c₂ - 3 * c₃ ^ 2 / 8, c₁ - c₂ * c₃ / 2 + c₃ ^ 3 / 8,
    c₀ - c₁ * c₃ / 4 + c₂ * c₃ ^ 2 / 16 - 3 * c₃ ^ 4 / 256)

/-- The depressed-quartic coefficients are P-constructible. -/
theorem depressedQuartic_Pconstructible {c₀ c₁ c₂ c₃ : ℝ} (h₀ : PConstructible c₀)
    (h₁ : PConstructible c₁) (h₂ : PConstructible c₂) (h₃ : PConstructible c₃) :
    PConstructible (depressedQuartic c₀ c₁ c₂ c₃).1 ∧
      PConstructible (depressedQuartic c₀ c₁ c₂ c₃).2.1 ∧
      PConstructible (depressedQuartic c₀ c₁ c₂ c₃).2.2 := by
  simp only [depressedQuartic]
  exact ⟨by pconstructible, by pconstructible, by pconstructible⟩

/-- The monic quartic `x⁴ + c₃x³ + c₂x² + c₁x + c₀` is `z⁴ + a z² + b z + c` at
`z = x + c₃/4`, with `a`, `b`, `c` its `depressedQuartic`. -/
theorem quarticVal_eq_depressed {c₀ c₁ c₂ c₃ x : ℝ} :
    quarticVal c₀ c₁ c₂ c₃ 1 x
      = (x + c₃ / 4) ^ 4 + (depressedQuartic c₀ c₁ c₂ c₃).1 * (x + c₃ / 4) ^ 2
        + (depressedQuartic c₀ c₁ c₂ c₃).2.1 * (x + c₃ / 4)
        + (depressedQuartic c₀ c₁ c₂ c₃).2.2 := by
  simp only [quarticVal, depressedQuartic]
  ring

/-- **Lemma Q.** The graph of a monic quartic with P-constructible coefficients is a
`PConstructibleCurve`.

Starting points are `poly_graph` of `X⁴`, `X⁴ + X²` and `X⁴ - X²`, all with rational
coefficients and degree `≤ 6`; with `λ = √|a|` and `σ` the sign of `a` the substitution
`z = λ w` carries the first two to `z⁴ + σ λ² z² = z⁴ + a z²`. -/
theorem quarticGraph_PConstructibleCurve {c₀ c₁ c₂ c₃ : ℝ}
    (h₀ : PConstructible c₀) (h₁ : PConstructible c₁) (h₂ : PConstructible c₂)
    (h₃ : PConstructible c₃) :
    PConstructibleCurve (quarticGraph c₀ c₁ c₂ c₃ 1) := by
  obtain ⟨ha, hb, hc⟩ := depressedQuartic_Pconstructible h₀ h₁ h₂ h₃
  have he : PConstructible (c₃ / 4) := PConstructible.div h₃ (by pconstructible)
  -- the starting points `X⁴ + σ X²` all have degree 4
  have hdeg : ∀ sigma : ℚ, (X ^ 4 + C sigma * X ^ 2).natDegree ≤ 6 := by
    intro sigma
    have hm : (C sigma * X ^ 2).natDegree ≤ (C sigma).natDegree + (X ^ 2).natDegree :=
      Polynomial.natDegree_mul_le
    have hs := Polynomial.natDegree_add_le (X ^ 4) (C sigma * X ^ 2)
    simp only [Polynomial.natDegree_X_pow, Polynomial.natDegree_C] at hm hs
    omega
  -- With `z = λ w` the graph of `w ↦ w⁴ + σ w²` rescales to `z ↦ z⁴ + σ λ² z²`.
  have go : ∀ (sigma : ℚ) (lam : ℝ), PConstructible lam → lam ≠ 0 →
      (sigma : ℝ) * lam ^ 2 = (depressedQuartic c₀ c₁ c₂ c₃).1 →
      PConstructibleCurve (quarticGraph c₀ c₁ c₂ c₃ 1) := by
    intro sigma lam hlam hlam0 hkey
    have hlam4 : PConstructible (lam ^ 4) := pow_Pconstructible hlam 4
    have hbase := PConstructibleCurve.poly_graph (X ^ 4 + C sigma * X ^ 2) (hdeg sigma)
    have hshear := linearMap_PConstructibleCurve ((hbase.scale_x hlam).scale_y hlam4)
      PConstructible.base_one zero_Pconstructible hb PConstructible.base_one
    have hcurve := translate_PConstructibleCurve hshear (neg_Pconstructible he) hc
    -- `hcurve` is the base graph pushed through `λ w - c₃/4` and the shear and the shift
    have hfun : (fun p : ℝ × ℝ => (p.1 + -(c₃ / 4), p.2 + (depressedQuartic c₀ c₁ c₂ c₃).2.2))
        ∘ linearMap 1 0 (depressedQuartic c₀ c₁ c₂ c₃).2.1 1 ∘
        (fun p : ℝ × ℝ => (p.1, lam ^ 4 * p.2)) ∘ (fun p : ℝ × ℝ => (lam * p.1, p.2))
        = fun p : ℝ × ℝ => (p.1 * lam - c₃ / 4,
            p.2 * lam ^ 4 + (p.1 * lam) * (depressedQuartic c₀ c₁ c₂ c₃).2.1
              + (depressedQuartic c₀ c₁ c₂ c₃).2.2) := by
      funext p
      simp only [Function.comp_apply, linearMap, Prod.mk.injEq]
      constructor <;> ring
    -- and that push-forward is exactly the graph of the monic quartic
    have hset : (quarticGraph c₀ c₁ c₂ c₃ 1)
        = (fun p : ℝ × ℝ => (p.1 * lam - c₃ / 4,
            p.2 * lam ^ 4 + (p.1 * lam) * (depressedQuartic c₀ c₁ c₂ c₃).2.1
              + (depressedQuartic c₀ c₁ c₂ c₃).2.2)) ''
          {pt : ℝ × ℝ | pt.2 = Polynomial.aeval pt.1 (X ^ 4 + C sigma * X ^ 2)} := by
      ext ⟨a, b⟩
      simp only [quarticGraph, Set.mem_ofPred_eq, Set.mem_image, Prod.exists]
      constructor
      · intro hb
        have hb' : b = (a + c₃ / 4) ^ 4
              + (depressedQuartic c₀ c₁ c₂ c₃).1 * (a + c₃ / 4) ^ 2
              + (depressedQuartic c₀ c₁ c₂ c₃).2.1 * (a + c₃ / 4)
              + (depressedQuartic c₀ c₁ c₂ c₃).2.2 := by
          rw [hb, quarticVal_eq_depressed]
        refine ⟨(a + c₃ / 4) / lam, ((a + c₃ / 4) / lam) ^ 4
            + (sigma : ℝ) * ((a + c₃ / 4) / lam) ^ 2, ?_, ?_⟩
        · simp [Polynomial.aeval_def]
        · rw [Prod.mk.injEq]
          constructor
          · field_simp
            ring
          · calc
              _ = (a + c₃ / 4) ^ 4 + ((sigma : ℝ) * lam ^ 2) * (a + c₃ / 4) ^ 2
                  + (depressedQuartic c₀ c₁ c₂ c₃).2.1 * (a + c₃ / 4)
                  + (depressedQuartic c₀ c₁ c₂ c₃).2.2 := by
                field_simp
            _ = (a + c₃ / 4) ^ 4
                  + (depressedQuartic c₀ c₁ c₂ c₃).1 * (a + c₃ / 4) ^ 2
                  + (depressedQuartic c₀ c₁ c₂ c₃).2.1 * (a + c₃ / 4)
                  + (depressedQuartic c₀ c₁ c₂ c₃).2.2 := by rw [hkey]
            _ = b := hb'.symm
      · rintro ⟨x, y, hp, hM⟩
        rw [Prod.mk.injEq] at hM
        obtain ⟨hM1, hM2⟩ := hM
        have hp' : y = x ^ 4 + (sigma : ℝ) * x ^ 2 := by
          simpa [Polynomial.aeval_def] using hp
        have hz : x * lam = a + c₃ / 4 := by linarith
        calc
          b = y * lam ^ 4 + (x * lam) * (depressedQuartic c₀ c₁ c₂ c₃).2.1
              + (depressedQuartic c₀ c₁ c₂ c₃).2.2 := hM2.symm
          _ = (x ^ 4 + (sigma : ℝ) * x ^ 2) * lam ^ 4
              + (x * lam) * (depressedQuartic c₀ c₁ c₂ c₃).2.1
              + (depressedQuartic c₀ c₁ c₂ c₃).2.2 := by rw [hp']
          _ = (x * lam) ^ 4 + ((sigma : ℝ) * lam ^ 2) * (x * lam) ^ 2
              + (x * lam) * (depressedQuartic c₀ c₁ c₂ c₃).2.1
              + (depressedQuartic c₀ c₁ c₂ c₃).2.2 := by ring
          _ = (a + c₃ / 4) ^ 4 + ((sigma : ℝ) * lam ^ 2) * (a + c₃ / 4) ^ 2
              + (depressedQuartic c₀ c₁ c₂ c₃).2.1 * (a + c₃ / 4)
              + (depressedQuartic c₀ c₁ c₂ c₃).2.2 := by rw [hz]; ring
          _ = (a + c₃ / 4) ^ 4
              + (depressedQuartic c₀ c₁ c₂ c₃).1 * (a + c₃ / 4) ^ 2
              + (depressedQuartic c₀ c₁ c₂ c₃).2.1 * (a + c₃ / 4)
              + (depressedQuartic c₀ c₁ c₂ c₃).2.2 := by rw [hkey]
          _ = quarticVal c₀ c₁ c₂ c₃ 1 a := (quarticVal_eq_depressed (x := a)).symm
    have hcurve' : PConstructibleCurve ((fun p : ℝ × ℝ => (p.1 * lam - c₃ / 4,
        p.2 * lam ^ 4 + (p.1 * lam) * (depressedQuartic c₀ c₁ c₂ c₃).2.1
          + (depressedQuartic c₀ c₁ c₂ c₃).2.2)) ''
        {pt : ℝ × ℝ | pt.2 = Polynomial.aeval pt.1 (X ^ 4 + C sigma * X ^ 2)}) := by
      convert hcurve using 1
      rw [← Set.image_comp, ← Set.image_comp, ← Set.image_comp,
        Function.comp_assoc, Function.comp_assoc, hfun]
    exact hset ▸ hcurve'
  -- the three cases, according to the sign of the quadratic coefficient `a`
  rcases lt_trichotomy (depressedQuartic c₀ c₁ c₂ c₃).1 0 with hlt | hz | hgt
  · refine go (-1) (Real.sqrt (-(depressedQuartic c₀ c₁ c₂ c₃).1))
      (sqrt_Pconstructible (neg_Pconstructible ha)) ?_ ?_
    · exact ne_of_gt (Real.sqrt_pos.mpr (by linarith))
    · rw [Real.sq_sqrt (by linarith)]
      ring
  · refine go 0 1 PConstructible.base_one (by norm_num) ?_
    rw [hz]
    norm_num
  · refine go 1 (Real.sqrt (depressedQuartic c₀ c₁ c₂ c₃).1) (sqrt_Pconstructible ha) ?_ ?_
    · exact ne_of_gt (Real.sqrt_pos.mpr hgt)
    · rw [Real.sq_sqrt (le_of_lt hgt)]
      ring

/-! ### Real roots of a quartic with P-constructible coefficients -/

/-- A real root of a quartic with P-constructible coefficients is P-constructible.

Not needed in its own right (`root_Pconstructible_le_six_coeffs` already covers degree
`≤ 6`) but it keeps the degenerate branches of the two engines one line each. -/
theorem quarticVal_root_Pconstructible {c₀ c₁ c₂ c₃ c₄ β : ℝ}
    (h₀ : PConstructible c₀) (h₁ : PConstructible c₁) (h₂ : PConstructible c₂)
    (h₃ : PConstructible c₃) (h₄ : PConstructible c₄)
    (hne : c₄ ≠ 0 ∨ c₃ ≠ 0 ∨ c₂ ≠ 0 ∨ c₁ ≠ 0 ∨ c₀ ≠ 0)
    (hroot : quarticVal c₀ c₁ c₂ c₃ c₄ β = 0) :
    PConstructible β := by
  set P : Polynomial ℝ :=
    C c₄ * X ^ 4 + C c₃ * X ^ 3 + C c₂ * X ^ 2 + C c₁ * X + C c₀ with hPdef
  have hevalP : ∀ t : ℝ, P.eval t = quarticVal c₀ c₁ c₂ c₃ c₄ t := by
    intro t
    simp [hPdef, quarticVal]
  have e4 : P.coeff 4 = c₄ := by simp [hPdef]
  have e3 : P.coeff 3 = c₃ := by simp [hPdef]
  have e2 : P.coeff 2 = c₂ := by simp [hPdef]
  have e1 : P.coeff 1 = c₁ := by simp [hPdef]
  have e0 : P.coeff 0 = c₀ := by simp [hPdef]
  have hPne : P ≠ 0 := by
    intro hc
    rw [hc] at e4 e3 e2 e1 e0
    simp only [Polynomial.coeff_zero] at e4 e3 e2 e1 e0
    rcases hne with h | h | h | h | h
    exacts [h e4.symm, h e3.symm, h e2.symm, h e1.symm, h e0.symm]
  have hdeg : P.natDegree ≤ 4 := by
    have h4 : (C c₄ * X ^ 4).natDegree ≤ 4 := Polynomial.natDegree_C_mul_X_pow_le c₄ 4
    have h3 : (C c₃ * X ^ 3).natDegree ≤ 3 := Polynomial.natDegree_C_mul_X_pow_le c₃ 3
    have h2 : (C c₂ * X ^ 2).natDegree ≤ 2 := Polynomial.natDegree_C_mul_X_pow_le c₂ 2
    have h1 : (C c₁ * X).natDegree ≤ 1 := by
      simpa only [pow_one] using Polynomial.natDegree_C_mul_X_pow_le c₁ 1
    have h0 : (C c₀).natDegree ≤ 0 := by simp
    have hsAB : (C c₄ * X ^ 4 + C c₃ * X ^ 3).natDegree ≤ 4 := by
      exact le_trans (Polynomial.natDegree_add_le _ _) (max_le (by omega) (by omega))
    have hsABC : (C c₄ * X ^ 4 + C c₃ * X ^ 3 + C c₂ * X ^ 2).natDegree ≤ 4 := by
      exact le_trans (Polynomial.natDegree_add_le _ _) (max_le (by omega) (by omega))
    have hsABCD : (C c₄ * X ^ 4 + C c₃ * X ^ 3 + C c₂ * X ^ 2 + C c₁ * X).natDegree ≤ 4 := by
      exact le_trans (Polynomial.natDegree_add_le _ _) (max_le (by omega) (by omega))
    rw [hPdef]
    exact le_trans (Polynomial.natDegree_add_le _ _) (max_le (by omega) (by omega))
  have hcoeff : ∀ i, PConstructible (P.coeff i) := by
    intro i
    rcases i.lt_trichotomy 5 with h | h | h
    · interval_cases i
      · rw [e0]; exact h₀
      · rw [e1]; exact h₁
      · rw [e2]; exact h₂
      · rw [e3]; exact h₃
      · rw [e4]; exact h₄
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      exact zero_Pconstructible
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      exact zero_Pconstructible
  refine root_Pconstructible_le_six_coeffs hPne (by omega) hcoeff ?_
  rw [hevalP, hroot]

/-! ### The septic engine (PLAN §2.2, Lemma E7) -/

/-- **Lemma E7.** If `R(x) = x³ + r₂x² + r₁x + r₀` is a monic cubic with
P-constructible coefficients, `c` is P-constructible, and a real `β` satisfies
`β · R(β²) = c`, then `β` is P-constructible.

The crossing that produces `x = β²` is between the cubic graph of `R` (restricted to a
rational isolating interval) and `scale_y (sgn β · c) (power_law 1 (-1/2))`. -/
theorem negHalf_cubic_root_Pconstructible {r₀ r₁ r₂ c β : ℝ}
    (h₀ : PConstructible r₀) (h₁ : PConstructible r₁) (h₂ : PConstructible r₂)
    (hc : PConstructible c) (heq : β * cubicVal r₀ r₁ r₂ 1 (β ^ 2) = c) :
    PConstructible β := by
  by_cases hβ : β = 0
  · rw [hβ]
    exact zero_Pconstructible
  by_cases hc0 : c = 0
  · -- `β²` is a root of a monic cubic, and `β = ±√(β²)`
    have hR : cubicVal r₀ r₁ r₂ 1 (β ^ 2) = 0 :=
      (mul_eq_zero.mp (by rw [heq, hc0])).resolve_left hβ
    have hroot : PConstructible (β ^ 2) :=
      cubicVal_root_Pconstructible h₀ h₁ h₂ PConstructible.base_one
        (Or.inl one_ne_zero) hR
    have hsqrt : PConstructible (Real.sqrt (β ^ 2)) := sqrt_Pconstructible hroot
    rcases le_total 0 β with hpos | hneg
    · rwa [Real.sqrt_sq hpos] at hsqrt
    · rw [Real.sqrt_sq_eq_abs, abs_of_nonpos hneg] at hsqrt
      simpa using neg_Pconstructible hsqrt
  have hrpow2 : ∀ x : ℝ, 0 < x → (x ^ ((-1 / 2 : ℚ) : ℝ)) ^ (2 : ℕ) = x⁻¹ := by
    intro x hx
    calc (x ^ ((-1 / 2 : ℚ) : ℝ)) ^ (2 : ℕ)
        = (x ^ ((-1 / 2 : ℚ) : ℝ)) ^ ((2 : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
      _ = x ^ (((-1 / 2 : ℚ) : ℝ) * 2) := (Real.rpow_mul hx.le _ _).symm
      _ = x ^ (-1 : ℝ) := by norm_num
      _ = x⁻¹ := Real.rpow_neg_one x
  -- the crossing of the cubic graph with `x ↦ s·x ^ (-1/2)`, isolated on the roots of
  -- `X·R(X)² - c²`
  have go : ∀ s : ℝ, PConstructible s → s ^ 2 = c ^ 2 →
      cubicVal r₀ r₁ r₂ 1 (β ^ 2) = s * (β ^ 2) ^ ((-1 / 2 : ℚ) : ℝ) →
      PConstructible (β ^ 2) := by
    intro s hs hsq hmemb
    set Q : Polynomial ℝ := X ^ 3 + C r₂ * X ^ 2 + C r₁ * X + C r₀ with hQdef
    set PP : Polynomial ℝ := X * Q ^ 2 - C (c ^ 2) with hPPdef
    have hevalPP : ∀ t : ℝ, PP.eval t = t * cubicVal r₀ r₁ r₂ 1 t ^ 2 - c ^ 2 := by
      intro t
      simp [hPPdef, hQdef, cubicVal]
    have hPPne : PP ≠ 0 := by
      intro hc
      have h0 := congrArg (fun q : Polynomial ℝ => q.eval 0) hc
      rw [Polynomial.eval_zero, hevalPP, zero_mul, sub_eq_zero] at h0
      have h0' : c ^ 2 = 0 := h0.symm
      exact hc0 (mul_self_eq_zero.mp (by rw [← pow_two]; exact h0'))
    have hroot : PP.IsRoot (β ^ 2) := by
      rw [Polynomial.IsRoot, hevalPP]
      have hsq' : (β ^ 2) * cubicVal r₀ r₁ r₂ 1 (β ^ 2) ^ 2 = c ^ 2 := by
        calc (β ^ 2) * cubicVal r₀ r₁ r₂ 1 (β ^ 2) ^ 2
            = (β * cubicVal r₀ r₁ r₂ 1 (β ^ 2)) ^ 2 := by ring
          _ = c ^ 2 := by rw [heq]
      linarith
    have hAfin : {t : ℝ | PP.IsRoot t ∧ t ≠ β ^ 2}.Finite :=
      (Polynomial.finite_setOfPred_isRoot hPPne).subset (fun t ht => ht.1)
    obtain ⟨q₁, q₂, hq₁b, hq₂a, huniq⟩ := exists_rat_isolating hAfin
    have hT := cubicGraph_PConstructibleCurve h₀ h₁ h₂ PConstructible.base_one
      (rat_Pconstructible q₁) (rat_Pconstructible q₂) (by linarith : (q₁ : ℝ) < q₂)
    have hS := (PConstructibleCurve.power_law 1 (-1 / 2)).scale_y hs
    refine PConstructible.inter_x hS hT
      (x := β ^ 2) (y := cubicVal r₀ r₁ r₂ 1 (β ^ 2)) ?_
    ext ⟨a, b⟩
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_image, Prod.exists,
      Set.mem_singleton_iff, Prod.mk.injEq, cubicGraph]
    constructor
    · rintro ⟨⟨x, y, ⟨hap, hb⟩, hM1, hM2⟩, hlo, hhi, hgraph⟩
      have hrp : (x ^ ((-1 / 2 : ℚ) : ℝ)) ^ (2 : ℕ) = x⁻¹ := hrpow2 x hap
      have hb' : y = x ^ ((-1 / 2 : ℚ) : ℝ) := by simpa using hb
      have hkey : a * cubicVal r₀ r₁ r₂ 1 a ^ 2 = c ^ 2 := by
        calc a * cubicVal r₀ r₁ r₂ 1 a ^ 2 = x * (s * y) ^ 2 := by
              rw [← hgraph, hM2.symm, hM1.symm]
          _ = x * (s ^ 2 * (x ^ ((-1 / 2 : ℚ) : ℝ)) ^ (2 : ℕ)) := by rw [hb']; ring
          _ = x * (s ^ 2 * x⁻¹) := by rw [hrp]
          _ = c ^ 2 := by rw [hsq]; field_simp
      have hra : PP.IsRoot a := by rw [Polynomial.IsRoot, hevalPP, hkey]; ring
      have ha : a = β ^ 2 := huniq a hra hlo hhi
      exact ⟨ha, by rw [hgraph, ha]⟩
    · rintro ⟨rfl, rfl⟩
      constructor
      · refine ⟨(β ^ 2), (β ^ 2) ^ ((-1 / 2 : ℚ) : ℝ), ⟨?_, ?_⟩, rfl, hmemb.symm⟩
        · exact sq_pos_of_ne_zero hβ
        · simp
      · exact ⟨hq₁b.le, hq₂a.le, rfl⟩
  -- the two signs of `β`, and then `β = ±√(β²)`
  rcases lt_or_gt_of_ne hβ with hβneg | hβpos
  · have hx : PConstructible (β ^ 2) := by
      refine go (-c) (neg_Pconstructible hc) (by ring) ?_
      have hinv : (β ^ 2) ^ ((-1 / 2 : ℚ) : ℝ) = |β|⁻¹ := by
        have e : ((-1 / 2 : ℚ) : ℝ) = -(1 / 2 : ℝ) := by norm_num
        rw [e, Real.rpow_neg (sq_nonneg β), ← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs]
      calc cubicVal r₀ r₁ r₂ 1 (β ^ 2) = c / β := by rw [← heq]; field_simp
        _ = -c * (β ^ 2) ^ ((-1 / 2 : ℚ) : ℝ) := by
          rw [hinv, abs_of_neg hβneg, inv_neg, div_eq_mul_inv]
          ring
    have hx : PConstructible (Real.sqrt (β ^ 2)) := sqrt_Pconstructible hx
    rw [Real.sqrt_sq_eq_abs, abs_of_neg hβneg] at hx
    simpa using neg_Pconstructible hx
  · have hx : PConstructible (β ^ 2) := by
      refine go c hc (by ring) ?_
      have hinv : (β ^ 2) ^ ((-1 / 2 : ℚ) : ℝ) = β⁻¹ := by
        have e : ((-1 / 2 : ℚ) : ℝ) = -(1 / 2 : ℝ) := by norm_num
        rw [e, Real.rpow_neg (sq_nonneg β), ← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs,
          abs_of_pos hβpos]
      calc cubicVal r₀ r₁ r₂ 1 (β ^ 2) = c / β := by rw [← heq]; field_simp
        _ = c * (β ^ 2) ^ ((-1 / 2 : ℚ) : ℝ) := by rw [hinv, div_eq_mul_inv]
    have hx : PConstructible (Real.sqrt (β ^ 2)) := sqrt_Pconstructible hx
    rwa [Real.sqrt_sq_eq_abs, abs_of_pos hβpos] at hx

/-! ### The octic engine (PLAN §2.3, Lemma E8) -/

/-- **Lemma E8.** If `Q(x) = x⁴ + q₃x³ + q₂x² + q₁x + q₀` is a monic quartic with
P-constructible coefficients, `c` is P-constructible, and a real `β` satisfies
`Q(β²) = c · β`, then `β` is P-constructible.

The crossing is between the graph of `Q` and `scale_y (sgn β · c) (power_law 1 (1/2))`,
which is Lemma Q's `quarticGraph_PConstructibleCurve` on one side. -/
theorem half_quartic_root_Pconstructible {q₀ q₁ q₂ q₃ c β : ℝ}
    (h₀ : PConstructible q₀) (h₁ : PConstructible q₁) (h₂ : PConstructible q₂)
    (h₃ : PConstructible q₃) (hc : PConstructible c)
    (heq : quarticVal q₀ q₁ q₂ q₃ 1 (β ^ 2) = c * β) :
    PConstructible β := by
  by_cases hβ : β = 0
  · rw [hβ]
    exact zero_Pconstructible
  by_cases hc0 : c = 0
  · -- `β²` is a root of a monic quartic, and `β = ±√(β²)`
    have hroot : PConstructible (β ^ 2) :=
      quarticVal_root_Pconstructible h₀ h₁ h₂ h₃ PConstructible.base_one
        (Or.inl one_ne_zero) (by rw [heq, hc0]; ring)
    have hsqrt : PConstructible (Real.sqrt (β ^ 2)) := sqrt_Pconstructible hroot
    rcases lt_or_gt_of_ne hβ with hβneg | hβpos
    · rw [Real.sqrt_sq_eq_abs, abs_of_neg hβneg] at hsqrt
      simpa using neg_Pconstructible hsqrt
    · rw [Real.sqrt_sq_eq_abs, abs_of_pos hβpos] at hsqrt
      exact hsqrt
  have hrpow2 : ∀ x : ℝ, 0 < x → (x ^ ((1 / 2 : ℚ) : ℝ)) ^ (2 : ℕ) = x := by
    intro x hx
    calc (x ^ ((1 / 2 : ℚ) : ℝ)) ^ (2 : ℕ)
        = (x ^ ((1 / 2 : ℚ) : ℝ)) ^ ((2 : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
      _ = x ^ (((1 / 2 : ℚ) : ℝ) * 2) := (Real.rpow_mul hx.le _ _).symm
      _ = x ^ (1 : ℝ) := by norm_num
      _ = x := Real.rpow_one x
  -- the crossing of the quartic graph with `x ↦ s·x ^ (1/2)`, isolated on the roots of
  -- `Q(X)² - c²·X` (squaring `Q(x) = s·√x` is all that is needed, since `s² = c²`)
  have go : ∀ s : ℝ, PConstructible s → s ^ 2 = c ^ 2 →
      quarticVal q₀ q₁ q₂ q₃ 1 (β ^ 2) = s * (β ^ 2) ^ ((1 / 2 : ℚ) : ℝ) →
      PConstructible (β ^ 2) := by
    intro s hs hsq hmemb
    set W : Polynomial ℝ :=
      X ^ 4 + (C q₃ * X ^ 3 + C q₂ * X ^ 2 + C q₁ * X + C q₀) with hWdef
    set N : Polynomial ℝ := W ^ 2 - C (c ^ 2) * X with hNdef
    have hevalW : ∀ t : ℝ, W.eval t = quarticVal q₀ q₁ q₂ q₃ 1 t := by
      intro t
      simp [hWdef, quarticVal]; ring
    have hz : W.coeff 4 = 1 := by
      simp [hWdef, Polynomial.coeff_X_pow]
    have hW4 : W.natDegree = 4 := by
      have h0 : (C q₀).natDegree ≤ 0 := by simp
      have h1 : (C q₁ * X).natDegree ≤ 1 := by
        simpa only [pow_one] using Polynomial.natDegree_C_mul_X_pow_le q₁ 1
      have h2 : (C q₂ * X ^ 2).natDegree ≤ 2 := Polynomial.natDegree_C_mul_X_pow_le q₂ 2
      have h3 : (C q₃ * X ^ 3).natDegree ≤ 3 := Polynomial.natDegree_C_mul_X_pow_le q₃ 3
      have h0' : (C q₀).natDegree ≤ 3 := h0.trans (Nat.zero_le 3)
      have h1' : (C q₁ * X).natDegree ≤ 3 := by omega
      have h2' : (C q₂ * X ^ 2).natDegree ≤ 3 := by omega
      have hAB : (C q₃ * X ^ 3 + C q₂ * X ^ 2).natDegree ≤ 3 :=
        Polynomial.natDegree_add_le_of_degree_le h3 h2'
      have hABC : (C q₃ * X ^ 3 + C q₂ * X ^ 2 + C q₁ * X).natDegree ≤ 3 :=
        Polynomial.natDegree_add_le_of_degree_le hAB h1'
      have hD : (C q₃ * X ^ 3 + C q₂ * X ^ 2 + C q₁ * X + C q₀).natDegree ≤ 3 :=
        Polynomial.natDegree_add_le_of_degree_le hABC h0'
      have hD4 : (C q₃ * X ^ 3 + C q₂ * X ^ 2 + C q₁ * X + C q₀).natDegree ≤ 4 := by
        omega
      have hle : W.natDegree ≤ 4 := by
        rw [hWdef]
        exact Polynomial.natDegree_add_le_of_degree_le (by simp) hD4
      exact Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hle (by rw [hz]; norm_num)
    have hlcW : W.leadingCoeff = 1 := by
      change W.coeff W.natDegree = 1
      rw [hW4, hz]
    have hc8 : (W ^ 2).coeff 8 = 1 := by
      have h2 : 2 * W.natDegree = 8 := by rw [hW4]
      rw [← h2, Polynomial.coeff_pow_mul_natDegree, hlcW]
      norm_num
    have hNne : N ≠ 0 := by
      intro hN
      have hsub : W ^ 2 - C (c ^ 2) * X = 0 := hNdef ▸ hN
      have hW2 : W ^ 2 = C (c ^ 2) * X := sub_eq_zero.mp hsub
      have h8 := congrArg (fun q : Polynomial ℝ => q.coeff 8) hW2
      rw [hc8, Polynomial.coeff_C_mul, Polynomial.coeff_X, if_neg (by omega)] at h8
      norm_num at h8
    have hevalN : ∀ t : ℝ,
        N.eval t = quarticVal q₀ q₁ q₂ q₃ 1 t ^ 2 - c ^ 2 * t := by
      intro t
      rw [hNdef]
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_C, Polynomial.eval_X, hevalW]
    have hroot : N.IsRoot (β ^ 2) := by
      rw [Polynomial.IsRoot, hevalN]
      have hsq' : quarticVal q₀ q₁ q₂ q₃ 1 (β ^ 2) ^ 2 = c ^ 2 * (β ^ 2) := by
        rw [heq]
        ring
      linarith
    have hAfin : {t : ℝ | N.IsRoot t ∧ t ≠ β ^ 2}.Finite :=
      (Polynomial.finite_setOfPred_isRoot hNne).subset (fun t ht => ht.1)
    obtain ⟨u, v, hub, hvb, huniq⟩ := exists_rat_isolating hAfin
    obtain ⟨n, hn⟩ := exists_nat_gt |quarticVal q₀ q₁ q₂ q₃ 1 (β ^ 2)|
    obtain ⟨hylo, hyhi⟩ := abs_lt.mp hn
    have hnP : PConstructible ((n : ℝ)) := nat_Pconstructible n
    have hT' := (quarticGraph_PConstructibleCurve h₀ h₁ h₂ h₃).restrict
      (u : ℝ) (v : ℝ) (-(n : ℝ)) (n : ℝ) (rat_Pconstructible u)
      (rat_Pconstructible v) (neg_Pconstructible hnP) hnP
    have hS := (PConstructibleCurve.power_law 1 (1 / 2)).scale_y hs
    refine PConstructible.inter_x hS hT'
      (x := β ^ 2) (y := quarticVal q₀ q₁ q₂ q₃ 1 (β ^ 2)) ?_
    ext ⟨a, b⟩
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_image, Prod.exists,
      Set.mem_singleton_iff, Prod.mk.injEq, quarticGraph]
    constructor
    · rintro ⟨⟨x, y, ⟨hap, hb⟩, hM1, hM2⟩, hgraph, hlo, hhi, hyl, hyh⟩
      have hrp : (x ^ ((1 / 2 : ℚ) : ℝ)) ^ (2 : ℕ) = x := hrpow2 x hap
      have hb' : y = x ^ ((1 / 2 : ℚ) : ℝ) := by simpa using hb
      have hkey : quarticVal q₀ q₁ q₂ q₃ 1 a ^ 2 = c ^ 2 * a := by
        calc quarticVal q₀ q₁ q₂ q₃ 1 a ^ 2 = (s * y) ^ 2 := by rw [← hgraph, ← hM2]
          _ = s ^ 2 * (x ^ ((1 / 2 : ℚ) : ℝ)) ^ (2 : ℕ) := by rw [hb']; ring
          _ = s ^ 2 * x := by rw [hrp]
          _ = c ^ 2 * a := by rw [hM1, hsq]
      have hra : N.IsRoot a := by rw [Polynomial.IsRoot, hevalN, hkey]; ring
      have ha : a = β ^ 2 := huniq a hra hlo hhi
      exact ⟨ha, by rw [hgraph, ha]⟩
    · rintro ⟨rfl, rfl⟩
      constructor
      · refine ⟨(β ^ 2), (β ^ 2) ^ ((1 / 2 : ℚ) : ℝ), ⟨?_, ?_⟩, rfl, hmemb.symm⟩
        · exact sq_pos_of_ne_zero hβ
        · simp
      · exact ⟨rfl, hub.le, hvb.le, hylo.le, hyhi.le⟩
  -- the two signs of `β`, and then `β = ±√(β²)`
  rcases lt_or_gt_of_ne hβ with hβneg | hβpos
  · have hx : PConstructible (β ^ 2) := by
      refine go (-c) (neg_Pconstructible hc) (by ring) ?_
      have hinv : (β ^ 2) ^ ((1 / 2 : ℚ) : ℝ) = -β := by
        have e : ((1 / 2 : ℚ) : ℝ) = (1 / 2 : ℝ) := by norm_num
        rw [e, ← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs, abs_of_neg hβneg]
      calc quarticVal q₀ q₁ q₂ q₃ 1 (β ^ 2) = c * β := heq
        _ = -c * (β ^ 2) ^ ((1 / 2 : ℚ) : ℝ) := by rw [hinv]; ring
    have hx : PConstructible (Real.sqrt (β ^ 2)) := sqrt_Pconstructible hx
    rw [Real.sqrt_sq_eq_abs, abs_of_neg hβneg] at hx
    simpa using neg_Pconstructible hx
  · have hx : PConstructible (β ^ 2) := by
      refine go c hc (by ring) ?_
      have hinv : (β ^ 2) ^ ((1 / 2 : ℚ) : ℝ) = β := by
        have e : ((1 / 2 : ℚ) : ℝ) = (1 / 2 : ℝ) := by norm_num
        rw [e, ← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs, abs_of_pos hβpos]
      calc quarticVal q₀ q₁ q₂ q₃ 1 (β ^ 2) = c * β := heq
        _ = c * (β ^ 2) ^ ((1 / 2 : ℚ) : ℝ) := by rw [hinv]
    have hx : PConstructible (Real.sqrt (β ^ 2)) := sqrt_Pconstructible hx
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hβpos] at hx
    exact hx

end Pconstructible
