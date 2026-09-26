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
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.IntermediateValue

/-! # Pptc.TotallyReal.SignChange

Generic real-analysis lemmas recording that a function with a *simple* zero changes sign
at every sufficiently small radius around that zero.

The certificates produced by `Pptc.TotallyReal.Certificate` exhibit a real root `x₀` of a
polynomial as an exact factorization `f t = (t - x₀) * G t` with `G` continuous and
`G x₀ ≠ 0`.  Because the linear factor flips sign across `x₀` while `G` does not, the
product `f (x₀ - δ) * f (x₀ + δ)` is strictly negative for every small `δ > 0`.  This is
what lets the certificate detect a genuine sign change (and hence a genuine root) of the
polynomial, independently of any numerical root finder.

The three statements are:

* `signChange_at_radius_of_factorization` — the elementary algebraic core, at a
  caller-chosen radius on which `G` is known to keep its sign;
* `signChange_of_factorization` — the existence form, obtained by extracting a sign
  neighbourhood of `x₀` from continuity of `G`;
* `signChange_of_simpleRoot` — the same conclusion from the analytic hypothesis that `f`
  has a nonzero derivative at `x₀`, proved through the slope limit of `HasDerivAt`.
-/

open Filter

open scoped Topology

namespace Pconstructible

/-! ### Sign change at a prescribed radius -/

/-- If `f t = (t - x₀) * G t` and `G` keeps the sign of `G x₀` on `[x₀ - δ, x₀ + δ]`,
then `f` has a sign change at `x₀ ± δ`.  This is the elementary algebraic core: the
linear factor contributes `-δ` and `+δ` respectively, so the two values have opposite
signs. -/
-- Theorem: sign change of `f` at `x₀ ± δ` from an exact factorization `f = (· - x₀) * G`
-- when `G` is sign-definite on `[x₀ - δ, x₀ + δ]`.
theorem signChange_at_radius_of_factorization {f G : ℝ → ℝ} {x₀ δ : ℝ}
    (hδ : 0 < δ) (hG : ContinuousAt G x₀) (hG0 : G x₀ ≠ 0)
    (hsign : ∀ t ∈ Set.Icc (x₀ - δ) (x₀ + δ), 0 < G t * G x₀)
    (hfac : ∀ t, f t = (t - x₀) * G t) :
    f (x₀ - δ) * f (x₀ + δ) < 0 := by
  -- `hG` and `hG0` are part of the interface (they are what makes `hsign` meaningful).
  have _hG := hG
  have _hG0 := hG0
  have h1 : 0 < G (x₀ - δ) * G x₀ :=
    hsign (x₀ - δ) ⟨le_refl _, by linarith⟩
  have h2 : 0 < G (x₀ + δ) * G x₀ :=
    hsign (x₀ + δ) ⟨by linarith, le_refl _⟩
  -- Multiplying the two sign hypotheses turns them into a sign for the product
  -- `G (x₀ - δ) * G (x₀ + δ)`, since the common factor `G x₀` appears squared.
  have hm : 0 < (G (x₀ - δ) * G x₀) * (G (x₀ + δ) * G x₀) := mul_pos h1 h2
  have hprod : 0 < G (x₀ - δ) * G (x₀ + δ) := by
    have e : (G (x₀ - δ) * G x₀) * (G (x₀ + δ) * G x₀)
        = (G (x₀ - δ) * G (x₀ + δ)) * (G x₀) ^ 2 := by ring
    rw [e] at hm
    exact pos_of_mul_pos_left hm (sq_nonneg (G x₀))
  rw [hfac (x₀ - δ), hfac (x₀ + δ)]
  have e1 : x₀ - δ - x₀ = -δ := by ring
  have e2 : x₀ + δ - x₀ = δ := by ring
  rw [e1, e2]
  have e3 : (-δ * G (x₀ - δ)) * (δ * G (x₀ + δ))
      = -((δ * δ) * (G (x₀ - δ) * G (x₀ + δ))) := by ring
  rw [e3]
  have hpos : 0 < (δ * δ) * (G (x₀ - δ) * G (x₀ + δ)) :=
    mul_pos (mul_pos hδ hδ) hprod
  linarith

/-! ### Existence form via continuity -/

/-- If `f t = (t - x₀) * G t` with `G` continuous at `x₀` and `G x₀ ≠ 0`, then for every
`ε > 0` there is `0 < δ < ε` with `f (x₀ - δ) * f (x₀ + δ) < 0`.  Continuity of `G`
provides a symmetric interval around `x₀` on which `G` keeps the sign of `G x₀`. -/
-- Theorem: sign change at every small radius from an exact factorization with continuous
-- nonvanishing cofactor.
theorem signChange_of_factorization {f G : ℝ → ℝ} {x₀ : ℝ}
    (hG : ContinuousAt G x₀) (hG0 : G x₀ ≠ 0)
    (hfac : ∀ t, f t = (t - x₀) * G t) :
    ∀ ε > 0, ∃ δ, 0 < δ ∧ δ < ε ∧ f (x₀ - δ) * f (x₀ + δ) < 0 := by
  intro ε hε
  -- `G` keeps the sign of `G x₀` on a neighbourhood of `x₀`.
  have hpos : ∀ᶠ t in 𝓝 x₀, 0 < G t * G x₀ := by
    have hcont : ContinuousAt (fun t => G t * G x₀) x₀ := hG.mul continuousAt_const
    exact hcont.eventually (isOpen_Ioi.mem_nhds (mul_self_pos.mpr hG0))
  rw [Metric.eventually_nhds_iff] at hpos
  obtain ⟨r, hr, hball⟩ := hpos
  set δ : ℝ := min (r / 2) (ε / 2) with hδdef
  have hδ : 0 < δ := by
    rw [hδdef]; exact lt_min (by linarith) (by linarith)
  have hδr : δ < r := by
    rw [hδdef]; exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδε : δ < ε := by
    rw [hδdef]; exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  refine ⟨δ, hδ, hδε, ?_⟩
  refine signChange_at_radius_of_factorization hδ hG hG0 ?_ hfac
  intro t ht
  apply hball
  rw [Real.dist_eq]
  have habs : |t - x₀| ≤ δ := by
    rw [abs_le]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  linarith

/-! ### Derivative form -/

/-- A function with a *simple* zero (nonzero derivative `d` at `x₀`) changes sign at
every sufficiently small radius `δ` around `x₀`.  Proof: the difference quotient
`h ↦ (f (x₀ + h) - f x₀) / h` tends to `d` as `h → 0`, so for small `h ≠ 0` the product
`d * (f (x₀ + h) - f x₀) / h` is positive.  At `h = δ > 0` this makes `f (x₀ + δ)` have
the sign of `d`; at `h = -δ < 0` the same positivity shows `d * f (x₀ - δ) < 0`.  Hence the
two values have opposite signs. -/
-- Theorem: sign change at every small radius from a simple root, derivative form.
theorem signChange_of_simpleRoot {f : ℝ → ℝ} {x₀ d : ℝ}
    (hf : HasDerivAt f d x₀) (h0 : f x₀ = 0) (hd : d ≠ 0) :
    ∀ ε > 0, ∃ δ, 0 < δ ∧ δ < ε ∧ f (x₀ - δ) * f (x₀ + δ) < 0 := by
  intro ε hε
  have hslope : Tendsto (fun t : ℝ => t⁻¹ * (f (x₀ + t) - f x₀))
      (𝓝[≠] (0 : ℝ)) (𝓝 d) := by
    simpa using hf.tendsto_slope_zero
  have hd2 : 0 < d * d := mul_self_pos.mpr hd
  -- For small nonzero `h`, the quantity `d * ((f (x₀ + h) - f x₀) / h)` is positive,
  -- because it tends to `d * d > 0`.
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ), 0 < d * (t⁻¹ * (f (x₀ + t) - f x₀)) := by
    have hc : Tendsto (fun t : ℝ => d * (t⁻¹ * (f (x₀ + t) - f x₀)))
        (𝓝[≠] (0 : ℝ)) (𝓝 (d * d)) := by
      simpa using hslope.const_mul d
    exact hc.eventually (isOpen_Ioi.mem_nhds hd2)
  rw [eventually_nhdsWithin_iff] at hev
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨r, hr, hball⟩ := hev
  set δ : ℝ := min (r / 2) (ε / 2) with hδdef
  have hδ : 0 < δ := by
    rw [hδdef]; exact lt_min (by linarith) (by linarith)
  have hδr : δ < r := by
    rw [hδdef]; exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδε : δ < ε := by
    rw [hδdef]; exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  refine ⟨δ, hδ, hδε, ?_⟩
  have hdistp : dist δ (0 : ℝ) < r := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hδ]; exact hδr
  have hdistm : dist (-δ) (0 : ℝ) < r := by
    rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos hδ]; exact hδr
  have hp := hball hdistp (ne_of_gt hδ)
  have hm := hball hdistm (neg_ne_zero.mpr (ne_of_gt hδ))
  -- At `h = δ`: `0 < d * f (x₀ + δ)`.
  have h1 : 0 < d * f (x₀ + δ) := by
    have h := hp
    rw [h0, sub_zero] at h
    have h' : 0 < (d * f (x₀ + δ)) * δ⁻¹ := by
      have e : d * (δ⁻¹ * f (x₀ + δ)) = (d * f (x₀ + δ)) * δ⁻¹ := by ring
      rwa [e] at h
    exact pos_of_mul_pos_left h' (le_of_lt (inv_pos.mpr hδ))
  -- At `h = -δ`: `d * f (x₀ - δ) < 0`.
  have h2 : d * f (x₀ - δ) < 0 := by
    have h := hm
    rw [h0, sub_zero] at h
    rw [show x₀ + -δ = x₀ - δ by ring, inv_neg] at h
    have h' : (d * f (x₀ - δ)) * δ⁻¹ < 0 := by
      have e : d * (-δ⁻¹ * f (x₀ - δ)) = -((d * f (x₀ - δ)) * δ⁻¹) := by ring
      rw [e] at h
      linarith
    exact lt_of_mul_lt_mul_right (by simpa using h') (le_of_lt (inv_pos.mpr hδ))
  have h12 : (d * f (x₀ - δ)) * (d * f (x₀ + δ)) < 0 := mul_neg_of_neg_of_pos h2 h1
  have key : (f (x₀ - δ) * f (x₀ + δ)) * (d * d) < 0 := by
    have e : (d * f (x₀ - δ)) * (d * f (x₀ + δ))
        = (f (x₀ - δ) * f (x₀ + δ)) * (d * d) := by ring
    rwa [e] at h12
  exact lt_of_mul_lt_mul_right (by simpa using key) (le_of_lt hd2)

/-- Eventual factorization form: it suffices that `f t = (t - x₀) * G t` holds only on a
neighbourhood of `x₀`. This is the form suited to *rational* functions, whose factorization
by `(t - x₀)` is only valid away from a denominator's zeros, but which are continuous at
`x₀` when the denominator is nonzero there. -/
-- Theorem: sign change at every small radius from an eventual factorization
-- `f = (· - x₀) * G` near `x₀`.
theorem signChange_of_factorization_eventually {f G : ℝ → ℝ} {x₀ : ℝ}
    (hG : ContinuousAt G x₀) (hG0 : G x₀ ≠ 0)
    (hfac : ∀ᶠ t in 𝓝 x₀, f t = (t - x₀) * G t) :
    ∀ ε > 0, ∃ δ, 0 < δ ∧ δ < ε ∧ f (x₀ - δ) * f (x₀ + δ) < 0 := by
  intro ε hε
  -- `G` keeps the sign of `G x₀` on a ball …
  have hpos : ∀ᶠ t in 𝓝 x₀, 0 < G t * G x₀ := by
    have hcont : ContinuousAt (fun t => G t * G x₀) x₀ := hG.mul continuousAt_const
    exact hcont.eventually (isOpen_Ioi.mem_nhds (mul_self_pos.mpr hG0))
  rw [Metric.eventually_nhds_iff] at hpos
  obtain ⟨r₁, hr₁, hball₁⟩ := hpos
  -- … and the factorization holds on a ball.
  rw [Metric.eventually_nhds_iff] at hfac
  obtain ⟨r₂, hr₂, hball₂⟩ := hfac
  set δ : ℝ := min (min (r₁ / 2) (r₂ / 2)) (ε / 2) with hδdef
  have hδ : 0 < δ := by
    rw [hδdef]; exact lt_min (lt_min (by linarith) (by linarith)) (by linarith)
  have hδr₁ : δ < r₁ := by
    rw [hδdef]
    exact lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_left _ _)) (by linarith)
  have hδr₂ : δ < r₂ := by
    rw [hδdef]
    exact lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_right _ _)) (by linarith)
  have hδε : δ < ε := by
    rw [hδdef]
    exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  refine ⟨δ, hδ, hδε, ?_⟩
  have hdisk (t : ℝ) (ht : dist t x₀ < r₂) : f t = (t - x₀) * G t := hball₂ (y := t) ht
  have hdistp : dist (x₀ + δ) x₀ < r₂ := by
    rw [Real.dist_eq]
    have h : x₀ + δ - x₀ = δ := by ring
    rw [h, abs_of_pos hδ]; exact hδr₂
  have hdistm : dist (x₀ - δ) x₀ < r₂ := by
    rw [Real.dist_eq]
    have h : x₀ - δ - x₀ = -δ := by ring
    rw [h, abs_neg, abs_of_pos hδ]; exact hδr₂
  have hsignp : 0 < G (x₀ + δ) * G x₀ := by
    apply hball₁ (y := x₀ + δ)
    rw [Real.dist_eq]
    have h : x₀ + δ - x₀ = δ := by ring
    rw [h, abs_of_pos hδ]; exact hδr₁
  have hsignm : 0 < G (x₀ - δ) * G x₀ := by
    apply hball₁ (y := x₀ - δ)
    rw [Real.dist_eq]
    have h : x₀ - δ - x₀ = -δ := by ring
    rw [h, abs_neg, abs_of_pos hδ]; exact hδr₁
  rw [hdisk (x₀ - δ) hdistm, hdisk (x₀ + δ) hdistp]
  have e1 : x₀ - δ - x₀ = -δ := by ring
  have e2 : x₀ + δ - x₀ = δ := by ring
  rw [e1, e2]
  have hprod : 0 < G (x₀ - δ) * G (x₀ + δ) := by
    have hm : 0 < (G (x₀ - δ) * G x₀) * (G (x₀ + δ) * G x₀) := mul_pos hsignm hsignp
    have e : (G (x₀ - δ) * G x₀) * (G (x₀ + δ) * G x₀)
        = (G (x₀ - δ) * G (x₀ + δ)) * (G x₀) ^ 2 := by ring
    rw [e] at hm
    exact pos_of_mul_pos_left hm (sq_nonneg (G x₀))
  have e3 : (-δ * G (x₀ - δ)) * (δ * G (x₀ + δ))
      = -((δ * δ) * (G (x₀ - δ) * G (x₀ + δ))) := by ring
  rw [e3]
  have hq : 0 < (δ * δ) * (G (x₀ - δ) * G (x₀ + δ)) := mul_pos (mul_pos hδ hδ) hprod
  linarith

end Pconstructible
