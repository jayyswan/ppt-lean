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

import Pptc.TotallyReal.Engines
import Pptc.Basic

/-! # Pptc.Octic.Engine

The octic power-law engine (Part A of `Pptc/Octic/PLAN.md`): a real `β` with

    β ^ 8 = c₄ β⁴ + c₃ β³ + c₂ β² + c₁ β + c₀

is P-constructible, when all five coefficients are.

This is the quartic counterpart of `powerLaw_cubic_root_PConstructible`: the resolvent of a
Tschirnhaus-reduced octic is of the shape `Q(t²) = c t` with `Q` a monic quartic, so after
writing `x = β²` one has to cross the power curve `y = x ^ 4` with a quartic graph rather
than with a cubic one.  The graph of a general quartic with nonzero leading coefficient is
the graph of a monic one scaled in the `y` direction by `c₄` (`scale_y`), which is the only
new ingredient over the septic engine.  The leading coefficient zero case degenerates to
the cubic engine.

Geometry: the curve `y = x ^ 8` is `power_law 1 8`, and the quartic is drawn by
`quarticGraph_general_PConstructibleCurve`.  Their crossing is isolated by a rational
window; uniqueness comes from `X ^ 8 - quartic ≠ 0`, which has finite root set, so
`exists_rat_isolating` supplies the window and `inter_x` reads off the abscissa.
-/

namespace Pconstructible

open Polynomial

/-! ### Quartic graphs with a general leading coefficient -/

-- Theorem: the graph of a quartic with P-constructible coefficients and nonzero leading
-- coefficient is a constructible curve.
theorem quarticGraph_general_PConstructibleCurve {c₀ c₁ c₂ c₃ c₄ : ℝ}
    (h₀ : PConstructible c₀) (h₁ : PConstructible c₁) (h₂ : PConstructible c₂)
    (h₃ : PConstructible c₃) (h₄ : PConstructible c₄) (hc₄ : c₄ ≠ 0) :
    PConstructibleCurve (quarticGraph c₀ c₁ c₂ c₃ c₄) := by
  have hval : ∀ x : ℝ, quarticVal c₀ c₁ c₂ c₃ c₄ x
      = c₄ * quarticVal (c₀ / c₄) (c₁ / c₄) (c₂ / c₄) (c₃ / c₄) 1 x := by
    intro x
    simp only [quarticVal]
    field_simp
  have hset : quarticGraph c₀ c₁ c₂ c₃ c₄
      = (fun p : ℝ × ℝ => (p.1, c₄ * p.2)) ''
          quarticGraph (c₀ / c₄) (c₁ / c₄) (c₂ / c₄) (c₃ / c₄) 1 := by
    ext ⟨a, b⟩
    simp only [quarticGraph, Set.mem_ofPred_eq, Set.mem_image, Prod.mk.injEq]
    constructor
    · intro hb
      refine ⟨(a, b / c₄), ?_, rfl, ?_⟩
      · rw [hval a] at hb
        rw [hb]
        field_simp
      · field_simp
    · rintro ⟨p, hp, hpa, hpb⟩
      subst hpa
      rw [← hpb, hval, hp]
  rw [hset]
  exact (quarticGraph_PConstructibleCurve
    (PConstructible.div h₀ h₄) (PConstructible.div h₁ h₄)
    (PConstructible.div h₂ h₄) (PConstructible.div h₃ h₄)).scale_y h₄

/-! ### Solving `β ^ 8 = quartic` -/

-- Theorem: a positive root of `x ^ 8 = quarticVal c₀ c₁ c₂ c₃ c₄ x`, with P-constructible
-- coefficients and nonzero leading coefficient, is P-constructible.
theorem powerLaw_quartic_root_pos_PConstructible {c₀ c₁ c₂ c₃ c₄ β : ℝ}
    (h₀ : PConstructible c₀) (h₁ : PConstructible c₁) (h₂ : PConstructible c₂)
    (h₃ : PConstructible c₃) (h₄ : PConstructible c₄) (hc₄ : c₄ ≠ 0) (hβ : 0 < β)
    (heq : β ^ 8 = quarticVal c₀ c₁ c₂ c₃ c₄ β) : PConstructible β := by
  set P : Polynomial ℝ :=
    X ^ 8 - (C c₄ * X ^ 4 + C c₃ * X ^ 3 + C c₂ * X ^ 2 + C c₁ * X + C c₀) with hPdef
  have hevalP : ∀ t : ℝ, P.eval t = t ^ 8 - quarticVal c₀ c₁ c₂ c₃ c₄ t := by
    intro t
    simp [hPdef, quarticVal]
  have hPne : P ≠ 0 := by
    intro hc
    have hcn : P.coeff 8 = 1 := by
      simp [hPdef, Polynomial.coeff_X_pow]
    rw [hc] at hcn
    simp at hcn
  have hroot : P.IsRoot β := by
    rw [Polynomial.IsRoot, hevalP, heq, sub_self]
  have hAfin : {t : ℝ | P.IsRoot t ∧ t ≠ β}.Finite :=
    (Polynomial.finite_setOfPred_isRoot hPne).subset (fun t ht => ht.1)
  obtain ⟨q₁, q₂, hq₁b, hq₂a, huniq⟩ := exists_rat_isolating hAfin
  have hT := quarticGraph_general_PConstructibleCurve h₀ h₁ h₂ h₃ h₄ hc₄
  have hS := (PConstructibleCurve.power_law (1 : ℚ) (8 : ℚ)).restrict
    (q₁ : ℝ) (q₂ : ℝ) 0 ((q₂ : ℝ) ^ 8 + 1)
    (rat_Pconstructible q₁) (rat_Pconstructible q₂) zero_Pconstructible
    (PConstructible.add (pow_Pconstructible (rat_Pconstructible q₂) 8)
      PConstructible.base_one)
  refine PConstructible.inter_x hS hT (x := β) (y := β ^ 8) ?_
  have hpow : ∀ t : ℝ, 0 < t → t ^ (((8 : ℚ) : ℝ)) = t ^ 8 := by
    intro t ht
    push_cast
    exact Real.rpow_natCast t 8
  ext ⟨a, b⟩
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, quarticGraph, Set.mem_singleton_iff,
    Prod.mk.injEq]
  constructor
  · rintro ⟨⟨⟨hapos, hb⟩, hlo, hhi, _h0, _hy⟩, hgraph⟩
    rw [hpow a hapos] at hb
    norm_num at hb
    have hra : P.IsRoot a := by
      rw [Polynomial.IsRoot, hevalP, ← hgraph, ← hb, sub_self]
    have ha : a = β := huniq a hra hlo hhi
    exact ⟨ha, by rw [hb, ha]⟩
  · rintro ⟨ha, hb⟩
    rw [ha, hb]
    have hpos : (0 : ℝ) < β ^ 8 := by positivity
    have hlt : β ^ 8 < (q₂ : ℝ) ^ 8 + 1 := by
      have h : β ^ 8 < (q₂ : ℝ) ^ 8 :=
        pow_lt_pow_left₀ hq₂a hβ.le (by norm_num)
      linarith
    refine ⟨⟨⟨hβ, ?_⟩, hq₁b.le, hq₂a.le, hpos.le, hlt.le⟩, heq⟩
    rw [hpow β hβ]
    ring

-- Theorem: the same for any root, by reflecting the negative case in the `y` axis. For
-- `n = 8` the reflection sends `quarticVal c₀ c₁ c₂ c₃ c₄` to
-- `quarticVal c₀ (-c₁) c₂ (-c₃) c₄`.
theorem powerLaw_quartic_root_PConstructible {c₀ c₁ c₂ c₃ c₄ β : ℝ}
    (h₀ : PConstructible c₀) (h₁ : PConstructible c₁) (h₂ : PConstructible c₂)
    (h₃ : PConstructible c₃) (h₄ : PConstructible c₄)
    (heq : β ^ 8 = quarticVal c₀ c₁ c₂ c₃ c₄ β) : PConstructible β := by
  rcases eq_or_ne c₄ 0 with hc₄ | hc₄
  · subst hc₄
    have heq' : β ^ 8 = cubicVal c₀ c₁ c₂ c₃ β := by
      simpa [quarticVal, cubicVal] using heq
    exact powerLaw_cubic_root_Pconstructible (n := 8) (by norm_num) h₀ h₁ h₂ h₃ heq'
  · rcases lt_trichotomy β 0 with hneg | rfl | hpos
    · have heq' : (-β) ^ 8 =
          quarticVal c₀ (-c₁) c₂ (-c₃) c₄ (-β) := by
        simp only [quarticVal] at heq ⊢
        rw [show (-β) ^ 8 = β ^ 8 by ring]
        rw [heq]
        ring
      have := powerLaw_quartic_root_pos_PConstructible h₀ (neg_Pconstructible h₁) h₂
        (neg_Pconstructible h₃) h₄ hc₄ (by linarith : (0 : ℝ) < -β) heq'
      simpa using neg_Pconstructible this
    · exact zero_Pconstructible
    · exact powerLaw_quartic_root_pos_PConstructible h₀ h₁ h₂ h₃ h₄ hc₄ hpos heq

end Pconstructible
