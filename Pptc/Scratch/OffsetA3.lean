import Pptc.Offset

/-! # Pptc.Scratch.OffsetA3 — scratch for task A3 (offset × offset, self-crossings, cusps)

This file is a private scratch file for the offset research programme task A3. It is imported
by nothing. Nothing here is needed by the library; the goal is to *pin the headline claims as
precise Lean statements* so a future formalisation has an exact target.

The two definitions below are the rationalised offset×offset system: equating
`γ₁(t₁)+d₁N₁(t₁) = γ₂(t₂)+d₂N₂(t₂)` and clearing the denominators `w₁w₂` gives `E₁=E₂=0`,
and the free variables `wᵢ` satisfy `wᵢ² = speed²`. Both signs of `wᵢ` are present at once,
which is exactly the freedom to use `offset` with either sign of `d` (Defs.lean).

The theorem below is the honest crossing statement. Its proof is not carried out here (the
manipulation of `unitNormal`/`speed` and the case `speed = 0` is routine but lengthy) and is
recorded as `sorry`. Per the programme's rules this counts as UNPROVED. -/

namespace Pconstructible

/-- First rationalised equation of the offset×offset system. -/
def offsetOffsetE1 (c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃ f₀ f₁ f₂ f₃ g₀ g₁ g₂ g₃
    d₁ d₂ w₁ w₂ t₁ t₂ : ℝ) : ℝ :=
  (cubicVal c₀ c₁ c₂ c₃ t₁ - cubicVal f₀ f₁ f₂ f₃ t₂) * w₁ * w₂
    - d₁ * cubicDer e₁ e₂ e₃ t₁ * w₂ + d₂ * cubicDer g₁ g₂ g₃ t₂ * w₁

/-- Second rationalised equation of the offset×offset system. -/
def offsetOffsetE2 (c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃ f₀ f₁ f₂ f₃ g₀ g₁ g₂ g₃
    d₁ d₂ w₁ w₂ t₁ t₂ : ℝ) : ℝ :=
  (cubicVal e₀ e₁ e₂ e₃ t₁ - cubicVal g₀ g₁ g₂ g₃ t₂) * w₁ * w₂
    + d₁ * cubicDer c₁ c₂ c₃ t₁ * w₂ - d₂ * cubicDer f₁ f₂ f₃ t₂ * w₁

-- Theorem [UNPROVED in this file]: a genuine crossing of the two cubic-pair offsets, at
-- regular parameters, satisfies the first rationalised equation with `wᵢ = speed γᵢ tᵢ`.
-- The reduction is `line_offset_mul_speed`'s pattern applied to the difference of the two
-- offsets; the `speed = 0` case is excluded by the regularity hypotheses.
theorem offsetOffsetE1_eq_zero_of_cross
    (c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃ f₀ f₁ f₂ f₃ g₀ g₁ g₂ g₃ d₁ d₂ t₁ t₂ : ℝ)
    (hreg₁ : speed (cubicPairParam c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃) t₁ ≠ 0)
    (hreg₂ : speed (cubicPairParam f₀ f₁ f₂ f₃ g₀ g₁ g₂ g₃) t₂ ≠ 0)
    (h : offsetParam (cubicPairParam c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃) d₁ t₁
       = offsetParam (cubicPairParam f₀ f₁ f₂ f₃ g₀ g₁ g₂ g₃) d₂ t₂) :
    offsetOffsetE1 c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃ f₀ f₁ f₂ f₃ g₀ g₁ g₂ g₃ d₁ d₂
      (speed (cubicPairParam c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃) t₁)
      (speed (cubicPairParam f₀ f₁ f₂ f₃ g₀ g₁ g₂ g₃) t₂) t₁ t₂ = 0 := by
  sorry

-- Theorem [UNPROVED in this file, the A3 headline]: if the second offset curve is a
-- PConstructibleCurve `T` and the composite `F ∘ offsetParam` has finitely many zeros
-- along the first offset, then the coordinates of a crossing and the parameters behind it
-- are P-constructible. This is `offsetCubicPair_cross_point_Pconstructible` /
-- `offsetCubicPair_cross_root_Pconstructible` applied with `T` the second offset arc; the
-- only input A3 does not formalise is the finiteness bound (the degree-92 elimination).
theorem offsetOffset_cross_root_Pconstructible
    {T : Set (ℝ × ℝ)} (hT : PConstructibleCurve T) {F : ℝ → ℝ → ℝ}
    {c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃ d₁ β : ℝ}
    (hc₀ : PConstructible c₀) (hc₁ : PConstructible c₁) (hc₂ : PConstructible c₂)
    (hc₃ : PConstructible c₃) (he₀ : PConstructible e₀) (he₁ : PConstructible e₁)
    (he₂ : PConstructible e₂) (he₃ : PConstructible e₃) (hd : PConstructible d₁)
    (hTzero : ∀ q ∈ T, F q.1 q.2 = 0)
    (hfin : {t : ℝ | F (offsetParam (cubicPairParam c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃) d₁ t).1
        (offsetParam (cubicPairParam c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃) d₁ t).2 = 0}.Finite)
    (hcubic : c₃ ≠ 0 ∨ e₃ ≠ 0)
    (hreg : cubicDer c₁ c₂ c₃ β ≠ 0 ∨ cubicDer e₁ e₂ e₃ β ≠ 0)
    (hβT : offsetParam (cubicPairParam c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃) d₁ β ∈ T) :
    PConstructible β := by
  exact offsetCubicPair_cross_root_Pconstructible hT hc₀ hc₁ hc₂ hc₃ he₀ he₁ he₂ he₃
    hd hTzero hfin hcubic hreg hβT

end Pconstructible
