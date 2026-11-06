# HANDOFF — half_quartic_root_Pconstructible (Lemma E8)

Goal (in `pptc/Pptc/TotallyReal/Engines.lean`):

```lean
theorem half_quartic_root_Pconstructible {q₀ q₁ q₂ q₃ c β : ℝ}
    (h₀ : PConstructible q₀) (h₁ : PConstructible q₁) (h₂ : PConstructible q₂)
    (h₃ : PConstructible q₃) (hc : PConstructible c)
    (heq : quarticVal q₀ q₁ q₂ q₃ 1 (β ^ 2) = c * β) :
    PConstructible β
```

Plan: mirror `negHalf_cubic_root_Pconstructible` (Lemma E7, already proved in the same
file): split on `c = 0` (→ `quarticVal_root_Pconstructible`) and `β = 0`; otherwise
cross the `quarticGraph q₀ q₁ q₂ q₃ 1` graph with `scale_y (sgn β · c) (power_law 1 (1/2))`,
read off `x = β² > 0` via `inter_x`, then `β = sgn β · √x`.

Status: PROVED (all 6 defects fixed + a 7th found: `obtain ⟨q₁, q₂, …⟩` from
`exists_rat_isolating` shadowed the coefficients `q₁ q₂`; isolating endpoints renamed to
`u v`). Route: `c = 0` → `quarticVal_root_Pconstructible` + `√(β²)=±β`; `β = 0` →
`zero_Pconstructible`; otherwise cross `quarticGraph q₀ q₁ q₂ q₃ 1` (restricted to a rational
isolating interval `[u,v]` and to `|y| ≤ n`) with `scale_y (sgn β · c) (power_law 1 (1/2))`.
Isolating polynomial is `N := W ^ 2 - C (c ^ 2) * X` (degree 8, monic) where
`W := X ^ 4 + (C q₃ * X ^ 3 + C q₂ * X ^ 2 + C q₁ * X + C q₀)`; `N ≠ 0` from
`(W^2).coeff 8 = 1` vs `(C (c^2) * X).coeff 8 = 0`.
`W.natDegree = 4` via `Polynomial.natDegree_eq_of_le_of_coeff_ne_zero` +
`natDegree_add_le_of_degree_le` (avoids the metavariable/omega flakiness).
`W.leadingCoeff = 1` by `change` (leadingCoeff *is* `coeff p (natDegree p)` in this Mathlib);
`(W^2).coeff 8` via `Polynomial.coeff_pow_mul_natDegree`.
`(β²)^(1/2) = ±β` via `Real.sqrt_eq_rpow` + `Real.sqrt_sq_eq_abs`.
`lean_verify`: axioms `propext, Classical.choice, Quot.sound` only; no errors/warnings.

Status: DONE — `lake_check Pptc/TotallyReal/Engines.lean` = "OK - no errors or warnings".
No new top-level declarations were introduced (only the existing six theorems changed;
`half_quartic_root_Pconstructible` is now a real proof, statement unchanged).
