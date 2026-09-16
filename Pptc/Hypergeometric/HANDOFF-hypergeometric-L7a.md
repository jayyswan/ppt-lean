# HANDOFF — L7a: Euler integral representation

## Goal (Lean syntax)

```
theorem hyp_eq_integral {a b c z : ℝ} (hb : 0 < b) (hbc : b < c) (hz : |z| < 1)
    (hc : ∀ n : ℕ, c ≠ -(n : ℝ)) :
    hyp a b c z = Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b)) *
      ∫ t in (0:ℝ)..1, t ^ (b - 1) * (1 - t) ^ (c - b - 1) * (1 - z * t) ^ (-a)
```

File: `Pptc/Hypergeometric/Euler.lean`, namespace `Pconstructible`.
Plan: expand `(1-zt)^{-a}` with the binomial series / `hyp a 1 1`,
integrate termwise (`intervalIntegral.hasSum_integral_of_dominated_convergence`),
evaluate each term with the Beta integral, match `hypCoeff a b c n`.

## Log

- [start] Read AGENTS.md, plan overview, Basic.lean. Created this log.
- Found: no real Beta integral in Mathlib; `Complex.betaIntegral` + `Complex.betaIntegral_eq_Gamma_mul_div`
  in `Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean`. Real integrability via
  `intervalIntegral.intervalIntegrable_rpow'` (`Mathlib/.../Integrability/Basic.lean`).
- DONE `integral_rpow_mul_one_sub_rpow`: `∫₀¹ x^(p-1)(1-x)^(q-1) = Γp Γq/Γ(p+q)` for p,q>0.
  Compiles (lean_diagnostic_messages empty).
- DONE `intervalIntegrable_weight`, `Gamma_add_nat`, `hypCoeff_self`. Compiles clean.
  Gotchas hit: `volume` must be `MeasureTheory.volume`; `[[a,b]]` notation needs `Set.uIcc`;
  `ContinuousOn.rpow_const` goal does not reduce lambda (use `change`).
- DONE `ne_neg_nat_of_pos`, `integral_term` (term-by-term integral). Compiles clean.
- Next: main `hyp_eq_integral` via `intervalIntegral.hasSum_integral_of_dominated_convergence`
  with bound `|hypCoeff a b b n| ρ^n g t`, `|z| < ρ < 1`.
- DONE main `hyp_eq_integral` (Euler integral representation, exact requested statement).
  Compiles clean (lean_diagnostic_messages empty). Remaining: final `lake_check`.
- FINAL: `lake_check Pptc/Hypergeometric/Euler.lean` => "OK - no errors or warnings".
  `lean_verify Pconstructible.hyp_eq_integral` => only propext, Classical.choice, Quot.sound.
  Declarations:
    * `integral_rpow_mul_one_sub_rpow (p q : ℝ) (hp : 0 < p) (hq : 0 < q)`:
      `∫ x in 0..1, x^(p-1)*(1-x)^(q-1) = Γ p * Γ q / Γ(p+q)`
    * `intervalIntegrable_weight (b c : ℝ) (hb : 0 < b) (hbc : b < c)`:
      `IntervalIntegrable (fun t => t^(b-1)*(1-t)^(c-b-1)) volume 0 1`
    * `Gamma_add_nat (s : ℝ) (hs : 0 < s) (n : ℕ)`:
      `Γ(s+n) = (ascPochhammer ℝ n).eval s * Γ s`
    * `hypCoeff_self (a b : ℝ) (hb : ∀ n, b ≠ -n) (n : ℕ)`:
      `hypCoeff a b b n = (ascPochhammer ℝ n).eval a / n!`
    * `ne_neg_nat_of_pos`, `integral_term`
    * `hyp_eq_integral {a b c z : ℝ} (hb : 0 < b) (hbc : b < c) (hz : |z| < 1)
        (hc : ∀ n : ℕ, c ≠ -(n:ℝ))`:
      `hyp a b c z = Γ c / (Γ b * Γ (c-b)) *
        ∫ t in 0..1, t^(b-1)*(1-t)^(c-b-1)*(1-z*t)^(-a)`
  No restrictions beyond the expected `c > b > 0`, `|z| < 1`, `c ∉ -ℕ`.
- `lake build Pptc.Hypergeometric.Euler` => success (olean written; L7b can import).
