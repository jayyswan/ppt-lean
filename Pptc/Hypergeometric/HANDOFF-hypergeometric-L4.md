# HANDOFF — L4: Gauss summation & denominator-24 family

Goal (Lean):
```
theorem hyp_one_eq_Gamma {a b c : ℝ} (h : 0 < c - a - b) (hc : ∀ n : ℕ, c ≠ -(n : ℝ)) :
    hyp a b c 1 = Real.Gamma c * Real.Gamma (c - a - b) / (Real.Gamma (c - a) * Real.Gamma (c - b))

theorem hyp_one_Pconstructible_of_den_24 ... : PConstructible (hyp a b c 1)
```
Target file: Pptc/Hypergeometric/Gauss.lean
Plan: use L7a `hyp_eq_integral` at z=1 -> Beta integral -> Gamma; headline via Gamma_intCast_div_twentyfour_Pconstructible.

## Log
- [start] created handoff.
- [read] Basic/Euler/Gamma. Euler has `hyp_eq_integral` (needs |z|<1), `integral_rpow_mul_one_sub_rpow`, `Gamma_add_nat`, `integral_term`, `intervalIntegrable_weight`, `hypCoeff_self`, `ne_neg_nat_of_pos`. Gamma has `Gamma_intCast_div_twentyfour_Pconstructible (n:ℤ) : PConstructible (Γ(n/24))`.
- [plan] z=1 integral can't use hyp_eq_integral (needs |z|<1). Instead: nonneg Tonelli/DCT via `intervalIntegral.hasSum_integral_of_dominated_convergence`, expanding (1-t)^{-a} in the `hyp a b b` series, bound n t = hypCoeff a b b n * t^n * w(t) ≥ 0. Needs a>0,b>0,b<c,c-a-b>0, plus hc. Then term integrals via `integral_term` at z=1; closing integral via `integral_rpow_mul_one_sub_rpow b (c-a-b)`.
- [landed] `hyp_one_eq_Gamma {a b c} (ha:0<a)(hb:0<b)(hbc:b<c)(h:0<c-a-b)(hc:∀n,c≠-n) : hyp a b c 1 = Γc·Γ(c-a-b)/(Γ(c-a)·Γ(c-b))`. NOTE: task's stated signature lacked ha/hb/hbc; the a>0,b>0 route is the only one that avoids needing Gauss-convergence of the series at 1 (which is itself equivalent to the theorem). hc is unused in the proof but kept.
- [landed] `hyp_one_Pconstructible_of_den_24 {m n l:ℤ} (hm:0<m)(hn:0<n)(h:0<(l-m-n)/24)(hc) : PConstructible (hyp (m/24)(n/24)(l/24) 1)`. Extra hm/hn needed because hyp_one_eq_Gamma needs a,b>0. Uses `Gamma_intCast_div_twentyfour_Pconstructible` on l, l-m-n, l-m, l-n.
- [diag] Gauss.lean: success, only an unnecessarySimpa warning (fixed).
- [check] running lake_check next.
- [check] `lake_check Pptc/Hypergeometric/Gauss.lean` => OK, no errors or warnings.
- [verify] axioms of both theorems = propext, Classical.choice, Quot.sound.
- [part 3] NOT attempted: Gauss's second theorem / Kummer need the quadratic transformation (L6a) which is not a dependency of L4 and was not available. No partial work left behind.
- [deviation] Requested `hyp_one_eq_Gamma` had only (h, hc); landed version also needs (ha:0<a)(hb:0<b)(hbc:b<c). Route: nonneg DCT at z=1. Dropping them requires an analytic-continuation / contiguous-relation extension that is a separate task; documented in the docstring.
- [final] Gauss.lean compiles clean, no sorry/axiom.
