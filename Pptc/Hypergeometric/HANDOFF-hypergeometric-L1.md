# HANDOFF — hypergeometric L1 (`Pptc/Hypergeometric/Basic.lean`)

Task: wave-0 critical path. Deliverable: the ₂F₁ API contract (hyp, hypCoeff,
hyp_eq_tsum_coeff, hasSum_hyp, hyp_eq_of_hasSum, hypCoeff_succ) plus the elementary
closed forms H1. Depends on: none (only `Pptc.Basic` for H1).

## Log

- [start] read PLAN-hypergeometric-00-overview.md; surveyed `Pptc/Defs.lean`,
  `Pptc/Basic.lean`, `Pptc/Tactic.lean`, Mathlib `OrdinaryHypergeometric.lean`,
  `Analytic/Binomial.lean`, `Analytic/ConvergenceRadius.lean`. No hypergeometric
  directory existed yet.
- [decision] namespace `Pconstructible`; module `Pptc.Hypergeometric.Basic`; imports
  `Pptc.Basic` + `Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric` +
  `Mathlib.Analysis.Analytic.Binomial`.
- [done] contract: `hyp`, `hypCoeff`, `hyp_eq_tsum_coeff`, `hasSum_hyp`,
  `hyp_eq_of_hasSum`, `hypCoeff_succ`. All compile clean; `lake env lean` OK.
- [done] `.olean` built: `lake build Pptc.Hypergeometric.Basic` succeeded (~20 s).
- [done] H1 case A: `ring_choose_eq_ascPochhammer`, `hyp_self_eq_rpow`
  (`₂F₁(a,b;b;z) = (1-z)^(-a)`, `b ∉ -ℕ`, `|z|<1`). Template: power series of the closed
  form via `Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero` + `hyp_eq_of_hasSum`.
- [todo] H1 cases B/C/D: `₂F₁(1,1;2;z) = -log(1-z)/z`, `₂F₁(½,1;3/2;-z²) = arctan z/z`,
  `₂F₁(½,½;3/2;z²) = arcsin z/z` (all with `z ≠ 0`; at `z = 0` both RHS are `0/0 = 0`
  while the LHS is `1`). Series lemmas found:
  `Real.hasSum_pow_div_log_of_abs_lt_one` (B), `Real.hasSum_arctan` (C). Mathlib has **no
  arcsin series**, so D needs one derived (e.g. via `arcsin = arctan ∘ (z/√(1-z²))` or
  from the binomial series). These need pointwise `HasSum.unique` rather than the function
  form of `hyp_eq_of_hasSum`, since the RHS is only meaningful away from `0`.
- [follow-up] PConstructible corollaries of A–D (tag `@[pconstructible_cond]`), using
  `rpow_Pconstructible` / `log_Pconstructible` / `arctan_Pconstructible` / `arcsin_Pconstructible`.
- [L1-resume] starting B/C/D identities + PConstructible corollaries A-D; read Basic.lean (A template) and plan.
- [L1-resume] confirmed reachable: Real.hasSum_pow_div_log_of_abs_lt_one, Real.hasSum_arctan, ascPochhammer_eval_one, factorial_mul_ascPochhammer, HasSum.div_const. No arcsin series in Mathlib (D likely blocked).
- [done] H1 B: hyp_one_one_two + hypCoeff_one_one_two; H1 C: hyp_half_one_three_half + hypCoeff_half_one_three_half. Corollaries A/B/C (hyp_self_Pconstructible, hyp_one_one_two_Pconstructible, hyp_half_one_three_half_Pconstructible) all compile. Diagnostics clean (was: hc positivity, typeclass stuck via Nat.cast_nonneg annotation, implicit-arg mismatch for hasSum_hyp z:=-(z^2), push_cast/ring cleanup).
- [todo] D: attempting arcsin power series via binomial + termwise integration; Mathlib has no arcsin series.
- [done] diagnostics clean (success:true, no warnings) on Pptc/Hypergeometric/Basic.lean. Declarations added: hypCoeff_one_one_two, hypCoeff_half_one_three_half, hyp_one_one_two, hyp_half_one_three_half, hyp_self_Pconstructible, hyp_one_one_two_Pconstructible, hyp_half_one_three_half_PConstructible. Added import Mathlib.Analysis.SpecialFunctions.Complex.Arctan (Real.hasSum_arctan not otherwise reachable).
- [BLOCKED] H1 D (hyp_half_half_three_half: 2F1(1/2,1/2;3/2;z^2)=arcsin z/z) OMITTED, and its PConstructible corollary too. Reason: Mathlib has NO arcsine power series (no hasSum_arcsin / arcsin_eq_tsum; searched local + leansearch). Deriving it needs either (i) binomial series for 1/sqrt(1-t^2) + justified termwise integration (intervalIntegral.hasSum_integral_of_dominated_convergence) or (ii) composing HasFPowerSeriesOnBall of arctan with x/sqrt(1-x^2) � both substantial new developments, out of scope for this run. Needed coefficient fact (checked, unused): hypCoeff (1/2)(1/2)(3/2) n = (Nat.choose (2*n) n)/(4^n*(2n+1)).
- [final] lake env lean Pptc/Hypergeometric/Basic.lean => OK - no errors or warnings. B, C identities + corollaries A/B/C landed; D omitted (blocked as above). Existing declarations untouched.

- [D-start] resuming H1 case D. Plan: binomial series for (1-t^2)^(-1/2), termwise interval integration to get arcsin HasSum, then HasSum.unique against hasSum_hyp; plus coefficient lemma hypCoeff_half_half_three_half = C(2n,n)/(4^n(2n+1)). Target file Pptc/Hypergeometric/Basic.lean; insert before final end.
- [D-1] read file (326 lines); A/B/C templates understood. Searching Mathlib for arcsin series / integral of (1-t^2)^(-1/2) / dominated convergence exact signatures.
- [D-2] found: `Nat.succ_mul_centralBinom_succ` ((n+1)C(2n+2,n+1)=2(2n+1)C(2n,n)); `ascPochhammer_succ_eval`; `Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero` gives 1/(1-x)^(1/2) with coeffs Ring.choose(1/2+n-1)n = (1/2)_n/n!; `Real.deriv_arcsin`; `hasSum_integral_of_dominated_convergence` (intervalIntegral version, DominatedConvergence.lean:203). Plan: use positive binomial series 1/sqrt(1-t^2) to avoid abs values in bound.
- [D-3] DONE both coefficient lemmas, diagnostics clean (no errors/warnings): `ascPochhammer_one_div_two` (line 338), `hypCoeff_half_half_three_half` (line 359, exact target form). Next: ring_choose identity + arcsin HasSum via dominated convergence.
- [D-4] DONE `hasSum_inv_sqrt_one_sub_sq` (binomial series 1/sqrt(1-t^2), coeffs C(2n,n)/4^n) and `hasSum_arcsin` (arcsin HasSum via intervalIntegral.hasSum_integral_of_dominated_convergence + FTC). Imports added: InverseDeriv, Integrals.Basic, DominatedConvergence. Diagnostics: success (one long-line warning being fixed). Next: theorem D + PConstructible corollary.
- [D-5] DONE theorem D `hyp_half_half_three_half` and corollary `hyp_half_half_three_half_Pconstructible`. lean_diagnostic_messages: success, zero errors, zero warnings. D no longer BLOCKED. Running lake_check for final confirmation.
- [final-D] lake_check Pptc/Hypergeometric/Basic.lean => "OK - no errors or warnings." No sorry/axiom. Added (line numbers): ascPochhammer_one_div_two (341), hypCoeff_half_half_three_half (362), hasSum_inv_sqrt_one_sub_sq (382), hasSum_arcsin (410), hyp_half_half_three_half (489), hyp_half_half_three_half_Pconstructible (509). Imports +3: Trigonometric.InverseDeriv, Integrals.Basic, MeasureTheory.Integral.DominatedConvergence. Key lemmas used: Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero, FormalMultilinearSeries.ofScalars_apply_eq, ring_choose_eq_ascPochhammer, Nat.succ_mul_centralBinom_succ, intervalIntegral.hasSum_integral_of_dominated_convergence, integral_pow (root ns!), intervalIntegral.integral_deriv_eq_sub, Real.deriv_arcsin, Real.sqrt_eq_rpow. Gotchas hit: integral_pow is root-namespaced not intervalIntegral.; `volume` needs MeasureTheory.volume; ring_nf/ring can't equate 4⁻¹^n with (4^n)⁻¹ — use field_simp; Real.deriv_arcsin rewrite leaves beta-redex so use simp only.
