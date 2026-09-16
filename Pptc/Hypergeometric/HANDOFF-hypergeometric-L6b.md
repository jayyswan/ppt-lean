# HANDOFF hypergeometric L6b (Clausen ₃F₂)

Goal (Lean):
```lean
theorem clausen_tsum_Pconstructible {x : ℝ} (hx : PConstructible x) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    PConstructible (∑' n : ℕ, (Nat.choose (2 * n) n : ℝ) ^ 3 * (x / 64) ^ n)
```
Target file: `Pptc/Hypergeometric/Clausen.lean` (new). Declaration: `clausen_tsum_Pconstructible`.

Plan:
1. Land `hyp_one_fourth_squared_Pconstructible`: `hyp (1/4)(1/4)1 x` and its square are
   PConstructible for PConstructible `x ∈ [0,1)`, via `hyp_quadratic` at `z=(1-√(1-x))/2`.
2. Try Clausen's identity `Σ C(2n,n)³(x/64)ⁿ = hyp(1/4)(1/4)1 x ^ 2` directly.
3. If it resists, state it as an explicit hypothesis and land the conditional version.

## Log
- [start] Created log. Read PLAN §2 V6/§5 B3/§6, Quadratic.lean (landed `hyp_quadratic`).
- [api] Read Basic.lean (hyp/hypCoeff/hasSum_hyp/hyp_eq_of_hasSum), Elliptic
  (`hyp_half_half_one_Pconstructible`), Signatures (V7 conditional pattern), `sqrt_Pconstructible`.
- [write v1] Wrote Clausen.lean: unconditional `hyp_one_fourth_one_Pconstructible`,
  `hyp_one_fourth_squared_Pconstructible`, conditional `clausen_tsum_Pconstructible`.
  Helper lemmas `four_mul_half_sub_sqrt_one_sub`, `half_sub_sqrt_one_sub_mem`.
- [verify] Wolfram: coefficient convolution identity
  `Σ_k ((1/4)_k/k!)²((1/4)_{n-k}/(n-k)!)² = ((1/2)_n/n!)³` holds n=0..8 (exact 0);
  ODE `x²(1-x)G'''+(3x-9x²/2)G''+(1-13x/4)G'-G/8=0` for G=₂F₁(1/4,1/4;1;x)² holds
  (series to x^6 == 0). Route 1 is viable.
- [diag] Waiting on first elaboration (heavy imports).
- [diag OK] Clausen.lean compiles clean, zero diagnostics. Route 2 deliverable safe.
- [next] Attempt Route 1: formal Clausen via ODE for `hypSeries(1/4)(1/4)1 ^ 2` + coefficient
  recurrence + Cauchy-product real transfer. Searching for Cauchy product lemma.

## L6b round 2 (make Clausen unconditional)
- [start] Read Clausen.lean (262 lines, clean). Target: prove the identity unconditionally via ODE + Cauchy product.
- [plan] Route: (a) extract recurrence 8(n+1)^3 g_{n+1}=(2n+1)^3 g_n from qG_ode_expand; (b) d n=C(2n,n)^3/64^n satisfies same; (c) g=d; (d) Cauchy product via hasSum_sum_range_mul_of_summable_norm to transfer to reals.
- [wip] Added qG_coeff_rec_zero/one/two, qG_coeff_rec (X^(k+3) extraction), qG_coeff_rec_all. Iterating on simp coefficient extraction.
- [wip] Recurrence lemmas compile clean. Added clausenCoeff, coeff_zero_qG, clausenCoeff_eq_coeff_qG, hypCoeff_quarter_quarter_one_mem_Icc, clausen_hasSum, clausen_tsum_eq, unconditional clausen_tsum_Pconstructible. Fixing remaining rw errors.

## DONE (L6b round 2)
- Clausen is now UNCONDITIONAL. File: Pptc/Hypergeometric/Clausen.lean.
- Landed: coeff_X_sq_mul_add_three, qG_coeff_rec_zero/one/two, qG_coeff_rec (X^(k+3) extraction), qG_coeff_rec_all (8(n+1)^3 g_{n+1}=(2n+1)^3 g_n); clausenCoeff = C(2n,n)^3/64^n with clausenCoeff_zero/succ; coeff_zero_qG; clausenCoeff_eq_coeff_qG (coeff n qG = d n); hypCoeff_quarter_quarter_one_mem_Icc; clausen_hasSum (Cauchy product via hasSum_sum_range_mul_of_summable_norm); clausen_tsum_eq; unconditional clausen_tsum_Pconstructible.
- lean_diagnostic_messages: success=true, items=[] (zero errors/warnings).
- lean_verify clausen_tsum_Pconstructible / clausen_tsum_eq: axioms = [propext, Classical.choice, Quot.sound]. No sorry/admit, no new imports, no whole-project build.
- Remaining gap: none. (Pre-existing line 135 of the Route-1 docstring is 116 chars; left untouched.)
