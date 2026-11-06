# Phase 4: Pfaff + continuity at -1

Goal (Lean syntax):
```
theorem hyp_pfaff {a b c z : ℝ} (hc : ∀ n : ℕ, c ≠ -(n : ℝ)) (hz1 : -1 < z)
    (hz2 : z < 1 / 2) :
    hyp a b c z = (1 - z) ^ (-a) * hyp a (c - b) c (z / (z - 1))

theorem hasSum_hypCoeff_neg_one {A B C : ℝ} (h : 0 < C - A - B)
    (hC : ∀ n : ℕ, C ≠ -(n : ℝ)) :
    HasSum (fun n => hypCoeff A B C n * (-1) ^ n) (hyp A B C (-1))

theorem tendsto_hyp_nhdsWithin_neg_one ... :
    Tendsto (fun w => hyp A B C w) (nhdsWithin (-1) (Set.Ioi (-1))) (nhds (hyp A B C (-1)))
```
Target file: Pptc/Hypergeometric/Pfaff.lean (create only; do not edit existing files).
Plan: (B) first via summability + continuousOn_tsum; (A) check for existing Pfaff in
Mathlib/Contiguous/Euler, else coefficient route or ODE route.

## Log
- Read PLAN and Quadratic.lean. Starting orientation on Basic/Gauss/Contiguous/Euler.
- Found Mathlib `Ring.descPochhammer_smeval_add` (Pochhammer Chu-Vandermonde,
  Mathlib/RingTheory/Binomial.lean:490). With r = b-c, s = c+n-1 it gives exactly
  sum_k C(n,k) (-1)^k (c-b)_k (c+k)_{n-k} = (b)_n, i.e. the needed coefficient identity.
- Route chosen: (1) Chu-Vandermonde lemma via descPochhammer_smeval_add;
  (2) double series F(n,k) = hypCoeff a (c-b) c n * (-1)^n * (a+n)_k/k! * z^(n+k),
  absolutely summable for |z|<1/2 using |(a+n)_k| <= (|a|+n)_k and summability of
  hypCoeff a (c-b) c n * rho^n (from hasSum_hyp at rho<1);
  (3) fibre sums = hypCoeff a b c N z^N by (1); row sums give
  (1-z)^(-a) * hyp a (c-b) c (z/(z-1)); uniqueness gives Pfaff for |z|<1/2;
  (4) analytic continuation on (-1,1/2) as in Quadratic.
- `Ring.descPochhammer_smeval_add` found; first two lemmas of Pfaff.lean compile:
  `descPochhammer_smeval_sub_eq`, `sum_choose_neg_one_mul_pochhammer_div`.
- Gotchas: `Ring.descPochhammer_smeval_add` (not Polynomial), `Finset.Nat.sum_antidiagonal_eq_sum_range_succ`,
  `ascPochhammer_mul` (root namespace).
- Next: double series `pfaffFamily`, summability for |z|<1/2, fibre sums, small-disc Pfaff,
  analytic continuation, then (B).
- summable_pfaffFamily compiles (diagnostics success).
- row sums + fibre coefficient identity + finite fibre sum: all compile (diagnostics success).
- hyp_pfaff_small, hyp_pfaff, hasSum_hypCoeff_neg_one, tendsto_hyp_nhdsWithin_neg_one: all compile (diagnostics success, no warnings). Fixes: eball<->abs via Real.enorm_eq_ofReal_abs + ENNReal.ofReal_lt_one; Metric.isOpen_eball; Filter.Tendsto; Filter.mem_of_superset/Filter.inter_mem; hasSum at -1 via summable_hypCoeff_one + Summable.of_norm_bounded + hyp_eq_tsum_coeff.
- FINAL: lake env lean Pptc/Hypergeometric/Pfaff.lean exit 0, no output (no errors/warnings).
- Axioms (lean_verify) for Pconstructible.hyp_pfaff, Pconstructible.hasSum_hypCoeff_neg_one,
  Pconstructible.tendsto_hyp_nhdsWithin_neg_one: [propext, Classical.choice, Quot.sound], trust standard.
- Signatures:
  hyp_pfaff : ? {a b c z : R}, (? n, c ? -?n) ? -1 < z ? z < 1/2 ?
      hyp a b c z = (1 - z) ^ (-a) * hyp a (c - b) c (z / (z - 1))
  hasSum_hypCoeff_neg_one : ? {A B C : R}, 0 < C - A - B ? (? n, C ? -?n) ?
      HasSum (fun n => hypCoeff A B C n * (-1) ^ n) (hyp A B C (-1))
  tendsto_hyp_nhdsWithin_neg_one : ? {A B C : R}, 0 < C - A - B ? (? n, C ? -?n) ?
      Filter.Tendsto (fun w : R => hyp A B C w) (??[Set.Ioi (-1)] (-1)) (?? (hyp A B C (-1)))
- Done. No other files touched; no git commit; no lake build.
