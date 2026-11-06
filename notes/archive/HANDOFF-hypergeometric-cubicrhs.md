# HANDOFF: cubicOp_rhs

Target file: `Pptc/Hypergeometric/CubicRHS.lean` (new)
Goal:
```lean
theorem cubicOp_rhs :
    cubicOp (gammaSeries
      * PowerSeries.subst alphaSeries (hypSeries (1 / 2) (1 / 2) 1)) = 0
```
Plan: use `hypSeries_subst_ode` for `hY`; expand `cubicOp (G*Y) = d Y'' + e Y' + f Y`;
prove `a*e = d*b`, `a*f = d*c`; conclude `a * cubicOp(G*Y) = d * hY = 0`, then
`mul_eq_zero` with `a ≠ 0` (order 5).

- [start] created log, orienting.
- Wolfram: `a*e-d*b=0`, `a*f-d*c=0` confirmed exactly. Key extra find:
  `a/d = b/e = c/f` (operators proportional). Also `e/d = b/a`.
- `field_simp` makes NO progress on `PowerSeries ℝ` (tested). But it DOES work in
  `FractionRing (PowerSeries ℝ)` (K), with injectivity transfer via
  `IsFractionRing.injective`. Plan: prove rational identities in K, transfer back.
- Also: g cancels; reduce to ẽ := 2P2(h1/u) + P1 v, f̃ := P2(3v/u²)+P1(h1/u)+P0 v,
  d̃ := P2 v with h1 = 3X(1+X); prove `a*ẽ = d̃*b`, `a*f̃ = d̃*c` (no g).
- Relations: G' = h1 G/(v u), G'' = 3G/u². A=PA/u, B=N/E; formulas needed for
  A',A'',B',B'' by differentiating alphaSeries_mul, betaSeries_mul.
- All defs + derivative lemmas (deriv_vC/uC/nC/2nC/eC/2eC, alpha/beta 1st+2nd,
  gSeries/gammaSeries incl. G''*uC²=3G) COMPILE (diagnostics clean on
  Pptc/Hypergeometric/CubicRHS.lean as of this entry).
- Key mechanical gotchas: `simp only` needs specific `deriv_1`, `deriv_2`, ... lemmas
  for derivatives of numerals; `X^(k-1)` needs a `show (2-1:ℕ)=1` rewrite; use
  `linear_combination` (not bare `rw`) to close derivative identities.
- Remaining: p2C/p1C/p0C/aC/bC/cC/dT/eT/fT defs; he_lin/hd_lin/hf_lin; K identities
  `aC*eT=dT*bC`, `aC*fT=dT*cC` via FractionRing+field_simp+ring; aC≠0; final
  `cubicOp_rhs` assembly.
