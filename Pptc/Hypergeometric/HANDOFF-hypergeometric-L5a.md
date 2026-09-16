# HANDOFF hypergeometric L5a (Graphs.lean)

Target file: `Pptc/Hypergeometric/Graphs.lean` (namespace `Pconstructible`).

Goal (V4, general form):
`∫₀^X √(1 + b² x^m) dx = X * hyp (-(1/2)) (1/m) (1 + 1/m) (-(b² X^m))`, m>0, |b²X^m|<1.
Corollaries: `integral_sqrt_one_add_sq_mul_pow` (n case, m = 2n-2, b = n) and
`arcLengthOf_graph_pow`.

Plan: expand `√(1+u) = ∑ₖ Ring.choose (1/2) k uᵏ` (Binomial), integrate termwise on `0..X`
using the interval `hasSum_integral_of_dominated_convergence` with geometric bound
`|Ring.choose(1/2,k)| * |b²X^m|^k`; match `Ring.choose(1/2,k)/(mk+1) = (-1)^k hypCoeff k`.

## Log
- [start] read AGENTS.md, plan §2/§4, Basic.lean L1 API, Defs.lean speed/arcLengthOf.
- [info] `Real.one_add_rpow_hasFPowerSeriesOnBall_zero` uses `binomialSeries ℝ a = ofScalars ℝ (Ring.choose a ·)`; `@[simp] binomialSeries_apply` gives `Ring.choose a n * u^n`.
- [info] `integral_pow` is root-namespaced; `deriv_pow_field` in Deriv/Pow; bound series via `(hasSum_sqrt_one_add hRlt).summable.abs`.
- [info] coeff ids: `(ascPochhammer ℝ k).eval (-1/2)/k! = (-1)^k Ring.choose (1/2) k` (via `ascPochhammer_eval_neg_eq_descPochhammer` + `descPochhammer_eval_eq_ascPochhammer` + `choose_eq_smul`); `(1/m)_k/(1+1/m)_k = 1/(mk+1)` by induction.
- [plan] Graphs.lean: hasSum_sqrt_one_add, two coeff lemmas, hypCoeff lemma, integral_sqrt_one_add_sq_mul_pow (dominated convergence), nat corollary, arcLengthOf_graph_pow (+eq hyp).
- [info] pitfalls: `ascPochhammer_eval_neg_eq_descPochhammer` / `descPochhammer_eval_eq_ascPochhammer` take `R` EXPLICITLY (section has `variable (R : Type u) [Ring R]`), so call as `... ℝ (1/2) k`.
- [done] all 8 declarations elaborate; `lean_diagnostic_messages` clean (success, 0 items).
- [note] `integral_sqrt_one_add_sq_pow_of_nat` / `arcLengthOf_graph_pow_eq_hyp` state the exponent param as `1 / ((2*n-2 : ℕ) : ℝ)` (the nat cast, = `1/(2n-2)` as reals); writing `1/(2*n-2)` would elaborate as ℝ-subtraction `2*↑n-2` and not definitionally match the general theorem.
- [DONE] `lake_check Pptc/Hypergeometric/Graphs.lean` => "OK - no errors or warnings."
- [DONE] `lean_verify` on `integral_sqrt_one_add_sq_mul_pow` and `arcLengthOf_graph_pow_eq_hyp` => axioms `{propext, Classical.choice, Quot.sound}` only. No sorry/axiom in file.
- [DONE] Landed declarations (all in `Pconstructible`):
  `hasSum_sqrt_one_add {u} (|u|<1) : HasSum (fun k => Ring.choose (1/2) k * u^k) (√(1+u))`
  `ring_choose_half`, `ascPochhammer_neg_half_div_factorial`, `ascPochhammer_one_div_ratio`, `hypCoeff_neg_half_one_div_m`
  `integral_sqrt_one_add_sq_mul_pow {m} (0<m) {b X} (0≤X) (|b²Xᵐ|<1) : ∫₀^X √(1+b²xᵐ) = X*hyp (-(1/2)) (1/m) (1+1/m) (-(b²Xᵐ))`
  `integral_sqrt_one_add_sq_pow_of_nat {n} (2≤n) {X} (0≤X) (|n²X^{2n-2}|<1)`
  `speed_graph_pow`, `arcLengthOf_graph_pow`, `arcLengthOf_graph_pow_eq_hyp`.
- [hyp] `hsmall : |b²Xᵐ| < 1` is needed because the proof's dominating bound is the geometric
  series `∑|C(1/2,k)|Rᵏ` for `|b²Xᵐ| < R < 1`; at the endpoint `= 1` no such `R` exists.
  The identity is presumably still true there but needs a separate limiting argument (L5b /
  H6 up to `w = -1` will meet this). Documented in the theorem docstring.

## Extension: affine (general-`b`) family, same file

Goal: `y = (b/n) xⁿ` is the `scale_y (b/n)` image of `poly_graph (Xⁿ)`, so its arc length
realizes the general-`b` V4 family. Verify ONLY via lean-lsp MCP (no lake_check/build).

- [start] read plan H6/§4, Graphs.lean, Basic.lean `parabolaArc_Pconstructible`, Defs closure ops.
- [info] derivative `(b/n)*x^n` is `b*x^(n-1)` via `deriv_const_mul_field` + `deriv_pow_field`;
  needed `← mul_assoc` to pair `(b/n)*n`.
- [NOTE / correction] deliverable (2) as stated (`{n} (2 ≤ n)`) is NOT provable: `poly_graph`
  caps `natDegree ≤ 6` and `(X^n).natDegree = n`, so the statement needs `hn6 : n ≤ 6`.
  Added that hypothesis (matches H6's n ∈ {2..6}).
- [done] `speed_scaledGraph_pow {n} (2≤n) (b t) : speed (fun x => (x,(b/n)*x^n)) t
  = √(1 + b² t^(2n-2))`.
- [done] `arcLengthOf_scaledGraph_pow {n} (2≤n) {b X} (0≤X) (|b²X^{2n-2}|<1) :
  arcLengthOf (fun t => (t,(b/n)*t^n)) 0 X
    = X * hyp (-(1/2)) (1/((2n-2:ℕ):ℝ)) (1+1/((2n-2:ℕ):ℝ)) (-(b² X^{2n-2}))`.
- [done] `@[pconstructible_cond] hyp_neg_half_arcLength_Pconstructible {n} (2≤n) (n≤6)
  {b X} (P b) (P X) (0<X) (|b²X^{2n-2}|<1) : PConstructible (hyp ...)`.
  Route: `scale_y (b/n) (poly_graph (X^n))` + `PConstructible.arc_length`, then `/ X`.
- [done] `lean_diagnostic_messages Pptc/Hypergeometric/Graphs.lean` => success, 0 items;
  `lean_verify` on both => axioms {propext, Classical.choice, Quot.sound}.
- [bonus done, with one added hypothesis] `speed_affineImageGraph_pow` and
  `arcLengthOf_affineImageGraph_pow_Pconstructible {n} (2≤n) (n≤6) {a b c d e f X}
  (P ...) (0≤X) (hinj : γ Injective on Icc 0 X) : PConstructible (arcLengthOf γ 0 X)`.
  Curve = `translate_y (translate_x (linearMap a b c d '' poly_graph)) f e`.
- [BLOCKER / deviation] the bonus was requested for *all* PConstructible coefficients, but
  `PConstructible.arc_length` needs the tracing injective on `[0,X]`, and an affine image can
  fail injectivity (e.g. `a=d=e=f=0`, `b=c=1`, n even). So `hinj` was added explicitly; it is
  automatic when `a*d - b*c ≠ 0` (the determinant argument is in the `/-! ###` note).
- [note] shear note in `/-! ###`: axis scaling (`b=c=0`, `e=f=0`) is the (1)/(2) family with
  effective coefficient `d/a`; a shear makes the radicand a quadratic in `tⁿ⁻¹`, i.e. a
  hyperelliptic integral, not ₂F₁.

### Final state of Graphs.lean (this extension)
`speed_scaledGraph_pow`, `arcLengthOf_scaledGraph_pow`,
`hyp_neg_half_arcLength_Pconstructible`, `speed_affineImageGraph_pow`,
`arcLengthOf_affineImageGraph_pow_Pconstructible`. All in namespace `Pconstructible`, no
`sorry`/`axiom`, diagnostics clean. (1) and (2) landed exactly as specified except for the
necessary `hn6 : n ≤ 6`; (3) landed with the necessary `hinj`.
