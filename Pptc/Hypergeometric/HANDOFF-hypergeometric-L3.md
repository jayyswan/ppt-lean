# HANDOFF — hypergeometric L3 (Contiguous.lean)

Target file: `Pptc/Hypergeometric/Contiguous.lean` (lake root `pptc/`).
Imports: `Pptc.Hypergeometric.Basic` + targeted Mathlib modules only.

## PRIMARY goal
```lean
theorem hyp_deriv {a b c : ℝ} (hc : ∀ n : ℕ, c ≠ -(n : ℝ))
    (hc1 : ∀ n : ℕ, c + 1 ≠ -(n : ℝ)) {z : ℝ} (hz : |z| < 1) :
    deriv (fun w => hyp a b c w) z = (a * b / c) * hyp (a + 1) (b + 1) (c + 1) z
```

## SECONDARY
Gauss contiguous three-term relations DLMF 15.5.10–15.5.16, coefficient-wise from
`hypCoeff_succ`, transferred with `hyp_eq_of_hasSum`; numeric check with `py`+mpmath.

## Plan
1. HasFPowerSeriesOnBall for `hyp a b c` at 0 (radius from `ordinaryHypergeometricSeries`).
2. `fderiv`/`deriv` -> derivative series `∑ (n+1) hypCoeff(n+1) z^n`.
3. Coefficient identity `(n+1) hypCoeff a b c (n+1) = (a b / c) hypCoeff (a+1)(b+1)(c+1) n`.
4. `hyp_deriv`. Then relations.

## Log
- [start] read AGENTS.md, plan, Basic.lean. Handoff created.
- [step] fetched DLMF 15.5 (exact forms of 15.5.11-15.5.18, 15.5.16_5).
- [step] API found: `FormalMultilinearSeries.hasFPowerSeriesOnBall`,
  `HasFPowerSeriesOnBall.fderiv`, `FormalMultilinearSeries.derivSeries_apply_diag`,
  `derivSeries_coeff_one`, `apply_eq_pow_smul_coeff`, `ContinuousLinearMap.apply ℝ ℝ 1`,
  `HasSum.map`, `HasSum.congr_fun`, `HasSum.mul_left`. `deriv f x` is def `fderiv ℝ f x 1`.
- [step] ascPochhammer_succ_left: (a)_{n+1}.eval a = a * (a+1)_n (via eval_comp).
- [step] PRIMARY DONE: `ascPochhammer_succ_eval_left`, `hypCoeff_succ_mul`,
  `one_le_hypergeometric_radius`, `hasSum_deriv_hyp`, `hyp_deriv` all elaborate clean
  (lean_diagnostic_messages success:true).
  Key: `HasSum.map L hL` needs continuity; `.congr_fun` wants reverse orientation.
- [next] add DLMF 15.5.12 (`hyp_contiguous_ab`) and 15.5.15 (`hyp_contiguous_c`).
- [step] numeric check (mpmath, dps=40), script `%TEMP%/hg_l3_check.py`: rel12, rel15 and
  15.5.1 residuals ≤ 5e-41 on 3 random parameter/argument triples.
- [step] relation 15.5.12 coefficient id is pure (`linear_combination`); its transfer uses
  `show (...) = (...) * z^n from by ring` then `rw [h, zero_mul]` (NOT `rw [← h]`, which
  loses the `z^n` factor).
- [step] relation 15.5.15 needs `(c)ₙ ≠ 0`, `(c-1)ₙ ≠ 0`; derived from `hc`/`hcm` via
  `ascPochhammer_eval_eq_zero_iff`. Coefficient id: `unfold; field_simp;
  linear_combination B*Cm*ha - A*B*hc'` with `mul_ascPochhammer_succ` / `mul_ascPochhammer_pred`.
- [step] added `hyp_comm` (via `ordinaryHypergeometricSeries_symm`) and its transpose
  `hyp_contiguous_ba`.
- [FINAL] `lake_check Pptc/Hypergeometric/Contiguous.lean` → OK, no errors or warnings.

## Declarations in Contiguous.lean (final)
- `ascPochhammer_succ_eval_left : (ascPochhammer ℝ (n+1)).eval a = a * (ascPochhammer ℝ n).eval (a+1)`
- `hypCoeff_succ_mul : ((n:ℝ)+1) * hypCoeff a b c (n+1) = a*b/c * hypCoeff (a+1) (b+1) (c+1) n`
- `one_le_hypergeometric_radius : 1 ≤ (ordinaryHypergeometricSeries ℝ a b c).radius`
- `hasSum_deriv_hyp : HasSum (fun n => ((n:ℝ)+1)*hypCoeff a b c (n+1)*z^n) (deriv (hyp a b c) z)`
- `hyp_deriv : deriv (hyp a b c) z = (a*b/c) * hyp (a+1) (b+1) (c+1) z`   [PRIMARY]
- `mul_ascPochhammer_succ : a * (ascPochhammer ℝ n).eval (a+1) = (a+n) * (ascPochhammer ℝ n).eval a`
- `hypCoeff_contiguous_ab`  + `hyp_contiguous_ab`  [DLMF 15.5.12]
- `mul_ascPochhammer_pred : (c-1)*(ascPochhammer ℝ n).eval c = (ascPochhammer ℝ n).eval (c-1)*(c+n-1)`
- `hypCoeff_contiguous_c` (with `(c)ₙ ≠ 0`, `(c-1)ₙ ≠ 0`) + `hyp_contiguous_c`  [DLMF 15.5.15]
- `hyp_comm` + `hyp_contiguous_ba`  [15.5.12 transposed]

## TODO (blockers: step budget, not mathematics)
- DLMF 15.5.11, 15.5.13, 15.5.14, 15.5.16, 15.5.16_5, 15.5.17, 15.5.18 need a power-series
  shift lemma `HasSum (fun n => g n * z^n) G → HasSum (fun n => (if n=0 then 0 else g (n-1)) * z^n) (G*z)`
  (buildable from `HasSum.mul_right` + `hasSum_nat_add_iff' 1`); not yet written.
- STRUCTURAL COROLLARY not stated: 15.5.12 + 15.5.15 alone do not isolate a single
  contiguous neighbour in the `ℚ(z)`-span of `F`, `F'`; DLMF 15.5.13 + 15.5.20 (or 15.5.14)
  are needed. Recorded as TODO rather than guessed.

## Log (continuing run)
- [start] re-read plan §4 H3, Contiguous.lean (332 lines), handoff. No `lake_check` per
  instruction; lean-lsp only.
- [plan] (1) z-shift HasSum lemma; (2) DLMF 15.5.11,13,14,16,16_5,17,18; (3) structural
  corollary isolating (a+1) and/or (c±1); (4) numeric checks with python scripts.
- [step] confirmed exact DLMF text via dlmf.nist.gov/15.5. 15.5.13:
  `(c−a−b)F + a(1−z)F(a+1,b) − (c−b)F(a,b−1)=0`.
  15.5.14: `c(a+(b−c)z)F − ac(1−z)F(a+1,b) + (c−a)(c−b)z F(a,b;c+1)=0`.
  15.5.20: `z(1−z)F' = (c−a)F(a−1,b)+(a−c+bz)F = (c−b)F(a,b−1)+(b−c+az)F`.
  15.5.21: `c(1−z)F' = (c−a)(c−b)F(a,b;c+1)+c(a+b−c)F`.
  Structural corollary route: 15.5.20 isolates F(a+1,b)/F(a,b+1) in span{F,F'}; 15.5.21 the c-shifts.
- [step] py+mpmath available (mpmath 1.3.0).


## Log (DLMF 15.5.21 run)
- [start] read Contiguous.lean + handoff. Target: DLMF 15.5.21 c(1-z)F' = (c-a)(c-b)F(a,b;c+1)+c(a+b-c)F.
- [plan] helper (c+1)_n relation; hypCoeff_succ_c helper; per-n coefficient id
  c*(n+1)c_{n+1}-c*n*c_n = (c-a)(c-b)d_n + c(a+b-c)c_n; transfer via
  hasSum_deriv_hyp + hasSum_mul_z_shift + hasSum_hyp.
- [note] task sketch said d_n=((c+n)/c)c_n but correct ratio is d_n=(c/(c+n))c_n
  (checked numerically); will use correct one.
- [step] added helpers mul_ascPochhammer_eval_add_one (c*(c+1)_n = (c)_n(c+n)) and
  hypCoeff_succ_c (hypCoeff a b (c+1) n = c/(c+n)*hypCoeff a b c n, needs
  c?0, (c)??0, c+n?0). NOTE ratio is c/(c+n), NOT (c+n)/c as the task sketch said.
- [step] coefficient id hypCoeff_contiguous_21: n=0 by unfold+simp+field_simp+ring;
  n=m+1 by hypCoeff_succ + hypCoeff_succ_c then field_simp; ring. No hc1 needed there.
- [step] hyp_contiguous_21 (DLMF 15.5.21): hderiv + hasSum_mul_z_shift + hasSum_hyp,
  combined into hL/hR, coefficientwise via hR.congr_fun; needed explicit HasSum type
  ascription on hR' (otherwise congr_fun's function metavariable blocks rw), and
  push_cast before ring in the z-shift succ case.
- [FINAL] lean_diagnostic_messages Pptc/Hypergeometric/Contiguous.lean ? success, 0 items
  (no errors, no warnings). lean_verify hyp_contiguous_21 ? propext, Classical.choice,
  Quot.sound only. No lake_check/lake build run (per instruction).

## Log (DLMF 15.5.20 run)
- [start] read handoff + Contiguous.lean. Target: hyp_contiguous_20_a and hyp_contiguous_20_b. lean-lsp only, no shell Lean.
