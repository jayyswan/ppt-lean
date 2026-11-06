# HANDOFF hypergeometric L9b — cubic & sextic Ramanujan-signature reductions

Target file: `pptc/Pptc/Hypergeometric/Signatures.lean` (extend; keep existing decls).
Plan: append after the existing quartic material, inside `namespace Pconstructible`,
`noncomputable section`.

## Exact goals

Definitions (all `p : ℝ`, plan: `0 ≤ p < 1`):

```
α p  = p^3 * (2+p) / (1+2*p)                       -- cubic argument  k²
β p  = 27 * p^2 * (1+p)^2 / (4 * (1+p+p^2)^3)      -- cubic / sextic signature argument z
γ p  = (1+p+p^2) / Real.sqrt (1+2*p)               -- cubic prefactor
x p  = p * (2+p) / (1+2*p)                         -- sextic argument k²
ξ p  = (27/4) * p^2 * (1+p)^2 / (1+p+p^2)^3        -- sextic signature argument
pre  = Real.sqrt (1+p+p^2) / Real.sqrt (1+2*p)     -- sextic prefactor (= (1-x+x²)^{1/4})
```

1. `hyp_one_third_two_thirds_Pconstructible (hp : PConstructible p) (hp0 : 0 ≤ p) (hp1 : p < 1)
   (hCubic : hyp (1/3) (2/3) 1 (β p) = γ p * hyp (1/2) (1/2) 1 (α p)) :
   PConstructible (hyp (1/3) (2/3) 1 (β p))`
2. `hyp_one_sixth_five_sixths_Pconstructible (hp) (hp0) (hp1)
   (hSextic : hyp (1/6) (5/6) 1 (ξ p) = pre * hyp (1/2) (1/2) 1 (x p)) :
   PConstructible (hyp (1/6) (5/6) 1 (ξ p))`
3. Optional special values at p=(√3-1)/2 (z=1/2).

## Side lemmas to prove

- `one_add_two_mul_pos`, `one_add_add_sq_pos` for `0 ≤ p`.
- `α_mem`: `0 ≤ α p < 1`; `β_mem`: `0 ≤ β p < 1`; `x_mem`: `0 ≤ x p < 1`; `ξ_mem`: `0 ≤ ξ p < 1`.
- `α_Pconstructible`, `β_Pconstructible`, `γ_Pconstructible`, `x_Pconstructible`,
  `ξ_Pconstructible`, `sexticPrefactor_Pconstructible` from `PConstructible p`.

## Plan

Define the six functions as `noncomputable def` (or local `let`s) so the statements are short,
prove the inequalities with `positivity`/`nlinarith`/`gcongr`, then build PConstructibility
via `pconstructible` + `sqrt_Pconstructible`, apply `hyp_half_half_one_Pconstructible`, rewrite.

## Progress log

- [start] read AGENTS.md, PLAN, R2 notes, Signatures.lean, Elliptic.lean. Created this file.
- Appended to Signatures.lean: defs `α β γ x ξ sexticPrefactor`; positivity
  `one_add_two_mul_pos`, `one_add_add_sq_pos`; bounds `α_nonneg/lt_one`, `β_nonneg/lt_one`,
  `x_nonneg/lt_one`, `ξ_nonneg/lt_one`, `abs_α_lt_one`, `abs_x_lt_one`;
  PConstructibility `α/β/γ/x/ξ/sexticPrefactor_Pconstructible` (tagged `@[pconstructible]`);
  main conditional theorems `hyp_one_third_two_thirds_Pconstructible`,
  `hyp_one_sixth_five_sixths_Pconstructible`.
- `lean_diagnostic_messages`: CLEAN (one earlier `rw [h]` -> `rw [← h]` fix).
- Line-length check (UTF-8 aware): all lines ≤ 100. No `sorry`/`axiom`.
- Target 3 ALSO DONE: `pHalf`; `sqrt_sqrt_eq_rpow_quarter`; `three_div_fourth_root_eq`;
  `sqrt_three_halves_div_sqrt_sqrt_three`; `β_pHalf`, `ξ_pHalf`, `x_pHalf`, `α_pHalf`,
  `γ_pHalf`, `sexticPrefactor_pHalf`; special-value theorems
  `hyp_one_third_two_thirds_half_of_reduction` (★) and
  `hyp_one_sixth_five_sixths_half_of_reduction` (★★), derived from the reduction hypothesis
  by `rw [...] at h`.
- Gotchas fixed: `Real.mul_rpow` has implicit exponent in this Mathlib (`rw [← Real.mul_rpow hx hy]`);
  `Real.rpow_mul` needs the Nat-cast exponent written as `((2:ℕ):ℝ)` to match.
- line-length (UTF-8) all ≤ 100; no sorry/admit/axiom.
- DONE: `lean_verify` on all four (cubic/sextic parametric + (★)/(★★) special-value) shows
  only `propext`, `Classical.choice`, `Quot.sound`. `lake_check` "OK - no errors or
  warnings". `lake build Pptc.Hypergeometric.Signatures` succeeded. No scratch files left.
