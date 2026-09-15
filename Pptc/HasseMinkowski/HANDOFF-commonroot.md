# HANDOFF: CommonRoot.lean (ternary Hasse-Minkowski analytic core)

Target file: `Pptc/HasseMinkowski/Padics/CommonRoot.lean`, namespace `Pptc.HasseMinkowski` (or `Padic`).
No `sorry`. Do not edit other files.

Declarations to port (WiN7 `HassePrinciple/Padics/Lemmas.lean`):
- `exists_padicInt_solution`
- `lift_solutions_to_int_first`
- `exists_nontrivial_zero`
- `common_root_tfae`
- `multivariable_hensel` / `multivariable_hensel'`

## Plan
1. Fetch upstream file; inspect exactly which auxiliary lemmas (e.g. `Padic.norm_mul_pow_neg_valuation_eq_one`,
   `Padic.unitPart`, `p2`, `norm_natCast_eq_one_iff`, etc.) are needed and whether they are in scope.
2. Determine which helper decls already exist in the local Pptc tree (search) so CommonRoot.lean can be self-contained.
3. Prove bottom-up: helpers first, then `exists_padicInt_solution` / `lift_solutions_to_int_first`,
   `exists_nontrivial_zero`, `common_root_tfae`, `multivariable_hensel`/`multivariable_hensel'`.
4. `lake_check` after each meaningful step.

## Log
- [start] Created log. Reading reference + upstream.
- Fetched upstream `Padics/Lemmas.lean`; most target decls are `sorry` there.
- PROVED `Padic.exists_padicInt_solution` in scratch (`Pptc/ScratchCommonRoot.lean`),
  lake_check OK. Proof: scale all coords by `p^(-w.valuation)` where `w` is a coordinate of
  maximal norm; then all lie in `ℤ_[p]` and `w` becomes a unit.
- `lift_solutions_to_int_first` has the exact same statement → alias.
- NOTE: `exists_nontrivial_zero` is FALSE as stated: `v : ℚ_[p]ˣ` may have norm `p` (e.g. `v=p`).
  Then `z'² = p x'² + v y'²` forces val(z')≥1, so `z'` cannot be a unit. Counterexample
  p=2, v=2: z=2,x=1,y=1 solves `z²-2x²-2y²=0`. So omit + document.
- `PadicInt.hensels_lemma` only gives `‖t‖ < p^{-k}` (not the sharper `p^{-n+k}`), so the
  valuation/norm targets need extra work; assessing feasibility.

## Round 2 (this worker)
- Created `Pptc/HasseMinkowski/Padics/CommonRoot.lean` with imports PadicVal/ PadicNumbers/
  PadicIntegers/ RingHoms. Helpers `norm_mul_pow_neg_valuation_le_one`,
  `norm_mul_pow_neg_valuation_eq_one`, `scaled_solution`.
- `exists_padicInt_solution` + `lift_solutions_to_int_first` compile clean (diagnostics empty).
- Next: corrected `exists_nontrivial_zero` with hypothesis `‖(v:ℚ_[p])‖ = 1`; conclusion both
  z',y' units. Strategy: from `exists_padicInt_solution` get a unit coord; prove
  `IsUnit Z → IsUnit Y` and `IsUnit Y → IsUnit Z` by ultrametric norm contradiction, then
  case on `hu`.
- Lemma names needed: `PadicInt.isUnit_iff`, `PadicInt.mkUnits`, `IsUnit.unit_spec`,
  `PadicInt.norm_lt_one_iff_dvd`, `PadicInt.norm_le_pow_iff_mem_span_pow`,
  `PadicInt.maximalIdeal_eq_span_p`.

## Round 2 result — DONE (targets 1–3), target 4 not attempted

File: `Pptc/HasseMinkowski/Padics/CommonRoot.lean`, namespace `Padic`.
`lake_check` → `OK - no errors or warnings`. No `sorry`/`admit`/`axiom`.
`lean_verify` on `Padic.exists_padicInt_solution` and `Padic.exists_nontrivial_zero`:
axioms `propext, Classical.choice, Quot.sound` only.

Compiled declarations:
- `Padic.exists_padicInt_solution` — scale by `p ^ (-(w.valuation))`, `w` a coordinate of
  maximal norm (`m := max ‖x‖ (max ‖y‖ ‖z‖)`), case on which coordinate attains `m`.
  Private helpers: `norm_mul_pow_neg_valuation_le_one`, `norm_mul_pow_neg_valuation_eq_one`,
  `scaled_solution`.
- `Padic.lift_solutions_to_int_first` — one-line alias (same statement).
- `Padic.exists_nontrivial_zero` — CORRECTED: adds hypothesis `(hv : ‖(v:ℚ_[p])‖ = 1)`;
  conclusion is the integral solution whose `z` and `y` coordinates are units.
  Proof: from `exists_padicInt_solution` get a triple with `IsUnit Z ∨ IsUnit Y ∨ IsUnit X`;
  prove `IsUnit Z → IsUnit Y` and `IsUnit Y → IsUnit Z` by an ultrametric-norm contradiction
  using `Padic.nonarchimedean` and the sharper `‖nonunit‖ ≤ p⁻²` (helper
  `norm_sq_coe_le_pow_neg_two_of_not_isUnit`); in the `IsUnit X` case derive `IsUnit Z ∨ IsUnit Y`
  then finish. `hZ.unit`/`hY.unit` (`IsUnit.unit`, `IsUnit.unit_spec`) package the units.
  Other helpers: `norm_coe_le_pow_neg_one_of_not_isUnit`, `norm_coe_eq_one_of_isUnit`,
  `norm_coe_le_one`, `p_zpow_neg_lt_one`, `p_zpow_neg_two_lt_neg_one`.

## Target 4 (`multivariable_hensel` / `common_root_tfae`) — NOT included

Not attempted in this round; prior round's blockers stand:
- Mathlib's `PadicInt.hensels_lemma` only gives the weak root-distance bound `‖t‖ < p ^ (-k)`,
  not the sharp Newton bound `p ^ (-n + k)` needed for Serre's multivariable Hensel; the sharp
  version is `private` in Mathlib. A port must re-derive it.
- `common_root_tfae`'s `(3) ⟹ (2)` direction needs a König/compactness argument (inverse limit of
  finite solution sets); not available as a ready lemma.
Decided NOT to add unfinished/`sorry`-ing statements. If picked up again, start from the
`multivariable_hensel` statement in the upstream file and plan for the sharp Hensel bound first.

