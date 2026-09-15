# HANDOFF: Pptc/HasseMinkowski/Prod.lean

Goal: port orthogonal-sum / base-change infra from WiN7 HassePrinciple/QuadraticForm/Basic.lean.
Target file: `Pptc/HasseMinkowski/Prod.lean`, namespace `Pptc.HasseMinkowski`.

Priority list:
1. `baseChange_prod`
2. `baseChange_prod_neg`
3. `weightedSumSquares_discr`, `baseChange_discr`
4. `nondegenerate_baseChange`
5. `QuadraticMap.Equivalent.nondegenerate` / `.nondegenerate_iff`
6. `mul_unit_isotropic_iff`, `weightedSumSquares_mul_squares_equivalent`
7. `prod_isotropic_iff` (skip if too hard)

## Log (round 1)
- [start] created handoff; about to read local files + fetch WiN7 reference.
- Recon: Mathlib 4.33 has `baseChange_ext` (top-level, no namespace), `QuadraticMap.prod`,
  `weightedSumSquares`, `QuadraticForm.discr`, `Nondegenerate` (radical=⊥ + rank cond),
  `nondegenerate_iff_radical_eq_bot`, `IsometryEquiv.map_radical`, `Equivalent = Nonempty`.
  Missing: `QuadraticForm.Equivalent`, `baseChange_compl₁₂`, `prodRight_fst/snd`,
  `weightedSumSquares_toMatrix`, `baseChange_toMatrix/discr`, `nondegenerate_iff_discr_ne_zero`.
- PROVED in Prod.lean (lake diagnostics clean): `baseChange_prod` (via prodRight + baseChange_ext),
  `baseChange_neg`, `baseChange_prod_neg`, `QuadraticMap.Equivalent.nondegenerate`,
  `QuadraticMap.Equivalent.nondegenerate_iff` (simpler than WiN7: use `e.map_radical` directly),
  `mul_unit_isotropic_iff`, `weightedSumSquares_mul_squares_equivalent`.
- Note: import `Pptc.HasseMinkowski.Basic` needed for `Isotropic`.
- TODO next: item 3 (weightedSumSquares_discr / baseChange_discr), item 4
  (nondegenerate_baseChange). Item 7 (prod_isotropic_iff) likely skip (WiN7 sorry).

## Log (round 2 - new task)
Task: (1) `nondegenerate_iff_discr_ne_zero`, (2) `nondegenerate_baseChange`,
(3) `prod_isotropic_iff` optional.
Note: file already contains baseChange_toMatrix/discr + weightedSumSquares_toMatrix/discr
(handoff round-1 TODO list is stale).
- [start] created log.
- File's `baseChange_toMatrix`/`baseChange_discr`/`weightedSumSquares_*` already present & clean.
- PROVED `nondegenerate_iff_discr_ne_zero`: route works.
  `rw [← QuadraticMap.nondegenerate_associated_iff, QuadraticForm.discr,
   QuadraticForm.toMatrix]; exact LinearMap.nondegenerate_iff_det_ne_zero b`.
- PROVED `nondegenerate_baseChange`. NOTE added hypotheses vs caller's sketch:
  `[IsDomain A] [Invertible (2:A)] [FaithfulSMul R A] [Finite ι]` (and section has
  `[IsDomain R]`). Rationale: item 1 over A needs `IsDomain A` + `Invertible (2:A)`;
  `[Nontrivial A]`/`[IsDomain A]` alone do NOT make `algebraMap R A` injective for general
  domain R (ℤ→𝔽_p), so we require `FaithfulSMul R A` (⇒ `FaithfulSMul.algebraMap_injective`).
  Used `[Finite ι]` + `Fintype.ofFinite` to dodge unused-Fintype-in-type linter.
  Proof: `rw [nondegenerate_iff_discr_ne_zero (b.baseChange A), baseChange_discr]`, then
  `(FaithfulSMul.algebraMap_eq_zero_iff R A).mp h` + `nondegenerate_iff_discr_ne_zero b Q`.
- DIAGNOSTICS for Prod.lean after these two: [] (clean).
- `lake_check Pptc/HasseMinkowski/Prod.lean` => "OK - no errors or warnings."
- SKIPPED item 3 `prod_isotropic_iff`. It is FALSE as stated (not just hard).
  * `(Q₁.prod Q₂) (x,y) = Q₁ x + Q₂ y` (Mathlib `QuadraticMap.prod`).
  * `represents Q a := ∃ x, x ≠ 0 ∧ Q x = a` (nonzero witness, Basic.lean), and
    `Isotropic Q := ∃ x, x ≠ 0 ∧ Q x = 0`.
  * Backward (RHS -> LHS) is trivially true: (x,y) with x,y ≠ 0 gives value 0, (x,y) ≠ 0.
  * Forward fails: an isotropic vector may be `(0, y)` with `y ≠ 0`, so `Q₂ y = 0`. Then the
    only compatible `a` from that vector is `a = 0`, requiring `Q₁` to represent 0, i.e. `Q₁`
    isotropic, which nondegeneracy does not give. E.g. over ℝ, `M₁ = ℝ` with `Q₁ = x²`,
    `M₂ = ℝ²` with `Q₂ = y₁² - y₂²`: `Q₁, Q₂` nondegenerate, `(0,(1,1))` isotropic in the sum,
    but there is also an actual RHS witness (`a = 1`), so a sharper counterexample is the zero
    module: `M₁ = 0`, `M₂ = ℝ²`, `Q₁ = 0`, `Q₂ = y₁² - y₂²`. Both nondegenerate; `(0,(1,1))`
    is isotropic in the sum, while `Q₁.represents a` is never true (no nonzero vector in 0) —
    so RHS is false. Over general rings it also fails without universality of the isotropic
    factor (nondeg + isotropic over ℝ/fields yields universality only via Witt extension).
  * A CORRECT, equally cheap statement (no nondegeneracy needed) is
    `(Q₁.prod Q₂).Isotropic ↔ Q₁.Isotropic ∨ Q₂.Isotropic ∨
       ∃ a, a ≠ 0 ∧ Q₁.represents a ∧ Q₂.represents (-a)`
    (forward: split on x = 0 / y = 0 / both nonzero; backward: use `(x,0)`, `(0,y)`, `(x,y)`).
    Not added since it is outside the requested deliverable.
- FINAL: declarations added: `Pptc.HasseMinkowski.nondegenerate_iff_discr_ne_zero`,
  `Pptc.HasseMinkowski.nondegenerate_baseChange`. Dropped: `prod_isotropic_iff` (false).

## Log (round 3 — new task: prod_isotropic_iff + iso_prod_neg)
Goal (Lean):
```
theorem prod_isotropic_iff (h₁ : Q₁.Nondegenerate) (h₂ : Q₂.Nondegenerate) :
  (Q₁.prod Q₂).Isotropic ↔
    Q₁.Isotropic ∨ Q₂.Isotropic ∨ ∃ a : R, a ≠ 0 ∧ Q₁.represents a ∧ Q₂.represents (-a)
theorem iso_prod_neg ... (h : (Q₁.prod (-Q₂)).Isotropic) : ∃ a ≠ 0, Q₁.rep a ∧ Q₂.rep a
```
Target: append to `Pptc/HasseMinkowski/Prod.lean`, ns `Pptc.HasseMinkowski`.
Plan: (1) prove corrected criterion directly (no nondeg needed). (2) Over a *field* prove
universality `nondeg + isotropic → represents everything`, then `iso_prod_neg` with the
`V₁,V₂` nontrivial hypotheses (the zero-module cases are genuine counterexamples otherwise).
- [start] read Prod.lean, Basic.lean, HANDOFF-prod.md; recon Mathlib polarBilin API.
- [part1] `prod_isotropic_iff` proof drafted; testing whether unused `h₁ h₂` warn.
- [part1] DECISION: dropped unused `h₁ h₂` (would be linter warnings); statement is the
  unconditional corrected criterion from HANDOFF-prod round-2 note. Placed in a new section.
