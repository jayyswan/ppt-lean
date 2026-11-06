# HANDOFF: RatSquares.lean

Goal: `Pptc/HasseMinkowski/RatSquares.lean`, namespace `Pptc.HasseMinkowski`.

Main target:
```
theorem Rat.isSquare_iff_even_padicValRat {q : ℚ} :
    IsSquare q ↔ 0 ≤ q ∧ ∀ p : ℕ, p.Prime → Even (padicValRat p q)
```

Companion:
```
theorem isSquare_of_nonneg_of_even_padicValRat {q : ℚ} (hq : 0 ≤ q)
    (h : ∀ p : ℕ, p.Prime → Even (padicValRat p q)) : IsSquare q
```

Plan: search Mathlib for Rat.isSquare_iff, padicValRat lemmas, Nat.factorization
square characterizations. Then implement.

## Log
- (start) created log.
- Recon: `Nat.isSquare_iff_even_factorization` does NOT exist in this toolchain
  (loogle v4.28 phantom). Proving it locally. `padicValNat_def` is root-level with
  `[Fact p.Prime]`; `padicValNat_def'` root-level takes `p ≠ 1`, `n ≠ 0`.
  `Int.even_coe_nat`, `even_neg`, `Nat.sq_mul_squarefree`,
  `Nat.factorization_eq_one_of_squarefree` all present.
- Wrote full draft: helper `isSquare_nat_iff_even_factorization`,
  `factorization_eq_zero_or_eq_zero_of_coprime`, `padicValRat_eq_factorization`,
  `even_padicValRat_of_isSquare`, `nonneg_of_isSquare`, main
  `Rat.isSquare_iff_even_padicValRat`, `isSquare_of_nonneg_of_even_padicValRat`.
  Now compiling.
- Compile fixes: `Finsupp.add_apply`/`Finsupp.smul_apply` (not `Pi.add_apply`);
  `Even.zero` (no `even_zero`); `(Int.even_coe_nat n).mp` (explicit `n`);
  replaced `haveI : Fact p.Prime` with explicit `(hp := Fact.mk hp)` arg to
  `padicValRat.mul` to avoid the `linter.style.haveILetI` warning.
- `lake_check Pptc/HasseMinkowski/RatSquares.lean` → OK - no errors or warnings.
- `lean_verify` on main + companion: axioms only propext, Classical.choice, Quot.sound.

## DONE — final declarations (all in namespace `Pptc.HasseMinkowski`)

Full names (relative naming: `Rat.` prefix nests under `Pptc.HasseMinkowski`):
- `Pptc.HasseMinkowski.isSquare_nat_iff_even_factorization`
    `{n : ℕ} : IsSquare n ↔ ∀ p, p.Prime → Even (n.factorization p)`
- `Pptc.HasseMinkowski.factorization_eq_zero_or_eq_zero_of_coprime`
    `{a b p} (hp : p.Prime) (hab : Nat.Coprime a b) :
       a.factorization p = 0 ∨ b.factorization p = 0`
- `Pptc.HasseMinkowski.padicValRat_eq_factorization`
    `{q : ℚ} (hq : q ≠ 0) {p} (hp : p.Prime) :
       padicValRat p q = (q.num.natAbs.factorization p : ℤ) - (q.den.factorization p : ℤ)`
- `Pptc.HasseMinkowski.even_padicValRat_of_isSquare`
    `(hq : IsSquare q) (p) (hp : p.Prime) : Even (padicValRat p q)`
- `Pptc.HasseMinkowski.nonneg_of_isSquare : IsSquare q → 0 ≤ q`
- `Pptc.HasseMinkowski.Rat.isSquare_iff_even_padicValRat`  (MAIN, exact target)
    `{q : ℚ} : IsSquare q ↔ 0 ≤ q ∧ ∀ p, p.Prime → Even (padicValRat p q)`
- `Pptc.HasseMinkowski.isSquare_of_nonneg_of_even_padicValRat`  (companion)
    `(hq : 0 ≤ q) (h : ∀ p, p.Prime → Even (padicValRat p q)) : IsSquare q`

Note: the main theorem's full name is `Pptc.HasseMinkowski.Rat.isSquare_iff_even_padicValRat`
(Lean treats the `Rat.` prefix as relative to the current namespace). Referenced from
inside the namespace as `Rat.isSquare_iff_even_padicValRat`.
