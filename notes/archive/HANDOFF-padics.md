# HANDOFF: port WiN7 `Padics/Squares.lean` → `Pptc/HasseMinkowski/Padics/Squares.lean`

Goal (Lean syntax):
```
lemma Padic.isSquare_of_dist_one_lt_one (p : ℕ) [Fact (Nat.Prime p)] (hp : p ≠ 2)
    {x : ℚ_[p]} (hx : dist x 1 < 1) : IsSquare x
lemma Padic.isSquare_of_dist_one_lt_pow {x : ℚ_[2]} (hx : dist x 1 < 2 ^ (-(2:ℤ))) : IsSquare x
lemma Padic.exists_pow_isSquare_of_dist_one_lt (p) [Fact (Nat.Prime p)] :
    ∃ n, ∀ x : ℚ_[p], dist x 1 < p ^ (-(n:ℤ)) → IsSquare x
lemma Padic.isOpen_squares_sdiff_zero : IsOpen ({x : ℚ_[p] | IsSquare x} \ {0})
def   Padic.unitSquares : OpenSubgroup ℚ_[p]ˣ
```
Plus helpers: `PadicInt.isSquare_of_zmod`, `PadicInt.isSquare_of_zmodPow`,
`PadicInt.p_dvd_iff_toZMod_eq_zero`, `PadicInt.pow_p_dvd_iff_toZModPow_eq_zero`.

Plan: bottom-up; put all helpers in Squares.lean; lake_check clean, no sorry.

## Log

- Reference doc lacks a `Squares.lean` section; fetched upstream source via raw.githubusercontent.
- Reference does contain bodies for `isSquare_of_zmod` / `isSquare_of_zmodPow`.
- Fetched upstream `Padics/Lemmas.lean` for bodies of `p_dvd_iff_toZMod_eq_zero`,
  `pow_p_dvd_iff_toZModPow_eq_zero` (reference doc had statements only).
- Wrote `Pptc/HasseMinkowski/Padics/Squares.lean` (namespace PadicInt + Padic) with all
  helpers in the same file; plain imports, no `module`.
- `lake_check Pptc/HasseMinkowski/Padics/Squares.lean` → OK, no errors or warnings. NO sorry.
- `lean_verify` on `Padic.unitSquares` and `PadicInt.isSquare_of_zmod`: axioms
  `propext, Classical.choice, Quot.sound` only.
- DONE. Declarations: PadicInt.p_dvd_iff_toZMod_eq_zero, PadicInt.pow_p_dvd_iff_toZModPow_eq_zero,
  PadicInt.isSquare_of_zmod, PadicInt.isSquare_of_zmodPow,
  Padic.isSquare_of_dist_one_lt_one, Padic.isSquare_of_dist_one_lt_pow,
  Padic.exists_pow_isSquare_of_dist_one_lt, Padic.isOpen_squares_sdiff_zero, Padic.unitSquares.
