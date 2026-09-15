# Handoff: Hilbert symbol over R

Target file: `pptc/Pptc/HasseMinkowski/HilbertSymbol/Real.lean`, namespace `Pptc.HasseMinkowski`.

Goals:
1. `hilbertSym_real_eq {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
     hilbertSym a b = if 0 < a ∨ 0 < b then 1 else -1`
2. `hilbertSym_real_mul_left (a a' b : ℝ) :
     hilbertSym (a*a') b = hilbertSym a b * hilbertSym a' b`
3. `instance : HasBilinHilbertSym ℝ`

## Log
- start: read Defs.lean.
- wrote Real.lean with all three declarations.
- compile attempt 1: `pow_eq_zero` unknown; `push_neg` deprecated warning.
- fixed: `sq_eq_zero_iff.mp`, `simp only [not_or, not_lt]`; also `sq_eq_zero_iff` applies to `z^2`.
- lake_check: OK - no errors or warnings.
- lean_verify hilbertSym_real_eq + hilbertSym_real_mul_left: only propext/Classical.choice/Quot.sound. NO sorry.

## Final declarations (file Pptc/HasseMinkowski/HilbertSymbol/Real.lean)
- `Pptc.HasseMinkowski.hilbertSym_real_eq`
- `Pptc.HasseMinkowski.hilbertSym_real_mul_left`
- `instHasBilinHilbertSymReal : HasBilinHilbertSym ℝ`

