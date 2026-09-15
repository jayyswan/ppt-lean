# Handoff — Workstream A.1 part 3: hilbertSym_padic_two_mul_left

## Goal (Lean)
```lean
theorem hilbertSym_padic_two_mul_left (a a' b : ℚ_[2]) :
    hilbertSym (a * a') b = hilbertSym a b * hilbertSym a' b

instance : HasBilinHilbertSym ℚ_[2] :=
  ⟨fun _ _ _ => hilbertSym_padic_two_mul_left _ _ _⟩
```

Target file: `Pptc/HasseMinkowski/HilbertSymbol/Two.lean` (append before `end Pptc.HasseMinkowski`).

## Plan
Mirror `hilbertSym_padic_odd_mul_left` in `Padic.lean` ~915-934.
Use closed formula `hilbertSym_padic_two_eq`, valuation_mul, unit multiplicativity,
then eps/omg homomorphism lemmas via ZMod 8 decide checks.

## Log
- [start] created log.
- [done] Appended to `Two.lean`: `twoAdicUnit_mul`, `even_eps_mul_sub_aux`,
  `even_omg_mul_sub_aux`, `even_eps_mul_sub`, `even_omg_mul_sub`,
  `hilbertSym_padic_two_mul_left`, `instance : HasBilinHilbertSym ℚ_[2]`.
  LSP diagnostics: clean. Instance needed implicit binders `fun {a a' b} => ...`.
- [next] lean_verify + lake_check.
