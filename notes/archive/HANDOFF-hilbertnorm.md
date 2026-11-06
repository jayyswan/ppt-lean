# Handoff: norm characterization of Hilbert symbol

## Goal (Lean)
```
theorem hilbertSym_eq_one_iff_isNorm {k : Type*} [Field k] [Invertible (2 : k)]
    {a b : k} (ha : a ≠ 0) (hb : b ≠ 0) (hbsq : ¬ IsSquare b) :
    hilbertSym a b = 1 ↔ ∃ t : QuadraticAlgebra k b 0, a = QuadraticAlgebra.norm t
```
Target file: `Pptc/HasseMinkowski/HilbertSymbol/Norm.lean`, namespace `Pptc.HasseMinkowski`.

## Plan
1. Verify QuadraticAlgebra/norm shape in Mathlib 4.33.
2. Read Defs.lean hilbertSym + existing lemmas.
3. Prove (⇒) via witnesses, (⇐) from norm.

## Log
- [start] created log.
- Verified `QuadraticAlgebra` exists (`Mathlib.Algebra.QuadraticAlgebra.Basic`):
  `norm z = z.re^2 + b0*z.re*z.im - a0*z.im^2`; for `QuadraticAlgebra k b 0` = `x^2 - b*y^2`. `IsSquare a := ∃ r, a = r*r`.
- Read `hilbertSym` def; `hilbertSym_eq_one_of_sol` lives in heavy `Padic.lean`, so I prove a
  local `hilbertSym_eq_one_iff_sol` from the def instead.
- Wrote draft `Pptc/HasseMinkowski/HilbertSymbol/Norm.lean` (2 theorems).
- Key fix: `k` is only a `Field` (not ordered), so `linarith`/`nlinarith` fail; used
  `linear_combination` (ring-based) throughout. `field_simp` reduces the x≠0 and hbsq goals.
- LSP diagnostics: clean (success=true, no items). Both theorems proved, no `sorry`.
- TODO: lake_check + lean_verify.
- DONE. `lake_check Pptc/HasseMinkowski/HilbertSymbol/Norm.lean` -> OK, no errors/warnings.
  `lean_verify hilbertSym_eq_one_iff_isNorm` -> axioms exactly {propext, Classical.choice, Quot.sound}.

## Final file: Pptc/HasseMinkowski/HilbertSymbol/Norm.lean (75 lines, both theorems sorry-free)
- `hilbertSym_eq_one_iff_sol` (auxiliary): for nonzero a,b,
  `hilbertSym a b = 1 ↔ ∃ z x y, (z,x,y)≠0 ∧ z^2 - a*x^2 - b*y^2 = 0`.
- `hilbertSym_eq_one_iff_isNorm` (target):
  `hilbertSym a b = 1 ↔ ∃ t : QuadraticAlgebra k b 0, a = QuadraticAlgebra.norm t`.

Confirmed: QuadraticAlgebra (Mathlib.Algebra.QuadraticAlgebra.Basic) exists; constructor `mk`/`⟨x,y⟩`;
for `QuadraticAlgebra k b 0`, `norm_def z = z.re*z.re + 0*z.re*z.im - b*z.im*z.im = re^2 - b*im^2`.
`IsSquare a := ∃ r, a = r*r`.
Note: `[Invertible (2:k)]` is not actually used by the proof (statement holds char-free), but kept as specified.
