# HANDOFF hypergeometric L8 — bcc/fcc Watson constants

Goal (Lean): add to `Pptc/Hypergeometric/Polya.lean`:
- `bccReturn3 : ℝ := Real.Gamma (1/4)^4 / (4 * Real.pi^3)` + PConstructible
- `bccReturnProb3 : ℝ := 1 - bccReturn3⁻¹` + PConstructible
- `fccReturn3 : ℝ := 9 * Real.Gamma (1/3)^6 / (2^(14/3:ℝ) * Real.pi^4)` + PConstructible
- `fccReturnProb3 : ℝ := 1 - fccReturn3⁻¹` + PConstructible
- (optional) `watsonI2 := 3 * Γ(1/3)^6 / (2^(14/3) π^4)` + PConstructible

## Log
- Created log. Next: read NOTES-hypergeometric-R3.md, overview B5/§5, Polya.lean, grep Gamma.lean.
- Read R3 note (corrected fcc = 9Γ(1/3)^6/(2^{14/3}π^4); I2 = 3.../factor 3), overview B5, Polya.lean.
- Gamma.lean: `Gamma_intCast_div_three_Pconstructible (n:ℤ)` @810, `Gamma_intCast_div_four_Pconstructible (n:ℤ)` @1074.
- `rpow_Pconstructible` exists (Pptc/Basic.lean). Applied both edits (docstring paragraph + new block before `end`).
- First diagnostics: bcc/fcc/watsonI2 Γ defs closed by `pconstructible`; the two `…ReturnProb3` defs failed (pconstructible couldn't see through the named `bccReturn3`/`fccReturn3`).
- Fixed probs with explicit `refine PConstructible.sub …; rw [inv_eq_one_div]; exact PConstructible.div …`.
- FINAL `lean_diagnostic_messages Pptc/Hypergeometric/Polya.lean`: success=true, items=[] (zero errors/warnings).
- `lean_verify fccReturnProb3_Pconstructible`: axioms = propext, Classical.choice, Quot.sound; warnings [].

## Final declarations (namespace Pconstructible, in Pptc/Hypergeometric/Polya.lean)
```
noncomputable def bccReturn3 : ℝ := Real.Gamma (1 / 4) ^ 4 / (4 * Real.pi ^ 3)
theorem bccReturn3_Pconstructible : PConstructible bccReturn3   -- unfold; pconstructible
noncomputable def bccReturnProb3 : ℝ := 1 - (bccReturn3)⁻¹
theorem bccReturnProb3_Pconstructible : PConstructible bccReturnProb3
noncomputable def watsonI2 : ℝ := 3 * Real.Gamma (1 / 3) ^ 6 / (2 ^ (14 / 3 : ℝ) * Real.pi ^ 4)
theorem watsonI2_Pconstructible : PConstructible watsonI2   -- unfold; pconstructible
noncomputable def fccReturn3 : ℝ := 9 * Real.Gamma (1 / 3) ^ 6 / (2 ^ (14 / 3 : ℝ) * Real.pi ^ 4)
theorem fccReturn3_Pconstructible : PConstructible fccReturn3   -- unfold; pconstructible
noncomputable def fccReturnProb3 : ℝ := 1 - (fccReturn3)⁻¹
theorem fccReturnProb3_Pconstructible : PConstructible fccReturnProb3
```
Prob proofs:
```
  unfold bccReturnProb3
  refine PConstructible.sub PConstructible.base_one ?_
  rw [inv_eq_one_div]
  exact PConstructible.div PConstructible.base_one bccReturn3_Pconstructible
```
(same shape for fcc). Module docstring paragraph added naming Watson/Glasser–Zucker. No existing decl changed. No `lake_check` run (resource constraint).
