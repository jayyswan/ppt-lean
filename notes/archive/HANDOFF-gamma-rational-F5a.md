# HANDOFF: GammaRational/HalfShift.lean (F5a)

Goal:
```lean
def HalfProducts : Prop :=
  ∀ ρ : ℚ, 0 < ρ → ρ < 1 / 2 →
    PConstructible (Real.Gamma (ρ : ℝ) * Real.Gamma (1 / 2 - (ρ : ℝ)))

theorem Gamma_div_Gamma_add_half_Pconstructible (hΠ : HalfProducts) (x : ℚ) (hx : 0 < x) :
    PConstructible (Real.Gamma (x : ℝ) / Real.Gamma ((x : ℝ) + 1 / 2))

theorem Gamma_sq_div_Gamma_two_mul_Pconstructible (hΠ : HalfProducts) (x : ℚ) (hx : 0 < x) :
    PConstructible (Real.Gamma (x : ℝ) ^ 2 / Real.Gamma (2 * (x : ℝ)))
```

File: pptc/Pptc/GammaRational/HalfShift.lean (target decls, namespace Pconstructible)
Plan: half-shift by induction over 2x integer part; base ρ∈(0,1/2) via hΠ / reflection;
base x∈½ℤ via Gamma_intCast_div_two_Pconstructible; step H(x+1/2)=1/(x H(x)).
Doubling via Legendre duplication + dupFactor_Pconstructible.

## Log
- [start] read file skeleton, understand imports/namespace.
- [plan] helpers: half_shift_step, half_shift_base_Ioo, half_shift_halfInt, half_shift_iter;
  main via Int.floor/Int.fract decomposition x = m/2 + f/2; doubling via Legendre+dupFactor.
- [edit] wrote full proof attempt. Now checking diagnostics.
- [blocker+fix] `hΠ` does NOT lex in Lean 4.33 (uppercase Π/Σ are reserved tokens);
  verified with a scratch file (`example (hΠ : True)` errors). Used the escaped identifier
  `«hΠ»`, which names the binder EXACTLY `hΠ` -- statement unchanged. Scratch deleted.
- [diag] remaining errors: extra `ring` after `field_simp` closed goals (step, hfinal);
  base_Ioo linarith can't cast ℚ hypotheses to ℝ and field_simp left `1 = Γb*Γb⁻¹`;
  hfinal direction needs `.symm`. Fixing.
- [diag] clean: `success: true`, zero diagnostics (no errors, no warnings).
  Fixed ℚ->ℝ casts via `rw [show (1:ℝ)/2 = ((1/2:ℚ):ℝ) by norm_num]` + `exact_mod_cast`,
  and `rw [← Rat.cast_zero]` + `exact_mod_cast`. Base Ioo equality via
  `eq_comm`/`mul_comm` + `mul_div_mul_right`. hfinal via hdu then field_simp.
- [verify] `lean_verify` both theorems: axioms = propext, Classical.choice, Quot.sound only.
- [build] `lake build Pptc.GammaRational.HalfShift` succeeded (2868 jobs, 15s).
- [DONE] no sorry, no errors/warnings. Statements unchanged (binder displayed/escaped as
  `«hΠ»`, same name `hΠ`). Scratch file removed.

## Final structure (namespace Pconstructible)

Private helpers:
- `half_shift_step {y:ℚ} (hy:0<y) (h:P Γy/Γ(y+1/2)) : P Γ(y+1/2)/Γ(y+1)`
  via `PConstructible.div (1/y) h`, `Real.Gamma_add_one`, `field_simp`.
- `half_shift_base_Ioo («hΠ») (ρ) (0<ρ) (ρ<1/2) : P Γρ/Γ(ρ+1/2)`
  via `hΠ ρ`, reflection `Gamma_mul_Gamma_one_sub_Pconstructible` at `1/2-ρ`.
- `half_shift_halfInt (m:ℤ) : P Γ(m/2)/Γ(m/2+1/2)` via `Gamma_intCast_div_two_Pconstructible`.
- `half_shift_iter («hΠ») (ρ) (0<ρ) (ρ<1/2) : ∀ k, P Γ(ρ+k/2)/Γ(ρ+k/2+1/2)` by Nat induction.

`Gamma_div_Gamma_add_half_Pconstructible`: let q=2x, m=⌊q⌋, f=fract q; x = m/2 + f/2;
if f=0 use halfInt m, else ρ=f/2∈(0,1/2), m≥0, x=ρ+m.toNat/2, use half_shift_iter.
`Gamma_sq_div_Gamma_two_mul_Pconstructible`: `Γ(x)²/Γ(2x) = dupFactor x · H(x)` from
`Gamma_mul_Gamma_add_half'`, both factors P-constructible.
