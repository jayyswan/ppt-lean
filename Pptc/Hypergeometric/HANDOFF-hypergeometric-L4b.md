# HANDOFF — hypergeometric-L4b (hyp_one_eq_Gamma')

TARGET: `Pptc/Hypergeometric/Gauss.lean`
```lean
theorem hyp_one_eq_Gamma' {a b c : ℝ} (h : 0 < c - a - b)
    (hca : ∀ n : ℕ, c - a ≠ -(n : ℝ)) (hcb : ∀ n : ℕ, c - b ≠ -(n : ℝ))
    (hc : ∀ n : ℕ, c ≠ -(n : ℝ)) :
    hyp a b c 1 = Real.Gamma c * Real.Gamma (c - a - b) / (Real.Gamma (c - a) * Real.Gamma (c - b))
```
Plan: a-down relation at z=1 from `hyp_shift_a_down` limit; a-up/b-up; diagonal
recurrences preserving c-a-b; D-invariance; reduce to original `hyp_one_eq_Gamma`.
Rule: no lake_check/lake build, lean-lsp only.

## Log
- created log. WARNING: this file already existed; `write` overwrote the previous content.
  Restating the plan from the task prompt; prior log content is unrecoverable.
- [read] Gauss.lean (target file, 594 lines), Contiguous.lean (contiguous relations),
  EllipticClass.lean (hyp_shift_a/b/a_down). Landed: tendsto_hyp_nhdsWithin_one,
  tendsto_one_sub_mul_deriv_hyp, hyp_one_recurrence (R_c), Gamma_ratio_succ,
  hyp_one_div_Gamma_succ, hyp_one_eq_Gamma (needs a,b>0,b<c).
- [plan] a-up at c+1 from limit of hyp_shift_a_down at (a+1,b,c+1): requires `b ≠ 0`.
  b-up via hyp_comm requires `a ≠ 0`. Diagonal D-invariance; do all a-steps (resp. b-steps)
  first so only one nonzero is needed at a time. a=0 or b=0 handled by hyp 0 b c z = 1.
- [note] `have to verify identities numerically`.
- [verified] wolfram: diagA c/(c-b)·F, diagB c/(c-a)·F, a-up/b-up at c+1, combined
  c(c+1)/((c-a)(c-b))·F all agree to 20 digits at a=.3,b=.4,c=2.
- [key obstacle] `hyp_shift_a_down` lives in EllipticClass.lean, which Gauss.lean must NOT
  import (circular). Replaced with a direct limit of `hyp_contiguous_c` (DLMF 15.5.15) at
  (a,b,c+1): needs `a ≠ 0` (not `b ≠ 0`). b-up obtained via `hyp_comm`.
- [landed] Gauss.lean now has (compiles clean, diagnostics empty): gaussRatio,
  hypCoeff_zero_left, hyp_zero_left, hyp_shift_a_up_one, hyp_shift_b_up_one.
- [next] diagonal steps hyp_one_diag_a/b, gaussRatio_shift_a/b, hypD, hypD_shift_a/b,
  multistep shifts, then hyp_one_eq_Gamma' by case analysis (a∈-ℕ ⟹ reach a=0; b∈-ℕ;
  else shift both up and apply hyp_one_eq_Gamma).
- [landed] hyp_one_diag_a, hyp_one_diag_b, hypD, hyp_zero_right, gaussRatio_ne_zero,
  gaussRatio_shift_a, gaussRatio_shift_b, hypD_shift_a, hypD_shift_b.
- [landed] hypD_shift_a_nat, hypD_shift_b_nat (multistep), hypD_zero_left, hypD_zero_right.
- [landed] `hyp_one_eq_Gamma'` exactly as requested. Case analysis: a∈-ℕ → shift to a=0;
  b∈-ℕ → shift to b=0; otherwise shift a,b up by m with `m > max(max(-a)(-b))(b-c)` and
  apply `hyp_one_eq_Gamma`. No `sorry`, no `axiom`.
- [check] `lean_diagnostic_messages` whole file: empty (success). No shell Lean used.
- [verify] `lean_verify Pconstructible.hyp_one_eq_Gamma'`: propext, Classical.choice,
  Quot.sound; warnings [].
- [final] Gauss.lean fully compiles; remaining gap: none. Note: `hyp_one_eq_Gamma` (a,b>0,
  b<c) kept unchanged; `hyp_one_Pconstructible_of_den_24` untouched.
