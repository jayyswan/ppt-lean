# HANDOFF: Pptc/TotallyReal/SignChange.lean

## Goal
New file `pptc/Pptc/TotallyReal/SignChange.lean`, namespace `Pconstructible`, with three lemmas:

1. `signChange_of_simpleRoot {f : ℝ → ℝ} {x₀ d : ℝ} (hf : HasDerivAt f d x₀) (h0 : f x₀ = 0) (hd : d ≠ 0) :
     ∀ ε > 0, ∃ δ, 0 < δ ∧ δ < ε ∧ f (x₀ - δ) * f (x₀ + δ) < 0`
2. `signChange_of_factorization {f G : ℝ → ℝ} {x₀ : ℝ} (hG : ContinuousAt G x₀) (hG0 : G x₀ ≠ 0)
     (hfac : ∀ t, f t = (t - x₀) * G t) :
     ∀ ε > 0, ∃ δ, 0 < δ ∧ δ < ε ∧ f (x₀ - δ) * f (x₀ + δ) < 0`
3. `signChange_at_radius_of_factorization {f G : ℝ → ℝ} {x₀ δ : ℝ} (hδ : 0 < δ)
     (hG : ContinuousAt G x₀) (hG0 : G x₀ ≠ 0)
     (hsign : ∀ t ∈ Set.Icc (x₀ - δ) (x₀ + δ), 0 < G t * G x₀)
     (hfac : ∀ t, f t = (t - x₀) * G t) :
     f (x₀ - δ) * f (x₀ + δ) < 0`

## Plan
Prove (3) directly from factorization + hsign. Prove (2) by continuity sign-locally then pick δ.
Prove (1) via slope limit of HasDerivAt.tendsto_slope_zero.

## Log
- [start] Created handoff. Beginning file scaffold and reconnaissance.
- [recon] Confirmed lemma names: HasDerivAt.tendsto_slope_zero (Deriv/Slope.lean,
  fun t => t⁻¹ • (f (x₀+t)-f x₀)), Metric.eventually_nhds_iff, eventually_nhdsWithin_iff,
  pos_of_mul_pos_right (cancels LEFT: 0<a*b, 0≤a ⟹ 0<b), pos_of_mul_pos_left
  (cancels RIGHT: 0<a*b, 0≤b ⟹ 0<a), lt_of_mul_lt_mul_right (0≤a common right),
  Tendsto.const_mul, Tendsto.eventually, isOpen_Ioi.mem_nhds, mul_self_pos, inv_neg.
- [draft] Wrote full draft of SignChange.lean (all 3 lemmas). Running diagnostics.
- [fix] Lean doesn't have `Tendsto`/`𝓝` unqualified without opens. Added `open Filter`
  and `open scoped Topology`. Re-running diagnostics.
- [fix2] `Metric.eventually_nhds_iff`'s bound variable is IMPLICIT (`∀ ⦃y⦄`), so use
  `hball hdistp hne` (not `hball δ hdistp`). `abs_sub_le_iff` has the `a-b≤c ∧ b-a≤c`
  shape; used `rw [abs_le]` + linarith instead.
- [lsp] lean_diagnostic_messages on Pptc/TotallyReal/SignChange.lean: success=true, no items
  (no errors, no warnings).
- [blocker-env] `lake_check` initially failed 5x with "failed to read file ... .olean(.private)"
  on DIFFERENT files each run (Image.olean.private, WithBot, Grind/Main, LibraryRewrite,
  Grind/Param). Host was at ~600 MB free (guard threshold 900 MB); not a proof error.
  Waited, then applied documented recovery `Get-Process lean,lake | Stop-Process -Force`
  (freed to 4.8 GB).
- [lake_check-OK] `lake_check Pptc/TotallyReal/SignChange.lean` -> "OK - no errors or warnings."
- [axioms] axiom_check on the three declarations ->
  Pconstructible.signChange_at_radius_of_factorization: [propext, Classical.choice, Quot.sound]
  Pconstructible.signChange_of_factorization:            [propext, Classical.choice, Quot.sound]
  Pconstructible.signChange_of_simpleRoot:               [propext, Classical.choice, Quot.sound]
  No sorryAx.
- [sorry] rg -n "sorry|admit" -> no matches (exit 1).
- [DONE] All three lemmas proved. File path: pptc/Pptc/TotallyReal/SignChange.lean
  namespace Pconstructible. Exact signatures (final):
    theorem signChange_at_radius_of_factorization {f G : ℝ → ℝ} {x₀ δ : ℝ}
        (hδ : 0 < δ) (hG : ContinuousAt G x₀) (hG0 : G x₀ ≠ 0)
        (hsign : ∀ t ∈ Set.Icc (x₀ - δ) (x₀ + δ), 0 < G t * G x₀)
        (hfac : ∀ t, f t = (t - x₀) * G t) :
        f (x₀ - δ) * f (x₀ + δ) < 0
    theorem signChange_of_factorization {f G : ℝ → ℝ} {x₀ : ℝ}
        (hG : ContinuousAt G x₀) (hG0 : G x₀ ≠ 0)
        (hfac : ∀ t, f t = (t - x₀) * G t) :
        ∀ ε > 0, ∃ δ, 0 < δ ∧ δ < ε ∧ f (x₀ - δ) * f (x₀ + δ) < 0
    theorem signChange_of_simpleRoot {f : ℝ → ℝ} {x₀ d : ℝ}
        (hf : HasDerivAt f d x₀) (h0 : f x₀ = 0) (hd : d ≠ 0) :
        ∀ ε > 0, ∃ δ, 0 < δ ∧ δ < ε ∧ f (x₀ - δ) * f (x₀ + δ) < 0
  Imports used: Mathlib.Analysis.Calculus.Deriv.Slope (needed for
  HasDerivAt.tendsto_slope_zero) + Mathlib.Topology.Order.IntermediateValue (as supplied),
  plus `open Filter` / `open scoped Topology`. No other file edited.
