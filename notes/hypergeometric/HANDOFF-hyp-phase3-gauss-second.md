# Phase 3: Gauss's second theorem

Goal (target file `pptc/Pptc/Hypergeometric/GaussSecond.lean`):
```
theorem hyp_second {A B : ℝ}
    (hAB : ∀ n : ℕ, (A + B + 1) / 2 ≠ -(n : ℝ))
    (hA : ∀ n : ℕ, (A + 1) / 2 ≠ -(n : ℝ))
    (hB : ∀ n : ℕ, (B + 1) / 2 ≠ -(n : ℝ)) :
    hyp A B ((A + B + 1) / 2) (1 / 2) =
      Real.sqrt Real.pi * Real.Gamma ((A + B + 1) / 2) /
        (Real.Gamma ((A + 1) / 2) * Real.Gamma ((B + 1) / 2))

theorem hyp_second_rat_Pconstructible {A B : ℚ} (hAB hA hB) :
    PConstructible (hyp (A : ℝ) (B : ℝ) (((A + B + 1) / 2 : ℚ) : ℝ) (1 / 2))
```

Plan: a=A/2, b=B/2, c=(A+B+1)/2; Goursat maps hyp A B c z = hyp a b c (4z(1-z));
take z→1/2⁻, right side tends to hyp a b c 1 (Abel), LHS continuous at 1/2;
then Gauss at 1 for (a,b,c) plus Gamma(1/2).

## Log
- start
- read plan, GoursatGeneral (hyp_goursat, signature confirmed), GaussRational, Gauss.lean (Abel + hyp_one_eq_Gamma'), Quadratic analyticity template.
- wrote full draft of Pptc/Hypergeometric/GaussSecond.lean; first diagnostics: only local tactic errors (hcab norm_num, nhdsWithin mono_left elaboration, nlinarith, AnalyticOnNhd projection, hz0 type). Applying fixes.
- lean_diagnostic_messages: `success: true`, no errors/warnings. Both theorem statements accepted as given in the task.
- `lake env lean` with temporary `#print axioms`: hyp_second and hyp_second_rat_Pconstructible depend on [propext, Classical.choice, Quot.sound] only (no sorryAx).
- removed temporary #print lines, running final `lake env lean`.
- FINAL: `lake env lean Pptc/Hypergeometric/GaussSecond.lean` exit 0; no errors/warnings; no `sorry`; max line length 100.
- Axioms (from temporary `#print axioms`): both `Pconstructible.hyp_second` and
  `Pconstructible.hyp_second_rat_Pconstructible` depend only on `[propext, Classical.choice,
  Quot.sound]`.
- Declarations (exact):
  * `Pconstructible.hyp_second {A B : ℝ} (hAB : ∀ n, (A+B+1)/2 ≠ -(n:ℝ))
      (hA : ∀ n, (A+1)/2 ≠ -(n:ℝ)) (hB : ∀ n, (B+1)/2 ≠ -(n:ℝ)) :
      hyp A B ((A+B+1)/2) (1/2) = √π * Γ((A+B+1)/2) / (Γ((A+1)/2) * Γ((B+1)/2))`
  * `Pconstructible.hyp_second_rat_Pconstructible {A B : ℚ} (hAB hA hB : rational pole
      conditions) : PConstructible (hyp (A:ℝ) (B:ℝ) (((A+B+1)/2 : ℚ):ℝ) (1/2))`
- Proof: set c=(A+B+1)/2; h_limR = Abel at 1 composed with z↦4z(1-z): 𝓝[<](1/2)→𝓝[<]1;
  h_limL = analyticity of hyp A B c on the unit disc (ordinaryHypergeometricSeries +
  one_le_hypergeometric_radius) at 1/2; congr with hyp_goursat on 0≤z<1/2; tendsto_nhds_unique;
  hyp_one_eq_Gamma' + Real.Gamma_one_half_eq + ring.
- Rational version transfers hAB/hA/hB with `exact_mod_cast`, rewrites with `hyp_second`, pushes
  casts, then Gamma_rat_Pconstructible and sqrt_pi_Pconstructible.
- DONE. No gaps.
