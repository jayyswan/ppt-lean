# HANDOFF: Octic OnePair part (b) — COMPLETE

File: `Pptc/Octic/OnePair.lean` (1035 lines). Part A kept unchanged; the trailing banner
`/-! ### Part B: sign change and assembly (to be appended) -/` was replaced by the new
section (it re-opens `namespace Pconstructible` / `noncomputable section` and closes with
`end` / `end Pconstructible`).

**Status: compiles clean.**
`lake build Pptc.Octic.OnePair` -> "Build completed successfully (2951 jobs)" (83 s).
`lean_diagnostic_messages` on the file: zero items.
No `sorry`/`admit`/`axiom`. No line over 100 chars.
`lean_verify` on all eight new declarations: axioms `propext, Classical.choice, Quot.sound`
(`trust: standard`).

## Declarations added (all in `namespace Pconstructible`)

```lean
theorem p3vec_Lcomb_stereo_of_qform_zero8 (q : ℝ[X]) {P₀ x : Fin 7 → ℝ}
    (hx : qform (Gram8 q) x = 0) :
    p3vec8 q (Lcomb8 q (stereoN (Gram8 q) P₀ x))
      = -8 * (bilin (Gram8 q) P₀ x) ^ 3 * p3vec8 q (Lcomb8 q x)

lemma root_of_mem_R8 {q : ℝ[X]} (hmon : q.Monic) {z : ℂ} {R : Multiset ℝ}
    (hroots : (q.map (algebraMap ℝ ℂ)).roots
      = z ::ₘ starRingEnd ℂ z ::ₘ (R.map (algebraMap ℝ ℂ))) :
    ∀ r ∈ R, q.eval r = 0

lemma bilin_Hmat8_vecOf8 (q : ℝ[X]) (f g : ℝ[X]) (hf : f.natDegree ≤ 7)
    (hg : g.natDegree ≤ 7) :
    bilin (Hmat8 q) (vecOf8 f) (vecOf8 g)
      = Matrix.trace ((aeval (companionN (n := 8) q) f)
        * (aeval (companionN (n := 8) q) g))

theorem ofReal_trace_mul_eq_sum8 (q f g : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 8)
    (hsep : q.Separable) {z : ℂ} {R : Multiset ℝ}
    (hroots : (q.map (algebraMap ℝ ℂ)).roots
      = z ::ₘ starRingEnd ℂ z ::ₘ (R.map (algebraMap ℝ ℂ))) :
    algebraMap ℝ ℂ (Matrix.trace ((aeval (companionN (n := 8) q) f)
        * (aeval (companionN (n := 8) q) g)))
      = ((R.map (fun r => f.eval r * g.eval r)).sum : ℂ)
        + ((f.map (algebraMap ℝ ℂ)).eval z) * ((g.map (algebraMap ℝ ℂ)).eval z)
        + ((f.map (algebraMap ℝ ℂ)).eval (starRingEnd ℂ z))
            * ((g.map (algebraMap ℝ ℂ)).eval (starRingEnd ℂ z))

theorem exists_direction_of_value8 {q : ℝ[X]} (hmon : q.Monic) (hnat : q.natDegree = 8)
    (hsep : q.Separable) {z : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0)
    (hzim : z.im ≠ 0)
    (hone : ∀ w : ℂ, (q.map (algebraMap ℝ ℂ)).eval w = 0 → w.im ≠ 0 →
      w = z ∨ w = starRingEnd ℂ z)
    {R : Multiset ℝ}
    (hroots : (q.map (algebraMap ℝ ℂ)).roots
      = z ::ₘ starRingEnd ℂ z ::ₘ (R.map (algebraMap ℝ ℂ)))
    (hRroot : ∀ r ∈ R, q.eval r = 0) (hRnodup : R.Nodup)
    {P₀ : Fin 7 → ℝ} {xj : ℝ} (hxjmem : xj ∈ R)
    {c : ℂ} (hc1 : c + starRingEnd ℂ c = -1) (hc2 : c * starRingEnd ℂ c = 1) :
    ∃ (d : Fin 7 → ℝ) (b : ℝ),
      qform (Gram8 q) d = 0 ∧
      p3vec8 q (Lcomb8 q d) = 3 ∧
      (b : ℂ) = (((polyOfVec8 (Lcomb8 q P₀)).eval xj : ℝ) : ℂ)
        + ((polyOfVec8 (Lcomb8 q P₀)).map (algebraMap ℝ ℂ)).eval z * c
        + starRingEnd ℂ (((polyOfVec8 (Lcomb8 q P₀)).map (algebraMap ℝ ℂ)).eval z)
          * starRingEnd ℂ c ∧
      bilin (Gram8 q) P₀ d = b

set_option maxHeartbeats 400000 in
private lemma sign_neg_aux {y1 y2 α γ S b1 b2 : ℝ}
    (hS : y1 ^ 2 + y2 ^ 2 ≤ S) (hg : γ ^ 2 = α ^ 2 + S / 2)
    (h1 : b1 = (y1 - α) ^ 2 - 3 * γ ^ 2) (h2 : b2 = (y2 - α) ^ 2 - 3 * γ ^ 2) :
    b1 < 0 ∨ b2 < 0 ∨ (S = 0 ∧ α = 0 ∧ γ = 0)
-- copied VERBATIM from DegreeSeven:3501 (dimension-free real arithmetic)

theorem exists_sign_change8 {q : ℝ[X]} (hmon : q.Monic) (hnat : q.natDegree = 8)
    (hsep : q.Separable)
    {z : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0) (hzim : z.im ≠ 0)
    (hone : ∀ w : ℂ, (q.map (algebraMap ℝ ℂ)).eval w = 0 → w.im ≠ 0 →
      w = z ∨ w = starRingEnd ℂ z)
    {P₀ : Fin 7 → ℝ} (hQ₀ : qform (Gram8 q) P₀ = 0) (hP₀ne : P₀ ≠ 0) :
    ∃ dplus dminus : Fin 7 → ℝ,
      0 < p3vec8 q (Lcomb8 q (stereoN (Gram8 q) P₀ dplus)) ∧
      p3vec8 q (Lcomb8 q (stereoN (Gram8 q) P₀ dminus)) < 0

set_option maxHeartbeats 1000000 in
theorem root_Pconstructible_of_one_conjugate_pair8 {q : ℝ[X]} (hmon : q.Monic)
    (hnat : q.natDegree = 8) (hsep : q.Separable) (hq : ∀ k, PConstructible (q.coeff k))
    {z : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0) (hzim : z.im ≠ 0)
    (hone : ∀ w : ℂ, (q.map (algebraMap ℝ ℂ)).eval w = 0 → w.im ≠ 0 →
      w = z ∨ w = starRingEnd ℂ z)
    {β : ℝ} (hβ : q.eval β = 0) :
    PConstructible β
```

## Port notes (differences from `DegreeSeven.lean`)

- `p3vec_Lcomb_stereo_of_qform_zero8`: new (the septic version at DegreeSeven:2540 was not
  ported into `Cone.lean`); `Lcomb8_smul` + `p3vec8_smul`, then `ring`.
- `ofReal_trace_mul_eq_sum8` uses `companionN_trace_aeval8` on `f * g` and `map_mul`
  (shorter than the septic `companion7_trace_pow_aeval` + `pow_one` route).
- `qform_Gram8_Lcomb8` has orientation `qform (Hmat8 q) (Lcomb8 q x) = qform (Gram8 q) x`, so
  where the septic used `← qform_Hmat_Lcomb` / `qform_Hmat_Lcomb` we use
  `qform_Gram8_Lcomb8` (forward for `Hmat -> Gram`, reversed for `Gram -> Hmat`).
- Final assembly: `exists_rat_vec_pos 7` (was 6); `stereoN_Pconstructible`,
  `qform_stereoN_eq_zero`, `stereoN_smul_add_smul`, `continuous_Phi8`,
  `exists_sextic_along_line8`, `root_Pconstructible_of_tschirnhaus8`,
  `p1vec8_eq_trace`, `p1vec8_Lcomb8`. The sextic `Ψ` keeps `natDegree ≤ 6` and is solved by
  `root_Pconstructible_le_six_coeffs`; the degeneracy exponent stays `^ 6`.
- Private part-A helpers reused: `vecOf8_polyOfVec8`, `eval_map_ofReal`,
  `eq_zero_of_vanishes_on_roots8`.

## Remaining work (not part of this task)

`Pptc/Octic/Main.lean` still needs `root_Pconstructible_of_nonreal_root8` (case split on a
second conjugate pair, port of DegreeSeven:4488) and `root_Pconstructible_deg8_coeffs`, plus
the `import Pptc.Octic.Main` line in `Pptc.lean`.
