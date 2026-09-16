# B6 — sine arc-length cross-check (plan 3.N3)

Target file: `pptc/Pptc/BoxSine.lean` (package root `pptc`).
Add `import Pptc.BoxSine` to `pptc/Pptc.lean`.

Goal (Lean):
```lean
theorem speed_sineArc (t : ℝ) :
    speed (fun s : ℝ => (s, Real.sin s)) t
      = Real.sqrt 2 * ellipticEIntegrand (1 / 2) t

theorem arcLengthOf_sineArc (X : ℝ) :
    arcLengthOf (fun s : ℝ => (s, Real.sin s)) 0 X
      = Real.sqrt 2 * ellipticE (1 / 2) X

theorem ellipticEAm_Pconstructible_via_sine {L : ℝ} (hL : PConstructible L)
    (hL0 : 0 ≤ L) (hLub : L ≤ Real.sqrt 2 * ellipticE (1 / 2) (Real.pi / 2)) :
    PConstructible (ellipticEAm (1 / 2) (L / Real.sqrt 2))
```

Plan: prove speed identity from `speed` defn + `1 + cos² = 2 - sin²`; integrate;
third via `arc_of_length` + `arc_xendpoint_Pconstructible`.

## Log
- [start] created log; next: inspect `speed`, `ellipticEIntegrand`, `ellipticE`, `arcLengthOf`, `arc_xendpoint_Pconstructible`, `ellipticE_ellipticEAm`.
- [defs] matched: `speed γ t = √(deriv (γ·).1 t ^2 + deriv (γ·).2 t ^2)`; `arcLengthOf γ a b = ∫ t in a..b, speed γ t`; `ellipticEIntegrand c θ = √(1 - c*sin θ^2)`; `ellipticE c φ = ∫ θ in 0..φ, ellipticEIntegrand c θ`. Box: `arc_xendpoint_Pconstructible` (Box.lean:214), Jacobi: `ellipticE_ellipticEAm` (420), `strictMono_ellipticE` (129), pattern (503-541).
- [write] wrote all three theorems in Pptc/BoxSine.lean; added `import Pptc.BoxSine` to Pptc.lean.
- [fix] `hasDerivAt_id` had an `id`/`fun s=>s` instance mismatch; switched to `hasDerivAt_id'`. lean_diagnostic_messages now clean (0 items).
- next: lake_check + lean_verify.
- [done] `lake_check Pptc/BoxSine.lean` → "OK - no errors or warnings." `lean_verify` all three → only `propext`, `Classical.choice`, `Quot.sound`.
  - `speed_sineArc` (BoxSine.lean:52)
  - `arcLengthOf_sineArc` (BoxSine.lean:66)
  - `ellipticEAm_Pconstructible_via_sine` (BoxSine.lean:81)
  - import added Pptc.lean:13.
- Status: ALL THREE LANDED. No `sorry`. No name surprises beyond `hasDerivAt_id` needing `hasDerivAt_id'`.
- [final] removed two unused `have`s; re-ran `lake_check Pptc/BoxSine.lean` → "OK - no errors or warnings."
