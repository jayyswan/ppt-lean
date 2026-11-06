# HANDOFF: ellipseOffset_PConstructibleCurve

**File:** `C:/dev/Powerpoint/lean/pptc/Pptc/Offset.lean`
**Goal (Lean):**

```lean
theorem ellipseOffset_PConstructibleCurve {b d : ℝ} (hb : PConstructible b) (hbpos : 0 < b)
    (hd : PConstructible d) :
    PConstructibleCurve (offsetParam (ellipseParam b) d '' Set.Icc 0 (2 * Real.pi))
```

Helpers planned:
1. `ellipseParam_image_Icc_two_pi {b} (hbpos : 0 < b) :
     ellipseParam b '' Icc 0 (2π) = {p | p.1 ^ 2 + (p.2 / b) ^ 2 = 1}`
2. `injOn_ellipseParam_Ico {b} (hbpos : 0 < b) : InjOn (ellipseParam b) (Ico 0 (2π))`

Plan: outline file, prove helpers with lean_goal/lean_multi_attempt, then main
proof via `PConstructibleCurve.offset`, final `lake env lean Pptc/Offset.lean`.

## Log
- created log; next: outline Offset.lean
- outlined Offset.lean (856 lines, single `namespace Pconstructible`, ends `end Pconstructible`).
- read Defs.lean defs of `speed`/`unitNormal`/`offsetParam`; Basic.lean 3374-3393 for
  `ellipse_PConstructibleCurve`, `ellipseParam`, `speed_ellipseParam`.
- inserted section + 3 declarations with `sorry` bodies just before `end Pconstructible`;
  diagnostics: only 3 `sorry` warnings, statements all parse. ✓
- helper 1 (`ellipseParam_image_Icc_two_pi`) proof verified in `lean_multi_attempt`
  (no diagnostics) and written into the file. Key steps: `field_simp` +
  `linear_combination Real.sin_sq_add_cos_sq θ` for ⊆; `Real.surjOn_cos` + `sq_eq_sq_iff_eq_or_eq_neg`
  for ⊇, with `Prod.ext` for the pair equality.
- next: helper 2 (`injOn_ellipseParam_Ico`).
- helper 2 proof verified in `lean_multi_attempt` and written in. Idea: get
  `cos θ₁ = cos θ₂` / `sin θ₁ = sin θ₂`, hence `cos (θ₁ - θ₂) = 1`; since
  `θ₁ - θ₂ ∈ (-2π, 2π)`, `Real.cos_eq_one_iff_of_lt_of_lt` gives `θ₁ - θ₂ = 0`.
  Cleaner than `Real.cos_eq_cos_iff` (no integer case split). ✓
- next: main theorem `ellipseOffset_PConstructibleCurve`.
- main proof verified in `lean_multi_attempt` (no errors) and written in: builds `hderivx`,
  `hderivy`, `hs2`, `hs0`, `hseam`, `himg`, `hdiff`, `hreg`, `hC1`, then
  `PConstructibleCurve.offset ...`. All three declarations now filled.
- next: `lake env lean Pptc/Offset.lean` (final), then `axiom_check`.
