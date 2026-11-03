import Pptc.Basic
import Pptc.Box
import Pptc.Offset
import Pptc.OffsetInversion.Projectile

/-!
# Scratch: negative test for the `offset` soundness holes

**This file intentionally does not compile.** It is not imported by `Pptc.lean` and is not
part of the library. It records the two ways the old, unsound `offset` constructor collapsed
`PConstructible` to all reals, and shows that the new signature blocks both.

The old constructor took a *sub-arc* `γ '' Icc a b ⊆ S` and allowed `a = b`. The two
collapses were:

1. **Sub-arc collapse.** Trace the parabola, offset only the single point `γ b` by `d = 0`,
   and read the endpoint with `box_xmax`. Since the piece was merely a subset of the drawn
   shape, a point of an arbitrary shape could be used to reach an arbitrary real.
2. **Singleton collapse.** Crop the parabola to the single point `(b, b ^ 2)` with a
   degenerate `restrict` window, then offset it with `a = b`. The normal at a singleton is
   not determined by the singleton: it depends on the tracing away from that point, and the
   offset lands anywhere on a circle of radius `d` around it.

The new constructor asks for

* `himg : γ '' Icc a b = S` — the tracing must cover the *whole* curve, not a piece;
* `hab : a < b` — the window must be nondegenerate, so the one-sided derivatives at the
  endpoints determine the normal from inside the curve.

The live theorem below is the singleton variant. Its only failing step is `b < b`; there is
no proof of that proposition, so the collapse is closed. The old sub-arc call is shown in a
comment afterwards.

The singleton curve itself is legitimately constructible: start from
`parabola_PConstructibleCurve` and crop it with
`PConstructibleCurve.restrict hS b b (b ^ 2) (b ^ 2) ...`, whose bounds are all
`PConstructible`. The degenerate window really is a singleton. What fails is only the
`offset` step.
-/

namespace Pconstructible

open Set

/-- The parabola as a tracing. -/
def testGamma (t : ℝ) : ℝ × ℝ := (t, t ^ 2)

/-- If this compiled, every real would be P-constructible. It fails at `b < b`, the
nondegeneracy condition added to `PConstructibleCurve.offset`. -/
theorem all_real_Pconstructible_test (b : ℝ)
    (hS : PConstructibleCurve (testGamma '' Set.Icc b b)) : PConstructible b := by
  have hdiff : ∀ t ∈ Set.Icc b b,
      DifferentiableAt ℝ (fun s => (testGamma s).1) t ∧
        DifferentiableAt ℝ (fun s => (testGamma s).2) t := by
    intro t _
    constructor
    · change DifferentiableAt ℝ (fun s : ℝ => s) t
      exact differentiableAt_id
    · change DifferentiableAt ℝ (fun s : ℝ => s ^ 2) t
      exact differentiableAt_id.pow 2
  have hreg : ∀ t ∈ Set.Icc b b, speed testGamma t ≠ 0 := by
    intro t _
    simp only [speed, testGamma]
    have h1 : deriv (fun s : ℝ => s) t = 1 := deriv_id t
    have h2 : deriv (fun s : ℝ => s ^ 2) t = 2 * t := by
      change deriv (fun s : ℝ => s ^ 2) t = 2 * t
      simp
    rw [h1, h2]
    positivity
  have hC1 : ContinuousOn (deriv (fun s => (testGamma s).1)) (Set.Icc b b) ∧
      ContinuousOn (deriv (fun s => (testGamma s).2)) (Set.Icc b b) := by
    constructor
    · rw [show deriv (fun s : ℝ => (testGamma s).1) = fun _ => 1 from by
        funext t; exact deriv_id t]
      exact continuousOn_const
    · rw [show deriv (fun s : ℝ => (testGamma s).2) = fun s => 2 * s from by
        funext t
        change deriv (fun s : ℝ => s ^ 2) t = 2 * t
        simp]
      fun_prop
  have hinj : Set.InjOn testGamma (Set.Ico b b) := by
    intro x hx y hy _
    exact absurd hx.2 (not_lt.mpr hx.1)
  -- The old proof supplied `le_rfl : b ≤ b` here, and `hsub : γ '' Icc b b ⊆ S` above.
  -- Both are now rejected: `hab` must be `b < b`, which is false.
  have h := PConstructibleCurve.offset hS testGamma (a := b) (b := b)
    (by linarith : b < b)
    rfl hinj (fun _ => rfl) hdiff hreg hC1 (d := 0) zero_Pconstructible
  have h' : PConstructibleCurve (testGamma '' Set.Icc b b) := by
    simpa [offsetParam_zero, testGamma] using h
  have hcont : ContinuousOn testGamma (Set.Icc b b) :=
    (continuous_id.prodMk (continuous_id.pow 2)).continuousOn
  have hmono : MonotoneOn (fun t => (testGamma t).1) (Set.Icc b b) := by
    intro x hx y hy _
    simp only [Set.mem_Icc] at hx hy
    simp only [testGamma]
    omega
  have hx := arc_xendpoint_Pconstructible h' le_rfl hcont hmono
  simpa [testGamma] using hx

/-! The old sub-arc call looked like this (it no longer typechecks, because `offset` wants
`himg : γ '' Icc a b = S`, an equality with the whole curve, where this has `⊆`):

```lean
have h := PConstructibleCurve.offset hS testGamma le_rfl hsub hinj hdiff hreg hC1
  (d := 0) zero_Pconstructible
```

The singleton variant above is the second hole: even with a whole, genuinely constructible
curve (the cropped singleton), the missing `a < b` was what let the offset direction be
chosen by the tracing rather than by the curve. -/

end Pconstructible
