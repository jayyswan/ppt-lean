# HANDOFF: AGM step 2 — `agmI_eq_agmJ`

Status: **DONE**. `lake env lean Pptc/Scratch/AGMStep2.lean` exits 0 with no
output (no errors, no warnings). `lean_verify` on
`Pconstructible.agmI_eq_agmJ` reports only the standard axioms
`propext`, `Classical.choice`, `Quot.sound` (no `sorryAx`).

Target file: `Pptc/Scratch/AGMStep2.lean`
Declaration: `Pconstructible.agmI_eq_agmJ`

## Final statement

```lean
theorem agmI_eq_agmJ {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : agmI a b = agmJ a b
```

where

```lean
def agmI (a b : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..Real.pi / 2, (Real.sqrt (a ^ 2 * Real.cos θ ^ 2 + b ^ 2 * Real.sin θ ^ 2))⁻¹

def agmJ (a b : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), (Real.sqrt ((t ^ 2 + a ^ 2) * (t ^ 2 + b ^ 2)))⁻¹
```

## Helper lemmas

No new top-level helper declarations were introduced; everything is local
`have` clauses inside the theorem. The named local facts are (exact Lean
statements, copied verbatim from the file):

```lean
  have hI : agmI a b
      = ∫ θ in Ioo (0 : ℝ) (Real.pi / 2),
          (Real.sqrt (a ^ 2 * Real.cos θ ^ 2 + b ^ 2 * Real.sin θ ^ 2))⁻¹

  have himg : (fun θ : ℝ => b * Real.tan θ) '' Ioo (0 : ℝ) (Real.pi / 2) = Ioi (0 : ℝ)

  have hderiv : ∀ θ ∈ Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivWithinAt (fun θ : ℝ => b * Real.tan θ) (b * (1 / Real.cos θ ^ 2))
        (Ioo (0 : ℝ) (Real.pi / 2)) θ

  have hinj : InjOn (fun θ : ℝ => b * Real.tan θ) (Ioo (0 : ℝ) (Real.pi / 2))

  have hpt : ∀ θ ∈ Ioo (0 : ℝ) (Real.pi / 2),
      (Real.sqrt (a ^ 2 * Real.cos θ ^ 2 + b ^ 2 * Real.sin θ ^ 2))⁻¹
        = |b * (1 / Real.cos θ ^ 2)| •
            (Real.sqrt (((b * Real.tan θ) ^ 2 + a ^ 2)
              * ((b * Real.tan θ) ^ 2 + b ^ 2)))⁻¹
```

Inside `hpt` there are the algebraic sub-facts

```lean
    have h1T : 1 + Real.tan θ ^ 2 = 1 / Real.cos θ ^ 2
    have hQ : 0 < a ^ 2 * Real.cos θ ^ 2 + b ^ 2 * Real.sin θ ^ 2
    have hP2 : (b * Real.tan θ) ^ 2 + b ^ 2 = b ^ 2 / Real.cos θ ^ 2
    have hP1 : (b * Real.tan θ) ^ 2 + a ^ 2
        = (a ^ 2 * Real.cos θ ^ 2 + b ^ 2 * Real.sin θ ^ 2) / Real.cos θ ^ 2
    have hprod : ((b * Real.tan θ) ^ 2 + a ^ 2) * ((b * Real.tan θ) ^ 2 + b ^ 2)
        = b ^ 2 * (a ^ 2 * Real.cos θ ^ 2 + b ^ 2 * Real.sin θ ^ 2)
            / Real.cos θ ^ 4
    have hsqrt : Real.sqrt (((b * Real.tan θ) ^ 2 + a ^ 2)
          * ((b * Real.tan θ) ^ 2 + b ^ 2))
        = b * Real.sqrt (a ^ 2 * Real.cos θ ^ 2 + b ^ 2 * Real.sin θ ^ 2)
            / Real.cos θ ^ 2
    have habs : |b * (1 / Real.cos θ ^ 2)| = b / Real.cos θ ^ 2
```

## Mathlib lemmas that mattered

* `MeasureTheory.integral_image_eq_integral_abs_deriv_smul`
  (`hs : MeasurableSet s`) (`hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x`)
  (`hf : InjOn f s`) (`g`) :
  `∫ x in f '' s, g x = ∫ x in s, |f' x| • g (f x)` — the one-dimensional
  change of variables, no integrability hypothesis needed.
* `intervalIntegral.integral_of_le` :
  `∫ x in a..b, f x = ∫ x in Ioc a b, f x` for `a ≤ b`.
* `MeasureTheory.integral_Ioc_eq_integral_Ioo` :
  `∫ t in Ioc x y, f t = ∫ t in Ioo x y, f t`.
* `Real.hasDerivAt_tan` (`h : cos x ≠ 0`) :
  `HasDerivAt tan (1 / cos x ^ 2) x` (note: Mathlib states the derivative as
  `1 / cos x ^ 2`, not `1 + tan x ^ 2`).
* `Real.one_add_tan_sq_mul_cos_sq_eq_one` (`h : cos x ≠ 0`) :
  `(1 + tan x ^ 2) * cos x ^ 2 = 1`, used to get `1 + tan²θ = 1/cos²θ`.
* `Real.strictMonoOn_tan`, `Real.injOn_tan` :
  `InjOn tan (Ioo (-(π / 2)) (π / 2))`.
* `Real.arctan_pos` (`0 < arctan x ↔ 0 < x`), `Real.arctan_lt_pi_div_two`,
  `Real.tan_arctan` : surjectivity of `θ ↦ b * tan θ` onto `Ioi 0`.
* `Real.tan_eq_sin_div_cos` : `tan x = sin x / cos x`.
* `Real.cos_pos_of_mem_Ioo`, `Real.sin_pos_of_mem_Ioo` : positivity of
  `cos` on `(-(π/2), π/2)` and of `sin` on `(0, π)`.
* `Real.sqrt_div` (`0 ≤ x`) : `√(x / y) = √x / √y`.
* `Real.sqrt_mul` (`0 ≤ x`) : `√(x * y) = √x * √y`.
* `Real.sqrt_sq` (`0 ≤ x`) : `√(x ^ 2) = x`.
* `MeasureTheory.setIntegral_congr_fun` (`MeasurableSet s`) (`EqOn f g s`).
* `mul_left_cancel₀`, `mul_div_cancel₀`.

## Final file `Pptc/Scratch/AGMStep2.lean`

```lean
import Pptc.Basic
import Mathlib.MeasureTheory.Function.JacobianOneDim

noncomputable section
open MeasureTheory Set intervalIntegral Real Filter Topology
namespace Pconstructible

/-- `I(a, b) = ∫₀^{π/2} dθ / √(a² cos²θ + b² sin²θ)`. -/
def agmI (a b : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..Real.pi / 2, (Real.sqrt (a ^ 2 * Real.cos θ ^ 2 + b ^ 2 * Real.sin θ ^ 2))⁻¹

/-- `J(a, b) = ∫₀^∞ dt / √((t² + a²)(t² + b²))`. -/
def agmJ (a b : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), (Real.sqrt ((t ^ 2 + a ^ 2) * (t ^ 2 + b ^ 2)))⁻¹

theorem agmI_eq_agmJ {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : agmI a b = agmJ a b := by
  -- Rewrite the interval integral over the half-open interval as one over the open interval.
  have hI : agmI a b
      = ∫ θ in Ioo (0 : ℝ) (Real.pi / 2),
          (Real.sqrt (a ^ 2 * Real.cos θ ^ 2 + b ^ 2 * Real.sin θ ^ 2))⁻¹ := by
    unfold agmI
    rw [intervalIntegral.integral_of_le (by positivity)]
    exact integral_Ioc_eq_integral_Ioo
  -- The substitution `t = b * tan θ` maps `(0, π/2)` onto `(0, ∞)`.
  have himg : (fun θ : ℝ => b * Real.tan θ) '' Ioo (0 : ℝ) (Real.pi / 2) = Ioi (0 : ℝ) := by
    ext t
    constructor
    · rintro ⟨θ, hθ, rfl⟩
      have hpi := Real.pi_pos
      have hc : 0 < Real.cos θ :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, hpi], hθ.2⟩
      have hs : 0 < Real.sin θ :=
        Real.sin_pos_of_mem_Ioo ⟨hθ.1, by linarith [hθ.2, hpi]⟩
      have htan : 0 < Real.tan θ := by
        rw [Real.tan_eq_sin_div_cos]
        positivity
      exact mul_pos hb htan
    · intro ht
      have ht0 : 0 < t := ht
      refine ⟨Real.arctan (t / b), ⟨?_, ?_⟩, ?_⟩
      · exact Real.arctan_pos.mpr (div_pos ht0 hb)
      · exact Real.arctan_lt_pi_div_two (t / b)
      · change b * Real.tan (Real.arctan (t / b)) = t
        rw [Real.tan_arctan]
        exact mul_div_cancel₀ t hb.ne'
  -- Derivative of the substitution.
  have hderiv : ∀ θ ∈ Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivWithinAt (fun θ : ℝ => b * Real.tan θ) (b * (1 / Real.cos θ ^ 2))
        (Ioo (0 : ℝ) (Real.pi / 2)) θ := by
    intro θ hθ
    have hpi := Real.pi_pos
    have hc : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, hpi], hθ.2⟩
    exact ((Real.hasDerivAt_tan hc.ne').const_mul b).hasDerivWithinAt
  -- Injectivity of the substitution.
  have hinj : InjOn (fun θ : ℝ => b * Real.tan θ) (Ioo (0 : ℝ) (Real.pi / 2)) := by
    intro x hx y hy hxy
    have htan : Real.tan x = Real.tan y := mul_left_cancel₀ hb.ne' hxy
    have hsub : Ioo (0 : ℝ) (Real.pi / 2) ⊆ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      intro z hz
      exact ⟨by linarith [hz.1, Real.pi_pos], hz.2⟩
    exact Real.injOn_tan (hsub hx) (hsub hy) htan
  -- Pointwise collapse of the pulled-back integrand.
  have hpt : ∀ θ ∈ Ioo (0 : ℝ) (Real.pi / 2),
      (Real.sqrt (a ^ 2 * Real.cos θ ^ 2 + b ^ 2 * Real.sin θ ^ 2))⁻¹
        = |b * (1 / Real.cos θ ^ 2)| •
            (Real.sqrt (((b * Real.tan θ) ^ 2 + a ^ 2)
              * ((b * Real.tan θ) ^ 2 + b ^ 2)))⁻¹ := by
    intro θ hθ
    have hpi := Real.pi_pos
    have hc : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, hpi], hθ.2⟩
    have hs : 0 < Real.sin θ :=
      Real.sin_pos_of_mem_Ioo ⟨hθ.1, by linarith [hθ.2, hpi]⟩
    have hcne : Real.cos θ ≠ 0 := hc.ne'
    have h1T : 1 + Real.tan θ ^ 2 = 1 / Real.cos θ ^ 2 := by
      rw [eq_div_iff (pow_ne_zero 2 hcne)]
      exact Real.one_add_tan_sq_mul_cos_sq_eq_one hcne
    have hQ : 0 < a ^ 2 * Real.cos θ ^ 2 + b ^ 2 * Real.sin θ ^ 2 := by positivity
    have hP2 : (b * Real.tan θ) ^ 2 + b ^ 2 = b ^ 2 / Real.cos θ ^ 2 := by
      have h : (b * Real.tan θ) ^ 2 + b ^ 2 = b ^ 2 * (1 + Real.tan θ ^ 2) := by ring
      rw [h, h1T]
      ring
    have hP1 : (b * Real.tan θ) ^ 2 + a ^ 2
        = (a ^ 2 * Real.cos θ ^ 2 + b ^ 2 * Real.sin θ ^ 2) / Real.cos θ ^ 2 := by
      rw [Real.tan_eq_sin_div_cos]
      field_simp [hcne]
      ring
    have hprod : ((b * Real.tan θ) ^ 2 + a ^ 2) * ((b * Real.tan θ) ^ 2 + b ^ 2)
        = b ^ 2 * (a ^ 2 * Real.cos θ ^ 2 + b ^ 2 * Real.sin θ ^ 2)
            / Real.cos θ ^ 4 := by
      rw [hP1, hP2]
      field_simp [hcne]
    have hsqrt : Real.sqrt (((b * Real.tan θ) ^ 2 + a ^ 2)
          * ((b * Real.tan θ) ^ 2 + b ^ 2))
        = b * Real.sqrt (a ^ 2 * Real.cos θ ^ 2 + b ^ 2 * Real.sin θ ^ 2)
            / Real.cos θ ^ 2 := by
      rw [hprod, Real.sqrt_div (by positivity)]
      rw [Real.sqrt_mul (by positivity)]
      rw [Real.sqrt_sq hb.le]
      rw [show Real.cos θ ^ 4 = (Real.cos θ ^ 2) ^ 2 by ring,
        Real.sqrt_sq (by positivity)]
    have habs : |b * (1 / Real.cos θ ^ 2)| = b / Real.cos θ ^ 2 := by
      rw [abs_of_pos (by positivity)]
      field_simp
    rw [habs, hsqrt, smul_eq_mul]
    field_simp [hb.ne', hcne, (Real.sqrt_pos.mpr hQ).ne']
  rw [hI]
  calc
    ∫ θ in Ioo (0 : ℝ) (Real.pi / 2),
        (Real.sqrt (a ^ 2 * Real.cos θ ^ 2 + b ^ 2 * Real.sin θ ^ 2))⁻¹
        = ∫ θ in Ioo (0 : ℝ) (Real.pi / 2),
            |b * (1 / Real.cos θ ^ 2)| •
              (Real.sqrt (((b * Real.tan θ) ^ 2 + a ^ 2)
                * ((b * Real.tan θ) ^ 2 + b ^ 2)))⁻¹ :=
          setIntegral_congr_fun measurableSet_Ioo hpt
    _ = ∫ t in (fun θ : ℝ => b * Real.tan θ) '' Ioo (0 : ℝ) (Real.pi / 2),
          (Real.sqrt ((t ^ 2 + a ^ 2) * (t ^ 2 + b ^ 2)))⁻¹ := by
          rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj]
    _ = ∫ t in Ioi (0 : ℝ), (Real.sqrt ((t ^ 2 + a ^ 2) * (t ^ 2 + b ^ 2)))⁻¹ := by
          rw [himg]
    _ = agmJ a b := rfl

end Pconstructible
```

## Notes / gotchas

* The substitution derivative in Mathlib is `1 / cos θ ^ 2` (not
  `1 + tan θ ^ 2`); the two are converted with
  `Real.one_add_tan_sq_mul_cos_sq_eq_one`.
* `(fun θ => b * tan θ) (arctan (t/b))` needs a `change` (or beta-reduction)
  before `rw [Real.tan_arctan]`.
* `field_simp` alone closed the `hprod` and final pointwise goals, so the
  trailing `ring`s were removed (they raised "no goals to be solved").
* The hypothesis `ha : 0 < a` is not used by the proof (the identity holds
  once the substitution is made; positivity of `a` only guarantees the
  radicands are positive). It is kept to match the requested signature, and
  no unused-variable warning is emitted.
