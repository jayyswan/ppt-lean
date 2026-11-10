# Handoff — Newman's AGM invariance for `agmJ` (step 3)

**Status: DONE.** `Pptc/Scratch/AGMStep3.lean` compiles with
`lake env lean Pptc/Scratch/AGMStep3.lean` → exit 0, no errors, **no `sorry` warnings**;
`lake build Pptc.Scratch.AGMStep3` succeeds; `lean_verify` on
`Pconstructible.agmJ_newman` reports axioms `[propext, Classical.choice, Quot.sound]`
(no `sorryAx`).

## Final statement

```lean
theorem agmJ_newman {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    agmJ (Real.sqrt (a * b)) ((a + b) / 2) = agmJ a b
```

with `def agmJ (a b : ℝ) : ℝ := ∫ t in Set.Ioi (0 : ℝ), (Real.sqrt ((t ^ 2 + a ^ 2) * (t ^ 2 + b ^ 2)))⁻¹`.

## Deviation to note

`MeasureTheory.integral_comp_abs` is **not** in scope from the two suggested imports.
I added one import line that was *not* in the prescribed header:

```lean
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
```

(the `.olean` for that module was already built, so this costs nothing). If the third
import is unacceptable, the lemma `integral_comp_abs {f : ℝ → ℝ} : ∫ x, f |x| = 2 * ∫ x in Ioi 0, f x`
can be replaced by a local `private` version specialized to even functions, but note that
its proof needs `integral_comp_neg_Iic` / `Measure.map_neg_eq_self`, which are in the *same*
not-imported file, so this would mean inlining ~30 lines of integrability case-splitting.

## Helper lemmas (all `private`, in `namespace Pconstructible`)

| name | statement |
|---|---|
| `agmJ_alg_g` | `((x - a*b/x)/2)^2 + (√(a*b))^2 = (x^2 + a*b)^2 / (4*x^2)` (`0<a`, `0<b`, `0<x`) |
| `agmJ_alg_m` | `((x - a*b/x)/2)^2 + ((a+b)/2)^2 = (x^2+a^2)*(x^2+b^2) / (4*x^2)` (`0<x`) |
| `agmJ_deriv` | `HasDerivAt (fun y => (y - a*b/y)/2) ((1 + a*b/x^2)/2) x` (`x ≠ 0`) |
| `agmJ_key` | `\|(1+a*b/x^2)/2\| * (√(((φx)^2+((a+b)/2)^2) * ((φx)^2+(√(a*b))^2)))⁻¹ = 2 * (√((x^2+a^2)*(x^2+b^2)))⁻¹` where `φx = (x - a*b/x)/2` (`0<a`, `0<b`, `0<x`) — the change-of-variables algebra |
| `agmJ_surj` | `(fun x => (x - a*b/x)/2) '' Ioi 0 = univ` (`0<a`, `0<b`) |

Full sources are in the file listing below.

## Mathlib lemmas that mattered

* `MeasureTheory.integral_image_eq_integral_abs_deriv_smul`
  (`Mathlib/MeasureTheory/Function/JacobianOneDim.lean`) — one-dimensional change of
  variables `∫ x in f '' s, g x = ∫ x in s, |f' x| • g (f x)`, **with no integrability
  hypothesis**, which is what makes the improper integral go through.
* `integral_comp_abs` (`Mathlib/MeasureTheory/Measure/Lebesgue/Integral.lean`) —
  `∫ x, f |x| = 2 * ∫ x in Ioi 0, f x`; combined with evenness of `F` to halve the line.
* `MeasureTheory.integral_congr_ae` — must be **qualified**: unqualified
  `integral_congr` / `integral_congr_ae` are ambiguous with `intervalIntegral.*`.
* `MeasureTheory.integral_const_mul` — also must be qualified (`intervalIntegral.integral_const_mul` clashes).
* `MeasureTheory.setIntegral_univ`, `setIntegral_congr_fun`, `setIntegral_union`, `measurableSet_Ioi`.
* `Real.sq_sqrt`, `Real.mul_self_sqrt`, `Real.sqrt_pos`, `Real.sqrt_mul`,
  `Real.sqrt_sq_eq_abs`, `Real.sq_sqrt`.
* `strictMonoOn_of_hasDerivWithinAt_pos` was **not** needed: `InjOn` is proved directly
  from the algebraic factorisation `(x-y)*(1 + ab/(xy)) = 0`.
* Derivative gotcha: `(hasDerivAt_const ..).div (hasDerivAt_id x) hx` produces an
  instance mismatch (`Semiring.toModule` vs `NormedAlgebra.toNormedSpace.toModule`), and
  neither `simpa`, `convert` nor `exact` fixes it. Working route:
  `simpa [div_eq_mul_inv, neg_div] using (hasDerivAt_inv hx).const_mul (a * b)`.
* At this Mathlib version `le_or_lt` is **not** available; use `le_total` (and
  `push Not` instead of the deprecated `push_neg`).

## Proof shape

1. `hFeven : ∀ t, F (-t) = F t` (only `(-t)^2 = t^2`).
2. `hhalf : ∫ t, F t = 2 * ∫ t in Ioi 0, F t` — `integral_comp_abs` + evenness.
3. `hsub : ∫ t, F t = 2 * agmJ a b` — `integral_image_eq_integral_abs_deriv_smul` with
   `s = Ioi 0`, `f = φ`, `f' x = (1 + ab/x²)/2`, `φ '' Ioi 0 = univ` (`agmJ_surj`),
   pointwise identity `agmJ_key`, then `integral_const_mul`.
4. `h2 : ∫ t in Ioi 0, F t = agmJ a b` — `linarith` from 2 and 3.
5. `h3 : agmJ g m = ∫ t in Ioi 0, F t` — `mul_comm` under the `√` (`m = (a+b)/2`, `g = √(ab)`).

Note on ordering (as requested): only step 3 needs real work; `integral_comp_abs` needs
no integrability side conditions, and `linarith` does the halving.

## Full final file

```lean
import Pptc.Basic
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

noncomputable section
open MeasureTheory Set intervalIntegral Real Filter Topology
namespace Pconstructible

/-- `J(a, b) = ∫₀^∞ dt / √((t² + a²)(t² + b²))`. -/
def agmJ (a b : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), (Real.sqrt ((t ^ 2 + a ^ 2) * (t ^ 2 + b ^ 2)))⁻¹

/-! ### Algebra for the substitution `φ x = (x - ab/x)/2` -/

private lemma agmJ_alg_g {a b x : ℝ} (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) :
    ((x - a * b / x) / 2) ^ 2 + (Real.sqrt (a * b)) ^ 2 = (x ^ 2 + a * b) ^ 2 / (4 * x ^ 2) := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  rw [Real.sq_sqrt (mul_nonneg ha.le hb.le)]
  field_simp
  ring

private lemma agmJ_alg_m {a b x : ℝ} (hx : 0 < x) :
    ((x - a * b / x) / 2) ^ 2 + ((a + b) / 2) ^ 2 =
      (x ^ 2 + a ^ 2) * (x ^ 2 + b ^ 2) / (4 * x ^ 2) := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  field_simp
  ring

private lemma agmJ_deriv (a b x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => (y - a * b / y) / 2) ((1 + a * b / x ^ 2) / 2) x := by
  have h1 : HasDerivAt (fun y : ℝ => a * b / y) (-(a * b) / x ^ 2) x := by
    simpa [div_eq_mul_inv, neg_div] using (hasDerivAt_inv hx).const_mul (a * b)
  have h2 : HasDerivAt (fun y : ℝ => y - a * b / y) (1 - (-(a * b) / x ^ 2)) x :=
    (hasDerivAt_id x).sub h1
  have h3 : HasDerivAt (fun y : ℝ => (y - a * b / y) / 2) ((1 - (-(a * b) / x ^ 2)) / 2) x :=
    h2.div_const 2
  convert h3 using 1
  ring

private lemma agmJ_key {a b x : ℝ} (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) :
    |(1 + a * b / x ^ 2) / 2| *
        (Real.sqrt ((((x - a * b / x) / 2) ^ 2 + ((a + b) / 2) ^ 2) *
          (((x - a * b / x) / 2) ^ 2 + (Real.sqrt (a * b)) ^ 2)))⁻¹
      = 2 * (Real.sqrt ((x ^ 2 + a ^ 2) * (x ^ 2 + b ^ 2)))⁻¹ := by
  have hx2 : (0 : ℝ) < x ^ 2 := by nlinarith
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hP : 0 < (x ^ 2 + a ^ 2) * (x ^ 2 + b ^ 2) :=
    mul_pos (by nlinarith [sq_nonneg x]) (by nlinarith [sq_nonneg x])
  have hQ : 0 < x ^ 2 + a * b := by nlinarith [mul_pos ha hb]
  have h4x : (0 : ℝ) < 4 * x ^ 2 := by nlinarith
  rw [agmJ_alg_g ha hb hx, agmJ_alg_m hx]
  have hsq : ((x ^ 2 + a ^ 2) * (x ^ 2 + b ^ 2) / (4 * x ^ 2)) *
        ((x ^ 2 + a * b) ^ 2 / (4 * x ^ 2)) =
      (x ^ 2 + a ^ 2) * (x ^ 2 + b ^ 2) * ((x ^ 2 + a * b) / (4 * x ^ 2)) ^ 2 := by
    field_simp
  rw [hsq, Real.sqrt_mul hP.le, Real.sqrt_sq_eq_abs,
    abs_of_pos (div_pos hQ h4x)]
  have habs : |(1 + a * b / x ^ 2) / 2| = (x ^ 2 + a * b) / (2 * x ^ 2) := by
    have hsum : 1 + a * b / x ^ 2 = (x ^ 2 + a * b) / x ^ 2 := by
      field_simp
    have hpos : 0 < (x ^ 2 + a * b) / x ^ 2 / 2 := by
      have := div_pos hQ hx2
      linarith
    rw [hsum, abs_of_pos hpos, div_div, mul_comm (x ^ 2) 2]
  rw [habs]
  field_simp
  ring

private lemma agmJ_surj {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (fun x : ℝ => (x - a * b / x) / 2) '' Ioi (0 : ℝ) = univ := by
  ext t
  constructor
  · intro _; trivial
  · intro _
    have h1 : 0 < t ^ 2 + a * b := by nlinarith [sq_nonneg t]
    have hspos : 0 < Real.sqrt (t ^ 2 + a * b) := Real.sqrt_pos.2 h1
    have hs : Real.sqrt (t ^ 2 + a * b) * Real.sqrt (t ^ 2 + a * b) = t ^ 2 + a * b :=
      Real.mul_self_sqrt h1.le
    have hxpos : 0 < t + Real.sqrt (t ^ 2 + a * b) := by
      by_contra hcon
      push Not at hcon
      nlinarith [hs, hspos, hcon, sq_nonneg (t + Real.sqrt (t ^ 2 + a * b))]
    refine ⟨t + Real.sqrt (t ^ 2 + a * b), hxpos, ?_⟩
    have hx : t + Real.sqrt (t ^ 2 + a * b) ≠ 0 := ne_of_gt hxpos
    change (t + Real.sqrt (t ^ 2 + a * b) - a * b / (t + Real.sqrt (t ^ 2 + a * b))) / 2 = t
    field_simp
    nlinarith [hs]

theorem agmJ_newman {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    agmJ (Real.sqrt (a * b)) ((a + b) / 2) = agmJ a b := by
  set m : ℝ := (a + b) / 2 with hm
  set g : ℝ := Real.sqrt (a * b) with hg
  set F : ℝ → ℝ := fun t => (Real.sqrt ((t ^ 2 + m ^ 2) * (t ^ 2 + g ^ 2)))⁻¹ with hF
  -- `F` is even
  have hFeven : ∀ t : ℝ, F (-t) = F t := by
    intro t
    simp only [hF]
    ring_nf
  -- replace the integral over `ℝ` by twice the integral over `Ioi 0`
  have hhalf : ∫ t : ℝ, F t = 2 * ∫ t in Ioi (0 : ℝ), F t := by
    rw [← integral_comp_abs (f := F)]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht]
    · rw [abs_of_nonpos ht, hFeven t]
  -- change of variables `t = φ x` on `Ioi 0`, whose image is all of `ℝ`
  have hsub : ∫ t : ℝ, F t = 2 * agmJ a b := by
    have hinj : InjOn (fun x : ℝ => (x - a * b / x) / 2) (Ioi (0 : ℝ)) := by
      intro x hx y hy hxy
      have hx0 : x ≠ 0 := ne_of_gt hx
      have hy0 : y ≠ 0 := ne_of_gt hy
      have key : (x - y) * (1 + a * b / (x * y)) = 0 := by
        field_simp at hxy ⊢
        linarith
      have hpos : 0 < 1 + a * b / (x * y) := by
        have h : 0 < a * b / (x * y) := div_pos (mul_pos ha hb) (mul_pos hx hy)
        linarith
      have hxy' : x - y = 0 := by
        rcases mul_eq_zero.1 key with h | h
        · exact h
        · linarith
      linarith
    have hderiv : ∀ x ∈ Ioi (0 : ℝ),
        HasDerivWithinAt (fun x : ℝ => (x - a * b / x) / 2) ((1 + a * b / x ^ 2) / 2)
          (Ioi (0 : ℝ)) x := by
      intro x hx
      exact (agmJ_deriv a b x (ne_of_gt hx)).hasDerivWithinAt
    have h := integral_image_eq_integral_abs_deriv_smul (f := fun x : ℝ => (x - a * b / x) / 2)
      (f' := fun x : ℝ => (1 + a * b / x ^ 2) / 2) (s := Ioi (0 : ℝ)) measurableSet_Ioi
      hderiv hinj F
    rw [agmJ_surj ha hb, setIntegral_univ] at h
    have hcongr : ∫ x in Ioi (0 : ℝ), |(1 + a * b / x ^ 2) / 2| • F ((x - a * b / x) / 2)
        = ∫ x in Ioi (0 : ℝ), 2 * (Real.sqrt ((x ^ 2 + a ^ 2) * (x ^ 2 + b ^ 2)))⁻¹ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      simp only [hF]
      rw [smul_eq_mul, hm, hg]
      exact agmJ_key ha hb hx
    rw [hcongr, MeasureTheory.integral_const_mul] at h
    simpa [agmJ] using h
  -- halve
  have h2 : ∫ t in Ioi (0 : ℝ), F t = agmJ a b := by
    linarith
  have h3 : agmJ g m = ∫ t in Ioi (0 : ℝ), F t := by
    simp only [agmJ]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    simp only [hF]
    simp [mul_comm]
  rw [h3]
  exact h2

end Pconstructible
```
