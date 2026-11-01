/-
Copyright (c) 2024 Lean Community. All rights reserved.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

This file is part of the Pptc (PowerPoint Constructibility) project.
-/

import Pptc.ThirdKindAll.Period

/-! # Pptc.ThirdKindAll.Circular

The incomplete third-kind integral at **negative** characteristic `n < 0`.

The curve is a sheared sine graph,

  `γ(t) = (-b t + sin t, a t)`,  `b = √((1-n)(-n))/(c-n)`,  `a = √(c(1-c))/(c-n)`,

a linear image of the sine curve and therefore P-constructible. Its speed is
`√((cos t - b)² + a²)`, and the substitution

  `T(θ) = 2 arctan(k tan(θ/2))`,  `k = √(1-n) - √(-n)`

turns the arc length into

  `speed γ (T θ) · T'(θ) = Δ(θ)(p - q cos θ)² / (√D (1 - n sin²θ)²)`,

with `p = √(1-n)`, `q = √(-n)`, `D = c - n`. The antiderivative `circG` below has
exactly this derivative, and since it vanishes at `0` it *is* the arc length. Solving the
displayed expression of `circG` for `Π` gives the incomplete third-kind integral at `n < 0`
in terms of a P-constructible arc length and elementary functions.

The whole file works on `0 ≤ θ < π`; `Pptc.ThirdKindAll.Period` then removes that
restriction. -/

namespace Pconstructible

/-- `p = √(1 - n)`. -/
noncomputable def circP (n : ℝ) : ℝ := Real.sqrt (1 - n)

/-- `q = √(-n)`. -/
noncomputable def circQ (n : ℝ) : ℝ := Real.sqrt (-n)

/-- `k = p - q`; the half-angle scale of the substitution. -/
noncomputable def circK (n : ℝ) : ℝ := circP n - circQ n

/-- `D = c - n`. -/
noncomputable def circD (c n : ℝ) : ℝ := c - n

/-- `a = √(c(1-c))/D`, the vertical scale of the curve. -/
noncomputable def circA (c n : ℝ) : ℝ := Real.sqrt (c * (1 - c)) / circD c n

/-- `b = p q / D`, the horizontal shear of the curve. -/
noncomputable def circB (c n : ℝ) : ℝ := circP n * circQ n / circD c n

/-- The sheared sine curve. -/
noncomputable def circCurve (c n t : ℝ) : ℝ × ℝ :=
  (-circB c n * t + Real.sin t, circA c n * t)

/-- The curve as a linear image of the sine graph. -/
noncomputable def circS (c n : ℝ) : Set (ℝ × ℝ) :=
  linearMap (-circB c n) 1 (circA c n) 0 '' {p : ℝ × ℝ | p.2 = Real.sin p.1}

@[pconstructible]
theorem circP_Pconstructible {n : ℝ} (hnP : PConstructible n) : PConstructible (circP n) := by
  rw [circP]
  exact sqrt_Pconstructible (PConstructible.sub PConstructible.base_one hnP)

@[pconstructible]
theorem circQ_Pconstructible {n : ℝ} (hnP : PConstructible n) : PConstructible (circQ n) := by
  rw [circQ]
  exact sqrt_Pconstructible (neg_Pconstructible hnP)

@[pconstructible]
theorem circD_Pconstructible {c n : ℝ} (hcP : PConstructible c)
    (hnP : PConstructible n) : PConstructible (circD c n) := by
  rw [circD]
  exact PConstructible.sub hcP hnP

/-- The half-angle substitution `T(θ) = 2 arctan(k tan(θ/2))`. -/
noncomputable def circT (n θ : ℝ) : ℝ :=
  2 * Real.arctan (circK n * Real.tan (θ / 2))

/-- The characteristic denominator `w = 1 - n sin²θ`. -/
noncomputable def circW (n θ : ℝ) : ℝ := 1 - n * Real.sin θ ^ 2

/-- The principal denominator `Δ(θ)`. -/
noncomputable def circDelta (c θ : ℝ) : ℝ := ellipticEIntegrand c θ

/-- The argument of the arctangent in the elementary antiderivative. -/
noncomputable def circY (c n θ : ℝ) : ℝ :=
  Real.sqrt (circD c n) * Real.sin θ / circDelta c θ

/-- The elementary part of the antiderivative `circG`. -/
noncomputable def circElem (c n θ : ℝ) : ℝ :=
  - n * Real.sin θ * Real.cos θ * circDelta c θ / circW n θ
    - circP n * circQ n *
        (Real.sin θ * circDelta c θ / circW n θ
          + Real.arctan (circY c n θ) / Real.sqrt (circD c n))

/-- The antiderivative of the pulled-back speed. -/
noncomputable def circG (c n θ : ℝ) : ℝ :=
  (ellipticE c θ - ellipticF c θ + (1 - n) * ellipticPiInc c n θ + circElem c n θ)
    / Real.sqrt (circD c n)

/-! ### Elementary facts about the constants -/

theorem circP_sq {n : ℝ} (hn : n < 0) : circP n ^ 2 = 1 - n := by
  rw [circP]; exact Real.sq_sqrt (by linarith)

theorem circQ_sq {n : ℝ} (hn : n < 0) : circQ n ^ 2 = -n := by
  rw [circQ]; exact Real.sq_sqrt (by linarith)

theorem circP_pos {n : ℝ} (hn : n < 0) : 0 < circP n := by
  rw [circP]; exact Real.sqrt_pos.mpr (by linarith)

theorem circQ_pos {n : ℝ} (hn : n < 0) : 0 < circQ n := by
  rw [circQ]; exact Real.sqrt_pos.mpr (by linarith)

theorem circPQ_sq {n : ℝ} (hn : n < 0) : circP n ^ 2 - circQ n ^ 2 = 1 := by
  rw [circP_sq hn, circQ_sq hn]; ring

theorem circK_pos {n : ℝ} (hn : n < 0) : 0 < circK n := by
  have hp := circP_pos hn
  have hq := circQ_pos hn
  have hpq := circPQ_sq hn
  rw [circK]
  by_contra hle
  push_neg at hle
  have hnonpos : (circP n - circQ n) * (circP n + circQ n) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hle (by linarith)
  nlinarith

theorem circK_ne_zero {n : ℝ} (hn : n < 0) : circK n ≠ 0 :=
  (circK_pos hn).ne'

theorem circK_lt_one {n : ℝ} (hn : n < 0) : circK n < 1 := by
  have hp := circP_pos hn
  have hq := circQ_pos hn
  have hpq := circPQ_sq hn
  have hk := circK_pos hn
  have hsum : 0 < circP n + circQ n - 1 := by nlinarith
  have hmul : (circP n + circQ n) * circK n = 1 := by
    rw [circK]; nlinarith
  nlinarith [mul_pos hsum hk, hmul]

theorem circD_pos {c n : ℝ} (hc0 : 0 < c) (hn : n < 0) : 0 < circD c n := by
  rw [circD]; linarith

theorem circA_pos {c n : ℝ} (hc0 : 0 < c) (hc : c < 1) (hn : n < 0) :
    0 < circA c n := by
  rw [circA]
  exact div_pos (Real.sqrt_pos.mpr (mul_pos hc0 (by linarith))) (circD_pos hc0 hn)

theorem circB_pos {c n : ℝ} (hc0 : 0 < c) (hn : n < 0) : 0 < circB c n := by
  rw [circB]
  exact div_pos (mul_pos (circP_pos hn) (circQ_pos hn)) (circD_pos hc0 hn)

theorem circQ_eq {n : ℝ} (hn : n < 0) :
    circQ n = (1 - circK n ^ 2) / (2 * circK n) := by
  have hk := circK_ne_zero hn
  have hpq := circPQ_sq hn
  have hmul : (circP n + circQ n) * circK n = 1 := by rw [circK]; nlinarith
  have hsum : circP n + circQ n = 1 / circK n := by
    rw [eq_div_iff hk]; linarith
  have h2q : 2 * circQ n = 1 / circK n - circK n := by
    have hkdef : circK n = circP n - circQ n := rfl
    rw [hkdef] at hsum ⊢
    linarith
  have h2q' : 2 * circQ n * circK n = 1 - circK n ^ 2 := by
    have h := congrArg (fun z => z * circK n) h2q
    field_simp [hk] at h
    linarith [h]
  field_simp [hk]
  linarith [h2q']

theorem circP_eq {n : ℝ} (hn : n < 0) :
    circP n = (1 + circK n ^ 2) / (2 * circK n) := by
  have hk := circK_ne_zero hn
  have hpq := circPQ_sq hn
  have hmul : (circP n + circQ n) * circK n = 1 := by rw [circK]; nlinarith
  have hsum : circP n + circQ n = 1 / circK n := by
    rw [eq_div_iff hk]; linarith
  have h2p : 2 * circP n = 1 / circK n + circK n := by
    have hkdef : circK n = circP n - circQ n := rfl
    rw [hkdef] at hsum ⊢
    linarith
  have h2p' : 2 * circP n * circK n = 1 + circK n ^ 2 := by
    have h := congrArg (fun z => z * circK n) h2p
    field_simp [hk] at h
    linarith [h]
  field_simp [hk]
  linarith [h2p']

theorem circB_eq {c n : ℝ} (hn : n < 0) :
    circB c n = (1 - circK n ^ 4) / (4 * circK n ^ 2 * circD c n) := by
  have hk := circK_ne_zero hn
  rw [circB, circP_eq hn, circQ_eq hn]
  field_simp [hk]
  ring

theorem circD_eq {c n : ℝ} (hn : n < 0) :
    circD c n = c + (1 - circK n ^ 2) ^ 2 / (4 * circK n ^ 2) := by
  have hk := circK_ne_zero hn
  have hq := circQ_eq hn
  have hq2 : circQ n ^ 2 = (1 - circK n ^ 2) ^ 2 / (4 * circK n ^ 2) := by
    conv_lhs => rw [hq]
    field_simp [hk]
    ring
  have hcn : c - n = c + circQ n ^ 2 := by
    have hq2' : circQ n ^ 2 = -n := circQ_sq hn
    linarith
  rw [circD, hcn, hq2]

/-! ### The curve -/

theorem circCurve_mem_circS (c n t : ℝ) : circCurve c n t ∈ circS c n := by
  refine ⟨(t, Real.sin t), ?_, ?_⟩
  · simp
  · simp [circCurve, linearMap]

theorem circS_PConstructibleCurve {c n : ℝ} (hcP : PConstructible c)
    (hnP : PConstructible n) : PConstructibleCurve (circS c n) := by
  have hbP : PConstructible (circB c n) := by
    rw [circB]
    pconstructible
  have haP : PConstructible (circA c n) := by
    rw [circA]
    pconstructible
  exact linearMap_PConstructibleCurve PConstructibleCurve.sine (neg_Pconstructible hbP)
    PConstructible.base_one haP zero_Pconstructible

theorem deriv_circCurve_fst (c n t : ℝ) :
    deriv (fun s : ℝ => (circCurve c n s).1) t = -circB c n + Real.cos t := by
  have hfun : (fun s : ℝ => (circCurve c n s).1)
      = (fun s => -circB c n * s + Real.sin s) := by
    funext s; rfl
  have hsin : deriv (fun s : ℝ => Real.sin s) t = Real.cos t := by
    simpa using congrFun Real.deriv_sin t
  have hfun2 : (fun s : ℝ => -circB c n * s + Real.sin s)
      = (fun s => -circB c n * s) + (fun s => Real.sin s) := rfl
  rw [hfun, hfun2]
  rw [deriv_add (f := fun s : ℝ => -circB c n * s) (g := fun s : ℝ => Real.sin s)
    (differentiableAt_id.const_mul _) Real.differentiableAt_sin]
  rw [deriv_const_mul_id, hsin]

theorem deriv_circCurve_snd (c n t : ℝ) :
    deriv (fun s : ℝ => (circCurve c n s).2) t = circA c n := by
  have hfun : (fun s : ℝ => (circCurve c n s).2) = (fun s => circA c n * s) := by
    funext s; rfl
  rw [hfun, deriv_const_mul_id]

theorem speed_circCurve (c n t : ℝ) :
    speed (circCurve c n) t = Real.sqrt ((Real.cos t - circB c n) ^ 2 + circA c n ^ 2) := by
  unfold speed
  rw [deriv_circCurve_fst, deriv_circCurve_snd]
  congr 1
  ring

theorem continuous_speed_circCurve (c n : ℝ) : Continuous (speed (circCurve c n)) := by
  rw [show speed (circCurve c n) = fun t => Real.sqrt ((Real.cos t - circB c n) ^ 2 + circA c n ^ 2) from
    funext (speed_circCurve c n)]
  fun_prop

theorem differentiable_circCurve (c n t : ℝ) :
    DifferentiableAt ℝ (fun s : ℝ => (circCurve c n s).1) t ∧
      DifferentiableAt ℝ (fun s : ℝ => (circCurve c n s).2) t :=
  ⟨(by unfold circCurve; fun_prop), (by unfold circCurve; fun_prop)⟩

theorem strictMono_circCurve_snd {c n : ℝ} (hc0 : 0 < c) (hc : c < 1) (hn : n < 0) :
    StrictMono (fun t => (circCurve c n t).2) := by
  have ha := circA_pos hc0 hc hn
  intro x y hxy
  simp only [circCurve]
  nlinarith

theorem injOn_circCurve {c n : ℝ} (hc0 : 0 < c) (hc : c < 1) (hn : n < 0)
    {a b : ℝ} : Set.InjOn (circCurve c n) (Set.Icc a b) := by
  have hmono := strictMono_circCurve_snd hc0 hc hn
  intro x _ y _ hxy
  exact hmono.injective (congrArg Prod.snd hxy)

/-! ### Trigonometry of the substitution -/

theorem cos_two_arctan (x : ℝ) :
    Real.cos (2 * Real.arctan x) = (1 - x ^ 2) / (1 + x ^ 2) := by
  rw [Real.cos_two_mul, Real.cos_sq_arctan]
  field_simp
  ring

theorem sin_two_arctan (x : ℝ) :
    Real.sin (2 * Real.arctan x) = 2 * x / (1 + x ^ 2) := by
  have hpos : 0 < 1 + x ^ 2 := by positivity
  rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
  field_simp [(Real.sqrt_pos.mpr hpos).ne']
  rw [Real.sq_sqrt hpos.le]

theorem cos_eq_half_tan {θ : ℝ} (h0 : 0 ≤ θ) (hπ : θ < Real.pi) :
    Real.cos θ = (1 - Real.tan (θ / 2) ^ 2) / (1 + Real.tan (θ / 2) ^ 2) := by
  have hmem : θ / 2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  have h := cos_two_arctan (Real.tan (θ / 2))
  rw [Real.arctan_tan hmem.1 hmem.2] at h
  calc Real.cos θ = Real.cos (2 * (θ / 2)) := by congr 1; ring
    _ = (1 - Real.tan (θ / 2) ^ 2) / (1 + Real.tan (θ / 2) ^ 2) := h

theorem sin_eq_half_tan {θ : ℝ} (h0 : 0 ≤ θ) (hπ : θ < Real.pi) :
    Real.sin θ = 2 * Real.tan (θ / 2) / (1 + Real.tan (θ / 2) ^ 2) := by
  have hmem : θ / 2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  have h := sin_two_arctan (Real.tan (θ / 2))
  rw [Real.arctan_tan hmem.1 hmem.2] at h
  calc Real.sin θ = Real.sin (2 * (θ / 2)) := by congr 1; ring
    _ = 2 * Real.tan (θ / 2) / (1 + Real.tan (θ / 2) ^ 2) := h

theorem cos_circT (n θ : ℝ) :
    Real.cos (circT n θ)
      = (1 - circK n ^ 2 * Real.tan (θ / 2) ^ 2)
          / (1 + circK n ^ 2 * Real.tan (θ / 2) ^ 2) := by
  unfold circT
  rw [show 2 * Real.arctan (circK n * Real.tan (θ / 2))
      = 2 * Real.arctan (circK n * Real.tan (θ / 2)) from rfl, cos_two_arctan]
  ring

theorem sin_circT (n θ : ℝ) :
    Real.sin (circT n θ)
      = 2 * (circK n * Real.tan (θ / 2)) / (1 + circK n ^ 2 * Real.tan (θ / 2) ^ 2) := by
  unfold circT
  rw [sin_two_arctan]
  ring

theorem hasDerivAt_circT {n θ : ℝ} (h0 : 0 ≤ θ) (hπ : θ < Real.pi) :
    HasDerivAt (circT n) (circK n * (1 + Real.tan (θ / 2) ^ 2)
      / (1 + circK n ^ 2 * Real.tan (θ / 2) ^ 2)) θ := by
  have hmem : θ / 2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  have hcos : Real.cos (θ / 2) ≠ 0 := (Real.cos_pos_of_mem_Ioo hmem).ne'
  have htan : HasDerivAt (fun s : ℝ => Real.tan (s / 2))
      (1 / Real.cos (θ / 2) ^ 2 * (1 / 2)) θ := by
    have hdiv : HasDerivAt (fun s : ℝ => s / 2) (1 / 2) θ := by
      simpa using (hasDerivAt_id θ).div_const 2
    exact (Real.hasDerivAt_tan hcos).comp θ hdiv
  have hinner : HasDerivAt (fun s : ℝ => circK n * Real.tan (s / 2))
      (circK n * (1 / Real.cos (θ / 2) ^ 2 * (1 / 2))) θ :=
    htan.const_mul (circK n)
  have harctan := (Real.hasDerivAt_arctan (circK n * Real.tan (θ / 2))).comp θ hinner
  have h2 : HasDerivAt (fun s : ℝ => 2 * Real.arctan (circK n * Real.tan (s / 2)))
      (2 * (1 / (1 + (circK n * Real.tan (θ / 2)) ^ 2)
        * (circK n * (1 / Real.cos (θ / 2) ^ 2 * (1 / 2))))) θ :=
    harctan.const_mul 2
  have hfun : (fun s : ℝ => 2 * Real.arctan (circK n * Real.tan (s / 2))) = circT n := by
    funext s; rfl
  rw [hfun] at h2
  refine h2.congr_deriv ?_
  rw [Real.tan_eq_sin_div_cos]
  have hcos2 : Real.cos (θ / 2) ^ 2 ≠ 0 := pow_ne_zero 2 hcos
  field_simp
  rw [add_comm (Real.cos (θ / 2) ^ 2) (Real.sin (θ / 2) ^ 2),
    Real.sin_sq_add_cos_sq]
  ring

/-! ### The algebraic core of the substitution

All identities here are in the rational parameter `k = p - q`, where
`D = c - n = c + (1-k²)²/(4k²)`. -/

theorem circ_speed_sq_alg {c k u : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hk0 : 0 < k) :
    let D := c + (1 - k ^ 2) ^ 2 / (4 * k ^ 2)
    let b := ((k + 1 / k) / 2) * ((1 / k - k) / 2) / D
    let a2 := c * (1 - c) / D ^ 2
    ((1 - k ^ 2 * u ^ 2) / (1 + k ^ 2 * u ^ 2) - b) ^ 2 + a2
      = k ^ 2 * (1 + u ^ 2) ^ 2 * (1 - c * (2 * u / (1 + u ^ 2)) ^ 2)
          / ((c + (1 - k ^ 2) ^ 2 / (4 * k ^ 2)) * (1 + k ^ 2 * u ^ 2) ^ 2) := by
  dsimp only
  have hkne : k ≠ 0 := ne_of_gt hk0
  have hDpos : 0 < c + (1 - k ^ 2) ^ 2 / (4 * k ^ 2) := by positivity
  have hDne : c + (1 - k ^ 2) ^ 2 / (4 * k ^ 2) ≠ 0 := ne_of_gt hDpos
  field_simp
  ring

theorem circ_ratio_alg {c k u : ℝ} (hk0 : 0 < k) :
    let q := (1 / k - k) / 2
    let p := (k + 1 / k) / 2
    let w := 1 + q ^ 2 * (2 * u / (1 + u ^ 2)) ^ 2
    (p - q * ((1 - u ^ 2) / (1 + u ^ 2))) / w
      = k * (1 + u ^ 2) / (1 + k ^ 2 * u ^ 2) := by
  dsimp only
  have hkne : k ≠ 0 := ne_of_gt hk0
  field_simp
  ring

theorem circ_pointwise_alg {c k u : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hk0 : 0 < k) :
    let D := c + (1 - k ^ 2) ^ 2 / (4 * k ^ 2)
    let p := (k + 1 / k) / 2
    let q := (1 / k - k) / 2
    let b := p * q / D
    let a := Real.sqrt (c * (1 - c)) / D
    let cosT := (1 - k ^ 2 * u ^ 2) / (1 + k ^ 2 * u ^ 2)
    let sinth := 2 * u / (1 + u ^ 2)
    let costh := (1 - u ^ 2) / (1 + u ^ 2)
    let Delta := Real.sqrt (1 - c * sinth ^ 2)
    let w := 1 + q ^ 2 * sinth ^ 2
    Real.sqrt ((cosT - b) ^ 2 + a ^ 2) * (k * (1 + u ^ 2) / (1 + k ^ 2 * u ^ 2))
      = Delta * (p - q * costh) ^ 2 / (Real.sqrt D * w ^ 2) := by
  dsimp only
  have hkne : k ≠ 0 := ne_of_gt hk0
  set D : ℝ := c + (1 - k ^ 2) ^ 2 / (4 * k ^ 2) with hDdef
  have hDpos : 0 < D := by rw [hDdef]; positivity
  have hDne : D ≠ 0 := ne_of_gt hDpos
  have hp2 : 0 < c * (1 - c) := mul_pos hc0 (by linarith)
  set p : ℝ := (k + 1 / k) / 2 with hpdef
  set q : ℝ := (1 / k - k) / 2 with hqdef
  set b : ℝ := p * q / D with hbdef
  set a : ℝ := Real.sqrt (c * (1 - c)) / D with hadef
  set cosT : ℝ := (1 - k ^ 2 * u ^ 2) / (1 + k ^ 2 * u ^ 2) with hCT
  set sinth : ℝ := 2 * u / (1 + u ^ 2) with hs
  set costh : ℝ := (1 - u ^ 2) / (1 + u ^ 2) with hc
  set Delta : ℝ := Real.sqrt (1 - c * sinth ^ 2) with hDel
  set w : ℝ := 1 + q ^ 2 * sinth ^ 2 with hw
  have ha2 : a ^ 2 = c * (1 - c) / D ^ 2 := by
    rw [hadef, div_pow, Real.sq_sqrt hp2.le]
  have hsin_le : sinth ^ 2 ≤ 1 := by
    rw [hs, div_pow, div_le_one (by positivity)]
    nlinarith [sq_nonneg (u ^ 2 - 1)]
  have hDelta2 : Delta ^ 2 = 1 - c * sinth ^ 2 := by
    rw [hDel]
    exact Real.sq_sqrt (by nlinarith [hsin_le, hc0, hc1])
  have hDelta0 : 0 ≤ Delta := by rw [hDel]; positivity
  have hwpos : 0 < w := by rw [hw]; positivity
  have hspeed_sq : ((cosT - b) ^ 2 + a ^ 2)
      = k ^ 2 * (1 + u ^ 2) ^ 2 * Delta ^ 2 / (D * (1 + k ^ 2 * u ^ 2) ^ 2) := by
    have hb' : b = ((k + 1 / k) / 2) * ((1 / k - k) / 2) / D := by
      rw [hbdef, hpdef, hqdef]
    have h := circ_speed_sq_alg (c := c) (k := k) (u := u) hc0 hc1 hk0
    simp only [hDdef, hbdef, hpdef, hqdef, hCT, hs] at h
    rw [hDelta2, ha2, hb', hCT, hs]
    exact h
  have hspeed : Real.sqrt ((cosT - b) ^ 2 + a ^ 2)
      = k * (1 + u ^ 2) * Delta / (Real.sqrt D * (1 + k ^ 2 * u ^ 2)) := by
    rw [Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)]
    rw [hspeed_sq]
    field_simp
    rw [Real.sq_sqrt hDpos.le]
  have hratio := circ_ratio_alg (c := c) (k := k) (u := u) hk0
  simp only [hpdef, hqdef, hs, hc, hw] at hratio
  have hratio2 : (p - q * costh) ^ 2 / w ^ 2
      = (k * (1 + u ^ 2) / (1 + k ^ 2 * u ^ 2)) ^ 2 := by
    rw [← div_pow]
    exact congrArg (· ^ 2) hratio
  have hcalc : Delta * (p - q * costh) ^ 2 / (Real.sqrt D * w ^ 2)
      = k * (1 + u ^ 2) * Delta / (Real.sqrt D * (1 + k ^ 2 * u ^ 2))
          * (k * (1 + u ^ 2) / (1 + k ^ 2 * u ^ 2)) := by
    calc Delta * (p - q * costh) ^ 2 / (Real.sqrt D * w ^ 2)
        = Delta * ((p - q * costh) ^ 2 / w ^ 2) / Real.sqrt D := by
          field_simp
      _ = Delta * (k * (1 + u ^ 2) / (1 + k ^ 2 * u ^ 2)) ^ 2 / Real.sqrt D := by
            rw [hratio2]
      _ = k * (1 + u ^ 2) * Delta / (Real.sqrt D * (1 + k ^ 2 * u ^ 2))
            * (k * (1 + u ^ 2) / (1 + k ^ 2 * u ^ 2)) := by
            field_simp
  rw [hspeed]
  exact hcalc.symm

/-- **The substitution identity.** The arc-length element of the sheared sine curve,
pulled back by `T`, is the third-kind density at `n < 0`. -/
theorem speed_mul_deriv_circT {c n θ : ℝ} (hc0 : 0 < c) (hc : c < 1) (hn : n < 0)
    (h0 : 0 ≤ θ) (hπ : θ < Real.pi) :
    speed (circCurve c n) (circT n θ) * deriv (circT n) θ
      = ellipticEIntegrand c θ * (circP n - circQ n * Real.cos θ) ^ 2
          / (Real.sqrt (circD c n) * (1 - n * Real.sin θ ^ 2) ^ 2) := by
  have hk := circK_pos hn
  have h := circ_pointwise_alg (c := c) (k := circK n) (u := Real.tan (θ / 2)) hc0 hc hk
  dsimp only at h
  have hq' : (1 / circK n - circK n) / 2 = circQ n := by
    conv_rhs => rw [circQ_eq hn]
    field_simp [circK_ne_zero hn]
  have hP' : circP n = (circK n + 1 / circK n) / 2 := by
    conv_lhs => rw [circP_eq hn]
    field_simp [circK_ne_zero hn]
    ring
  have hQ' : circQ n = (1 / circK n - circK n) / 2 := hq'.symm
  rw [speed_circCurve, (hasDerivAt_circT h0 hπ).deriv]
  rw [cos_circT, cos_eq_half_tan h0 hπ]
  have hw : 1 - n * Real.sin θ ^ 2
      = 1 + ((1 / circK n - circK n) / 2) ^ 2 * Real.sin θ ^ 2 := by
    rw [hq']
    have hq2 := circQ_sq hn
    rw [hq2]
    ring
  rw [hw]
  simp only [circA, ellipticEIntegrand]
  rw [sin_eq_half_tan h0 hπ]
  have hb' : circB c n
      = ((circK n + 1 / circK n) / 2) * ((1 / circK n - circK n) / 2) / circD c n := by
    rw [circB_eq (c := c) hn]
    field_simp [circK_ne_zero hn]
    ring
  rw [hb', circD_eq (c := c) hn, hP', hQ']
  exact h

theorem circW_pos {n : ℝ} (hn : n < 0) (θ : ℝ) : 0 < circW n θ := by
  unfold circW
  have : n * Real.sin θ ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hn.le (sq_nonneg _)
  linarith

theorem circW_ne_zero {n : ℝ} (hn : n < 0) (θ : ℝ) : circW n θ ≠ 0 :=
  (circW_pos hn θ).ne'

theorem circDelta_pos {c : ℝ} (hc : c < 1) (θ : ℝ) : 0 < circDelta c θ := by
  unfold circDelta
  exact ellipticEIntegrand_pos hc θ

theorem circDelta_ne_zero {c : ℝ} (hc : c < 1) (θ : ℝ) : circDelta c θ ≠ 0 :=
  (circDelta_pos hc θ).ne'

theorem hasDerivAt_circDelta {c : ℝ} (hc : c < 1) (θ : ℝ) :
    HasDerivAt (circDelta c)
      (-(2 * c * Real.sin θ * Real.cos θ) / (2 * circDelta c θ)) θ := by
  unfold circDelta
  exact hasDerivAt_ellipticEIntegrand c θ (one_sub_mul_sin_sq_pos hc θ).ne'

theorem hasDerivAt_circW (n : ℝ) (θ : ℝ) :
    HasDerivAt (circW n) (-(2 * n * Real.sin θ * Real.cos θ)) θ := by
  unfold circW
  have hsin2 : HasDerivAt (fun s : ℝ => Real.sin s ^ 2)
      (2 * Real.sin θ * Real.cos θ) θ :=
    ((Real.hasDerivAt_sin θ).pow 2).congr_deriv (by ring)
  exact ((hasDerivAt_const (x := θ) (1 : ℝ)).sub (hsin2.const_mul n)).congr_deriv (by ring)

theorem hasDerivAt_circY {c n : ℝ} (hc : c < 1) (θ : ℝ) :
    HasDerivAt (circY c n)
      ((Real.sqrt (circD c n) * Real.cos θ * circDelta c θ
          - Real.sqrt (circD c n) * Real.sin θ
            * (-(2 * c * Real.sin θ * Real.cos θ) / (2 * circDelta c θ)))
        / circDelta c θ ^ 2) θ := by
  unfold circY
  have hnum : HasDerivAt (fun s : ℝ => Real.sqrt (circD c n) * Real.sin s)
      (Real.sqrt (circD c n) * Real.cos θ) θ :=
    (Real.hasDerivAt_sin θ).const_mul (Real.sqrt (circD c n))
  exact hnum.div (hasDerivAt_circDelta hc θ) (circDelta_ne_zero hc θ)

theorem hasDerivAt_ellipticPiInc {c n : ℝ} (hc : c < 1) (hn : n < 1) (θ : ℝ) :
    HasDerivAt (ellipticPiInc c n) (ellipticPiIntegrand c n θ) θ := by
  have hcont := continuous_ellipticPiIntegrand hc hn
  have h := (hcont.integral_hasStrictDerivAt 0 θ).hasDerivAt
  change HasDerivAt (fun u => ∫ x in (0 : ℝ)..u, ellipticPiIntegrand c n x)
    (ellipticPiIntegrand c n θ) θ
  exact h

/-- The derivative of the antiderivative `circG`. -/
theorem hasDerivAt_circG {c n : ℝ} (hc0 : 0 < c) (hc : c < 1) (hn : n < 0) (θ : ℝ) :
    HasDerivAt (circG c n)
      (ellipticEIntegrand c θ * (circP n - circQ n * Real.cos θ) ^ 2
        / (Real.sqrt (circD c n) * (1 - n * Real.sin θ ^ 2) ^ 2)) θ := by
  have hΔ := hasDerivAt_circDelta hc θ
  have hW := hasDerivAt_circW n θ
  have hY := hasDerivAt_circY (n := n) hc θ
  have hAprod := ((Real.hasDerivAt_sin θ).mul (Real.hasDerivAt_cos θ)).mul hΔ
  have hAquot := hAprod.div hW (circW_ne_zero hn θ)
  have hA := hAquot.const_mul (-n)
  have harctan := (Real.hasDerivAt_arctan (circY c n θ)).comp θ hY
  have hBprod := (Real.hasDerivAt_sin θ).mul hΔ
  have hBquot := hBprod.div hW (circW_ne_zero hn θ)
  have hsum := hBquot.add (harctan.div_const (Real.sqrt (circD c n)))
  have hB := hsum.const_mul (-(circP n * circQ n))
  have hElem0 := hA.add hB
  have hEF := (hasDerivAt_ellipticE c θ).sub (hasDerivAt_ellipticF hc θ)
  have hPi := (hasDerivAt_ellipticPiInc hc (by linarith : n < 1) θ).const_mul (1 - n)
  have htotal := ((hEF.add hPi).add hElem0).div_const (Real.sqrt (circD c n))
  refine (htotal.congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Filter.EventuallyEq.of_eq (by
      funext s
      simp only [circG, circElem, circDelta, circW, Pi.add_apply, Pi.sub_apply,
        Pi.mul_apply, Pi.div_apply, Function.comp_apply]
      ring_nf)
  · simp only [circDelta, circW, circY, ellipticEIntegrand, ellipticFIntegrand,
      ellipticPiIntegrand, circP, circQ, circD, Pi.add_apply, Pi.sub_apply,
      Pi.mul_apply, Pi.div_apply]
    have hsin := Real.sin_sq_add_cos_sq θ
    have hsinle : Real.sin θ ^ 2 ≤ 1 := Real.sin_sq_le_one θ
    set U : ℝ := Real.sqrt (1 - c * Real.sin θ ^ 2) with hU
    set V : ℝ := Real.sqrt (1 - n) with hV
    set W : ℝ := Real.sqrt (-n) with hW
    set X : ℝ := Real.sqrt (c - n) with hX
    have hU2 : U ^ 2 = 1 - c * Real.sin θ ^ 2 := by
      rw [hU]; exact Real.sq_sqrt (by nlinarith [hsinle, hc0, hc])
    have hV2 : V ^ 2 = 1 - n := by rw [hV]; exact Real.sq_sqrt (by linarith)
    have hW2 : W ^ 2 = -n := by rw [hW]; exact Real.sq_sqrt (by linarith)
    have hX2 : X ^ 2 = c - n := by rw [hX]; exact Real.sq_sqrt (by linarith)
    have hUpos : 0 < U := by rw [hU]; exact Real.sqrt_pos.mpr (by nlinarith [hsinle, hc0, hc])
    have hVpos : 0 < V := by rw [hV]; exact Real.sqrt_pos.mpr (by linarith)
    have hWpos : 0 < W := by rw [hW]; exact Real.sqrt_pos.mpr (by linarith)
    have hXpos : 0 < X := by rw [hX]; exact Real.sqrt_pos.mpr (by linarith)
    have hwpos : 0 < 1 - n * Real.sin θ ^ 2 := by
      have : n * Real.sin θ ^ 2 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hn.le (sq_nonneg _)
      linarith
    have hUinv : U⁻¹ = U / (1 - c * Real.sin θ ^ 2) := by
      have hden : 1 - c * Real.sin θ ^ 2 ≠ 0 := by
        nlinarith [hsinle, hc0, hc]
      rw [eq_div_iff hden]
      field_simp [hUpos.ne']
      rw [hU2]
    have hVW : (V * W) ^ 2 = (1 - n) * (-n) := by rw [mul_pow, hV2, hW2]
    have hwpos' : 1 - Real.sin θ ^ 2 * n ≠ 0 := by
      rw [mul_comm]; exact hwpos.ne'
    rw [hUinv]
    field_simp [hUpos.ne', hVpos.ne', hWpos.ne', hXpos.ne', hwpos.ne', hwpos',
      (by nlinarith [hsinle, hc0, hc] : 1 - c * Real.sin θ ^ 2 ≠ 0)]
    field_simp [hUpos.ne', hVpos.ne', hWpos.ne', hXpos.ne', hwpos.ne', hwpos',
      (by nlinarith [hsinle, hc0, hc] : 1 - c * Real.sin θ ^ 2 ≠ 0)]
    have hU4 : U ^ 4 = (1 - c * Real.sin θ ^ 2) ^ 2 := by
      rw [show U ^ 4 = (U ^ 2) ^ 2 by ring, hU2]
    have hcos2 : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by linarith [hsin]
    have hVdiff : V ^ 2 - W ^ 2 = 1 := by rw [hV2, hW2]; ring
    ring_nf
    rw [show W ^ 2 = V ^ 2 - 1 by linarith [hVdiff],
      show V ^ 2 = 1 - n by linarith [hV2], hU4, hU2, hX2, hcos2]
    ring_nf

theorem circT_zero (n : ℝ) : circT n 0 = 0 := by
  simp [circT]

theorem circG_zero (c n : ℝ) : circG c n 0 = 0 := by
  simp [circG, circElem, circW, circDelta, circY, ellipticE, ellipticF, ellipticPiInc]

/-- The antiderivative is the arc length of the sheared sine curve. -/
theorem arcLength_circ_eq {c n θ : ℝ} (hc0 : 0 < c) (hc : c < 1) (hn : n < 0)
    (h0 : 0 ≤ θ) (hπ : θ < Real.pi) :
    arcLengthOf (circCurve c n) 0 (circT n θ) = circG c n θ := by
  have hk := circK_pos hn
  have hcontTan : ContinuousOn (fun ψ : ℝ => Real.tan (ψ / 2)) (Set.Icc 0 θ) := by
    have h1 : ContinuousOn Real.tan (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :=
      Real.continuousOn_tan_Ioo
    have h2 : ContinuousOn (fun ψ : ℝ => ψ / 2) (Set.Icc 0 θ) := by fun_prop
    refine h1.comp h2 ?_
    intro ψ hψ
    constructor <;> linarith [hψ.1, hψ.2, Real.pi_pos, hπ]
  have hcontT : ContinuousOn (circT n) (Set.Icc 0 θ) := by
    unfold circT
    exact ((Real.continuous_arctan.continuousOn.comp
      (hcontTan.const_mul (circK n)) (fun _ _ => Set.mem_univ _)).const_mul 2)
  let f' : ℝ → ℝ := fun ψ => circK n * (1 + Real.tan (ψ / 2) ^ 2)
    / (1 + circK n ^ 2 * Real.tan (ψ / 2) ^ 2)
  have hderiv : ∀ ψ ∈ Set.Ioo (min 0 θ) (max 0 θ), HasDerivAt (circT n) (f' ψ) ψ := by
    intro ψ hψ
    have hψ0 : 0 ≤ ψ := by
      have := hψ.1; rw [min_eq_left h0] at this; exact this.le
    have hψπ : ψ < Real.pi := by
      have := hψ.2; rw [max_eq_right h0] at this; linarith
    exact hasDerivAt_circT hψ0 hψπ
  have hnonneg : ∀ ψ ∈ Set.Ioo (min 0 θ) (max 0 θ), 0 ≤ f' ψ := by
    intro ψ _
    have hden : 0 < 1 + circK n ^ 2 * Real.tan (ψ / 2) ^ 2 := by positivity
    have hnum : 0 ≤ circK n * (1 + Real.tan (ψ / 2) ^ 2) := by positivity
    exact div_nonneg hnum hden.le
  have hkey := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
    (a := (0 : ℝ)) (b := θ) (f := circT n) (f' := f') (g := speed (circCurve c n))
    (by simpa [Set.uIcc_of_le h0] using hcontT) hderiv hnonneg
  rw [circT_zero] at hkey
  rw [arcLengthOf, ← hkey]
  simp only [Function.comp_apply]
  have hcongr : (∫ ψ in (0 : ℝ)..θ, f' ψ • speed (circCurve c n) (circT n ψ))
      = ∫ ψ in (0 : ℝ)..θ,
          ellipticEIntegrand c ψ * (circP n - circQ n * Real.cos ψ) ^ 2
            / (Real.sqrt (circD c n) * (1 - n * Real.sin ψ ^ 2) ^ 2) := by
    refine intervalIntegral.integral_congr fun ψ hψ => ?_
    rw [Set.uIcc_of_le h0] at hψ
    have hψ0 : 0 ≤ ψ := hψ.1
    have hψπ : ψ < Real.pi := by linarith [hψ.2]
    have hder : f' ψ = deriv (circT n) ψ := (hasDerivAt_circT hψ0 hψπ).deriv.symm
    rw [smul_eq_mul, hder, mul_comm]
    exact speed_mul_deriv_circT hc0 hc hn hψ0 hψπ
  rw [hcongr]
  have hint : IntervalIntegrable (fun ψ : ℝ =>
      ellipticEIntegrand c ψ * (circP n - circQ n * Real.cos ψ) ^ 2
        / (Real.sqrt (circD c n) * (1 - n * Real.sin ψ ^ 2) ^ 2))
      MeasureTheory.volume 0 θ := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.div ?_ ?_ ?_
    · exact (continuous_ellipticEIntegrand c).continuousOn.mul
        ((Continuous.continuousOn (by fun_prop : Continuous fun ψ : ℝ =>
          circP n - circQ n * Real.cos ψ)).pow 2)
    · exact continuousOn_const.mul
        ((Continuous.continuousOn (by fun_prop)).pow 2)
    · intro ψ _
      exact mul_ne_zero (Real.sqrt_pos.mpr (circD_pos hc0 hn)).ne'
        (pow_ne_zero 2 (circW_ne_zero hn ψ))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun ψ _ => hasDerivAt_circG hc0 hc hn ψ) hint
  rw [hFTC, circG_zero, sub_zero]

/-- Solving the arc-length identity for the incomplete third-kind integral. -/
theorem ellipticPiInc_eq_circ {c n θ : ℝ} (hc0 : 0 < c) (hc : c < 1) (hn : n < 0)
    (h0 : 0 ≤ θ) (hπ : θ < Real.pi) :
    ellipticPiInc c n θ
      = (Real.sqrt (circD c n) * arcLengthOf (circCurve c n) 0 (circT n θ)
          - ellipticE c θ + ellipticF c θ
          + n * Real.sin θ * Real.cos θ * ellipticEIntegrand c θ
              / (1 - n * Real.sin θ ^ 2)
          + circP n * circQ n *
              (Real.sin θ * ellipticEIntegrand c θ / (1 - n * Real.sin θ ^ 2)
                + Real.arctan (circY c n θ) / Real.sqrt (circD c n))) / (1 - n) := by
  have hA := arcLength_circ_eq hc0 hc hn h0 hπ
  have hn1 : (1 : ℝ) - n ≠ 0 := by linarith
  rw [eq_div_iff hn1]
  unfold circG at hA
  rw [eq_div_iff (Real.sqrt_pos.mpr (circD_pos hc0 hn)).ne'] at hA
  unfold circElem at hA
  simp only [circDelta, circW] at hA
  linear_combination -hA

@[pconstructible]
theorem circK_Pconstructible {n : ℝ} (hnP : PConstructible n) : PConstructible (circK n) := by
  rw [circK]
  pconstructible

@[pconstructible]
theorem circA_Pconstructible {c n : ℝ} (hcP : PConstructible c)
    (hnP : PConstructible n) : PConstructible (circA c n) := by
  rw [circA]
  pconstructible

@[pconstructible]
theorem circB_Pconstructible {c n : ℝ} (hcP : PConstructible c)
    (hnP : PConstructible n) : PConstructible (circB c n) := by
  rw [circB]
  pconstructible

@[pconstructible]
theorem circT_Pconstructible {n θ : ℝ} (hnP : PConstructible n)
    (hθP : PConstructible θ) : PConstructible (circT n θ) := by
  unfold circT
  pconstructible

theorem ellipticPiInc_Pconstructible_neg_Ico {c n θ : ℝ} (hcP : PConstructible c)
    (hnP : PConstructible n) (hθP : PConstructible θ) (hc0 : 0 < c) (hc : c < 1)
    (hn : n < 0) (h0 : 0 ≤ θ) (hπ : θ < Real.pi) :
    PConstructible (ellipticPiInc c n θ) := by
  rw [ellipticPiInc_eq_circ hc0 hc hn h0 hπ]
  have hT : PConstructible (circT n θ) := circT_Pconstructible hnP hθP
  have hTnn : 0 ≤ circT n θ := by
    unfold circT
    have hk : 0 ≤ circK n := (circK_pos hn).le
    have htan : 0 ≤ Real.tan (θ / 2) :=
      Real.tan_nonneg_of_nonneg_of_le_pi_div_two (by linarith) (by linarith [Real.pi_pos, hπ])
    have h1 : 0 ≤ circK n * Real.tan (θ / 2) := mul_nonneg hk htan
    have h2 : 0 ≤ Real.arctan (circK n * Real.tan (θ / 2)) := Real.arctan_nonneg.mpr h1
    linarith
  have hArc : PConstructible (arcLengthOf (circCurve c n) 0 (circT n θ)) := by
    refine PConstructible.arc_length (a := (0 : ℝ)) (b := circT n θ)
      (circS_PConstructibleCurve hcP hnP) (circCurve c n) hTnn
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rintro p ⟨t, _, rfl⟩
      exact circCurve_mem_circS c n t
    · exact injOn_circCurve hc0 hc hn
    · intro t _
      exact differentiable_circCurve c n t
    · exact (continuous_speed_circCurve c n).intervalIntegrable 0 (circT n θ)
    · simpa [circCurve] using zero_Pconstructible
    · simpa [circCurve] using zero_Pconstructible
    · simp only [circCurve]
      pconstructible
    · simp only [circCurve]
      pconstructible
  have hE : PConstructible (ellipticE c θ) := ellipticE_Pconstructible hcP hθP hc
  have hF : PConstructible (ellipticF c θ) := ellipticF_Pconstructible hcP hθP hc
  have hDel : PConstructible (ellipticEIntegrand c θ) :=
    ellipticEIntegrand_Pconstructible hcP hθP
  have hY : PConstructible (circY c n θ) := by
    unfold circY circDelta
    pconstructible
  pconstructible

/-- **The incomplete third-kind integral at negative characteristic** is P-constructible,
for every real upper limit. -/
theorem ellipticPiInc_Pconstructible_neg {c n Φ : ℝ} (hcP : PConstructible c)
    (hnP : PConstructible n) (hΦP : PConstructible Φ) (hc0 : 0 < c) (hc : c < 1)
    (hn : n < 0) : PConstructible (ellipticPiInc c n Φ) :=
  ellipticPiInc_Pconstructible_of_base hcP hnP hΦP hc0 hc (by linarith) fun θ hθP h0 hlt =>
    ellipticPiInc_Pconstructible_neg_Ico hcP hnP hθP hc0 hc hn h0
      (by linarith [Real.pi_pos])

end Pconstructible
