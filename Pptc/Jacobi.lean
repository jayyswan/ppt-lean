/- Copyright (c) 2024 Lean Community. All rights reserved.

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

import Pptc.Basic

/-! # Pptc.Jacobi

Inverting the Legendre integrals: the Jacobi amplitude and `sn`, `cn`, `dn`, and the
arc-length parametrization of the ellipse.
-/

namespace Pconstructible

section Inversion

/-! ### Inverting an increasing antiderivative

Both Legendre integrals are `∫₀^φ` of a continuous integrand bounded away from `0` and
`∞`, so both are strictly increasing bijections of the line onto itself. Proved once here
in terms of the derivative and used twice below. -/

-- Theorem: a function whose derivative is everywhere positive is strictly monotone.
theorem strictMono_of_hasDerivAt_pos {f g : ℝ → ℝ}
    (hf : ∀ φ, HasDerivAt f (g φ) φ) (hpos : ∀ θ, 0 < g θ) : StrictMono f :=
  strictMono_of_deriv_pos fun x => by rw [(hf x).deriv]; exact hpos x

-- Theorem: a derivative bounded below by `d` forces the function away from `0` at least
-- as fast as the line of slope `d` does, on both sides of the origin.
theorem mul_le_of_hasDerivAt_ge {f g : ℝ → ℝ} {d : ℝ}
    (hf : ∀ φ, HasDerivAt f (g φ) φ) (hg : ∀ θ, d ≤ g θ) (hf0 : f 0 = 0) (φ : ℝ) :
    (0 ≤ φ → d * φ ≤ f φ) ∧ (φ ≤ 0 → f φ ≤ d * φ) := by
  have hd : ∀ x : ℝ, HasDerivAt (fun φ => f φ - d * φ) (g x - d) x := fun x =>
    (hf x).sub (by simpa using (hasDerivAt_id x).const_mul d)
  have hmono : Monotone fun φ => f φ - d * φ := by
    refine monotone_of_deriv_nonneg (fun x => (hd x).differentiableAt) fun x => ?_
    rw [(hd x).deriv]
    linarith [hg x]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := hmono h
    simp only [hf0, mul_zero, sub_zero] at this
    linarith
  · have := hmono h
    simp only [hf0, mul_zero, sub_zero] at this
    linarith

-- Theorem: such a function is onto, by the intermediate value theorem between the two
-- points where the line of slope `d` has already passed the target.
theorem surjective_of_hasDerivAt_ge {f g : ℝ → ℝ} {d : ℝ} (hd : 0 < d)
    (hf : ∀ φ, HasDerivAt f (g φ) φ) (hg : ∀ θ, d ≤ g θ) (hf0 : f 0 = 0) :
    Function.Surjective f := by
  have hcont : Continuous f := by
    have : Differentiable ℝ f := fun x => (hf x).differentiableAt
    exact this.continuous
  intro u
  have key := mul_le_of_hasDerivAt_ge hf hg hf0
  rcases le_total 0 u with hu | hu
  · have hb : 0 ≤ u / d := by positivity
    have h₁ : u ≤ f (u / d) := by
      have := (key (u / d)).1 hb
      rwa [mul_div_cancel₀ _ hd.ne'] at this
    have := intermediate_value_Icc hb (hcont.continuousOn)
    obtain ⟨φ, -, hφ⟩ := this (Set.mem_Icc.mpr ⟨by rw [hf0]; exact hu, h₁⟩)
    exact ⟨φ, hφ⟩
  · have hb : u / d ≤ 0 := div_nonpos_of_nonpos_of_nonneg hu hd.le
    have h₁ : f (u / d) ≤ u := by
      have := (key (u / d)).2 hb
      rwa [mul_div_cancel₀ _ hd.ne'] at this
    have := intermediate_value_Icc hb (hcont.continuousOn)
    obtain ⟨φ, -, hφ⟩ := this (Set.mem_Icc.mpr ⟨h₁, by rw [hf0]; exact hu⟩)
    exact ⟨φ, hφ⟩

end Inversion

section Amplitude

/-! ### The Legendre integrals are bijections of the line

For `c < 1` the second-kind integrand `Δ(θ) = √(1 - c sin²θ)` lies between the two
positive constants `√(min 1 (1 - c))` and `√(max 1 (1 - c))`, since `sin²θ` runs over
`[0, 1]` and the two ends of that range give `1` and `1 - c` in one order or the other.
The first-kind integrand is its reciprocal, so it is caught between the same two constants
inverted. Both integrals therefore increase strictly and without bound in both directions:
each is a bijection `ℝ → ℝ`, and so each has a genuine inverse function. -/

-- Theorem: the second-kind integrand is bounded below by a positive constant.
theorem ellipticEIntegrand_ge (c θ : ℝ) :
    Real.sqrt (min 1 (1 - c)) ≤ ellipticEIntegrand c θ := by
  refine Real.sqrt_le_sqrt ?_
  rcases le_total c 0 with h | h
  · nlinarith [min_le_left (1 : ℝ) (1 - c), sq_nonneg (Real.sin θ)]
  · nlinarith [min_le_right (1 : ℝ) (1 - c), Real.sin_sq_le_one θ]

-- Theorem: and above by another.
theorem ellipticEIntegrand_le (c θ : ℝ) :
    ellipticEIntegrand c θ ≤ Real.sqrt (max 1 (1 - c)) := by
  refine Real.sqrt_le_sqrt ?_
  rcases le_total c 0 with h | h
  · nlinarith [le_max_right (1 : ℝ) (1 - c), Real.sin_sq_le_one θ]
  · nlinarith [le_max_left (1 : ℝ) (1 - c), sq_nonneg (Real.sin θ)]

theorem sqrt_min_pos {c : ℝ} (hc : c < 1) : 0 < Real.sqrt (min 1 (1 - c)) :=
  Real.sqrt_pos.mpr (lt_min one_pos (by linarith))

theorem sqrt_max_pos (c : ℝ) : 0 < Real.sqrt (max 1 (1 - c)) :=
  Real.sqrt_pos.mpr (lt_max_of_lt_left one_pos)

-- Theorem: the first-kind integrand is bounded below by the reciprocal of that bound.
theorem ellipticFIntegrand_ge {c : ℝ} (hc : c < 1) (θ : ℝ) :
    (Real.sqrt (max 1 (1 - c)))⁻¹ ≤ ellipticFIntegrand c θ := by
  rw [ellipticFIntegrand]
  exact inv_anti₀ (ellipticEIntegrand_pos hc θ) (ellipticEIntegrand_le c θ)

-- Theorem: `E` is strictly increasing.
theorem strictMono_ellipticE {c : ℝ} (hc : c < 1) : StrictMono (ellipticE c) :=
  strictMono_of_hasDerivAt_pos (hasDerivAt_ellipticE c) (ellipticEIntegrand_pos hc)

-- Theorem: `F` is strictly increasing.
theorem strictMono_ellipticF {c : ℝ} (hc : c < 1) : StrictMono (ellipticF c) :=
  strictMono_of_hasDerivAt_pos (hasDerivAt_ellipticF hc) (ellipticFIntegrand_pos hc)

theorem ellipticE_zero_right (c : ℝ) : ellipticE c 0 = 0 := by simp [ellipticE]

theorem ellipticF_zero_right (c : ℝ) : ellipticF c 0 = 0 := by simp [ellipticF]

-- Theorem: `E` is onto.
theorem surjective_ellipticE {c : ℝ} (hc : c < 1) : Function.Surjective (ellipticE c) :=
  surjective_of_hasDerivAt_ge (sqrt_min_pos hc) (hasDerivAt_ellipticE c)
    (ellipticEIntegrand_ge c) (ellipticE_zero_right c)

-- Theorem: `F` is onto.
theorem surjective_ellipticF {c : ℝ} (hc : c < 1) : Function.Surjective (ellipticF c) :=
  surjective_of_hasDerivAt_ge (inv_pos.mpr (sqrt_max_pos c)) (hasDerivAt_ellipticF hc)
    (ellipticFIntegrand_ge hc) (ellipticF_zero_right c)

end Amplitude

section Jacobi

/-! ### The Jacobi amplitude and `sn`, `cn`, `dn`

`F(·, c)` being a bijection of the line, it has an inverse: the **amplitude** `am(u, c)`,
the angle whose first-kind integral is `u`. The three Jacobi elliptic functions are the
three natural quantities attached to that angle,

  `sn = sin am`,  `cn = cos am`,  `dn = Δ(am) = √(1 - c sin²am)`,

so that `sn² + cn² = 1` and `dn² = 1 - c sn²` are restatements of the Pythagorean identity
and of the definition of `Δ`. At `c = 0` the integral is `F(φ) = φ`, the amplitude is the
identity, and `sn`, `cn`, `dn` degenerate to `sin`, `cos`, `1`.

The definitions are by inversion rather than by the differential equations `sn' = cn dn`
etc. Inversion is the shorter road from what this file already has, and it is the
definition Legendre and Jacobi give; the differential equations then follow from the
derivative of `F`, which is `hasDerivAt_ellipticF`. -/

/-- The Jacobi amplitude: the inverse of `φ ↦ F(φ, c)`. For `c < 1` that map is a
bijection of the line (`strictMono_ellipticF`, `surjective_ellipticF`), so the inverse is
genuine; for `c ≥ 1` the integrand is not everywhere real and this is a junk value. -/
noncomputable def jacobiAm (c u : ℝ) : ℝ := Function.invFun (ellipticF c) u

/-- `sn(u, c) = sin (am (u, c))`. -/
noncomputable def jacobiSn (c u : ℝ) : ℝ := Real.sin (jacobiAm c u)

/-- `cn(u, c) = cos (am (u, c))`. -/
noncomputable def jacobiCn (c u : ℝ) : ℝ := Real.cos (jacobiAm c u)

/-- `dn(u, c) = Δ(am (u, c)) = √(1 - c sn²(u, c))`. -/
noncomputable def jacobiDn (c u : ℝ) : ℝ := ellipticEIntegrand c (jacobiAm c u)

-- Theorem: the amplitude undoes `F` on the right.
theorem ellipticF_jacobiAm {c : ℝ} (hc : c < 1) (u : ℝ) :
    ellipticF c (jacobiAm c u) = u :=
  Function.invFun_eq (surjective_ellipticF hc u)

-- Theorem: and on the left.
theorem jacobiAm_ellipticF {c : ℝ} (hc : c < 1) (φ : ℝ) :
    jacobiAm c (ellipticF c φ) = φ :=
  Function.leftInverse_invFun (strictMono_ellipticF hc).injective φ

-- Theorem: the amplitude is determined by the equation it solves.
theorem jacobiAm_eq_of_ellipticF_eq {c u φ : ℝ} (hc : c < 1) (h : ellipticF c φ = u) :
    jacobiAm c u = φ := by
  rw [← h, jacobiAm_ellipticF hc]

theorem jacobiAm_zero {c : ℝ} (hc : c < 1) : jacobiAm c 0 = 0 :=
  jacobiAm_eq_of_ellipticF_eq hc (ellipticF_zero_right c)

theorem jacobiSn_zero {c : ℝ} (hc : c < 1) : jacobiSn c 0 = 0 := by
  simp [jacobiSn, jacobiAm_zero hc]

theorem jacobiCn_zero {c : ℝ} (hc : c < 1) : jacobiCn c 0 = 1 := by
  simp [jacobiCn, jacobiAm_zero hc]

theorem jacobiDn_zero {c : ℝ} (hc : c < 1) : jacobiDn c 0 = 1 := by
  simp [jacobiDn, jacobiAm_zero hc, ellipticEIntegrand]

-- Theorem: at `c = 0` the amplitude is the identity and the three functions collapse.
theorem jacobiAm_zero_param (u : ℝ) : jacobiAm 0 u = u :=
  jacobiAm_eq_of_ellipticF_eq zero_lt_one (ellipticF_zero u)

-- Theorem: the Pythagorean identity `sn² + cn² = 1`.
theorem jacobiSn_sq_add_jacobiCn_sq (c u : ℝ) :
    jacobiSn c u ^ 2 + jacobiCn c u ^ 2 = 1 :=
  Real.sin_sq_add_cos_sq _

-- Theorem: `dn² = 1 - c sn²`, the definition of `Δ` read through the amplitude.
theorem jacobiDn_sq {c : ℝ} (hc : c < 1) (u : ℝ) :
    jacobiDn c u ^ 2 = 1 - c * jacobiSn c u ^ 2 :=
  ellipticEIntegrand_sq hc _

-- Theorem: `dn` is positive, being a square root of a positive number.
theorem jacobiDn_pos {c : ℝ} (hc : c < 1) (u : ℝ) : 0 < jacobiDn c u :=
  ellipticEIntegrand_pos hc _

-- Theorem: the amplitude is odd, since `F` is.
theorem jacobiAm_neg {c : ℝ} (hc : c < 1) (u : ℝ) :
    jacobiAm c (-u) = -jacobiAm c u :=
  jacobiAm_eq_of_ellipticF_eq hc (by rw [ellipticF_neg, ellipticF_jacobiAm hc])

-- Theorem: so `sn` is odd and `cn`, `dn` are even.
theorem jacobiSn_neg {c : ℝ} (hc : c < 1) (u : ℝ) : jacobiSn c (-u) = -jacobiSn c u := by
  simp [jacobiSn, jacobiAm_neg hc]

theorem jacobiCn_neg {c : ℝ} (hc : c < 1) (u : ℝ) : jacobiCn c (-u) = jacobiCn c u := by
  simp [jacobiCn, jacobiAm_neg hc]

theorem jacobiDn_neg {c : ℝ} (hc : c < 1) (u : ℝ) : jacobiDn c (-u) = jacobiDn c u := by
  simp [jacobiDn, jacobiAm_neg hc, ellipticEIntegrand]

-- Theorem: `am` advances by a half turn each time `u` advances by `F(π)`, that is, by two
-- quarter periods `2K`. This is the quasi-periodicity of the Jacobi functions.
theorem jacobiAm_add_int_mul {c : ℝ} (hc : c < 1) (u : ℝ) (n : ℤ) :
    jacobiAm c (u + n * ellipticF c Real.pi) = jacobiAm c u + n * Real.pi := by
  refine jacobiAm_eq_of_ellipticF_eq hc ?_
  rw [ellipticF_add_int_mul_pi hc, ellipticF_jacobiAm hc]

-- Theorem: the value of `sn` at an argument that is *presented* as a first-kind integral
-- is the sine of the angle presenting it. This is the forward direction, and with
-- `ellipticF_Pconstructible` it makes `sn` P-constructible on the whole image of the
-- P-constructible angles under `F`.
theorem jacobiSn_ellipticF {c : ℝ} (hc : c < 1) (φ : ℝ) :
    jacobiSn c (ellipticF c φ) = Real.sin φ := by
  rw [jacobiSn, jacobiAm_ellipticF hc]

theorem jacobiCn_ellipticF {c : ℝ} (hc : c < 1) (φ : ℝ) :
    jacobiCn c (ellipticF c φ) = Real.cos φ := by
  rw [jacobiCn, jacobiAm_ellipticF hc]

theorem jacobiDn_ellipticF {c : ℝ} (hc : c < 1) (φ : ℝ) :
    jacobiDn c (ellipticF c φ) = ellipticEIntegrand c φ := by
  rw [jacobiDn, jacobiAm_ellipticF hc]

end Jacobi
section JacobiConstructibility

/-! ### The four functions stand or fall together

`am` gives `sn`, `cn` and `dn` by a sine, a cosine and a square root, and any one of the
three gives `am` back. `cn` does it through `arccos`, after reducing the amplitude modulo
a full turn; `sn` and `dn` do it through `cn`, and the sign ambiguity of the square root
costs nothing, since both signs are P-constructible and the true value is one of them.

So there is one question here and not four, and it is whether the amplitude — the inverse
of `F` — is P-constructible. -/

-- Theorem: `sn` is P-constructible wherever the amplitude is.
theorem jacobiSn_Pconstructible_of_am {c u : ℝ} (h : PConstructible (jacobiAm c u)) :
    PConstructible (jacobiSn c u) :=
  sin_Pconstructible h

-- Theorem: and so is `cn`.
theorem jacobiCn_Pconstructible_of_am {c u : ℝ} (h : PConstructible (jacobiAm c u)) :
    PConstructible (jacobiCn c u) :=
  cos_Pconstructible h

-- Theorem: and so is `dn`, the parameter being P-constructible.
theorem jacobiDn_Pconstructible_of_am {c u : ℝ} (hcP : PConstructible c)
    (h : PConstructible (jacobiAm c u)) : PConstructible (jacobiDn c u) :=
  ellipticEIntegrand_Pconstructible hcP h

-- Theorem: conversely the amplitude is P-constructible as soon as `cn` is.
--
-- Reduction modulo `2π` first: the residue `r` of `am` lies in `[0, 2π)` and has the same
-- cosine, so it is either `arccos (cn u)` or `2π - arccos (cn u)` according to which half
-- of the turn it falls in, and `am = r + n · 2π`. Note that nothing is assumed about `u`.
theorem jacobiAm_Pconstructible_of_cn {c u : ℝ} (h : PConstructible (jacobiCn c u)) :
    PConstructible (jacobiAm c u) := by
  obtain ⟨n, h0, h2⟩ := exists_int_turns (jacobiAm c u)
  have hcos : Real.cos (jacobiAm c u - n * (2 * Real.pi)) = jacobiCn c u :=
    Real.cos_sub_int_mul_two_pi _ n
  have harc : PConstructible (Real.arccos (jacobiCn c u)) :=
    arccos_Pconstructible_of_mem_Icc h (Real.neg_one_le_cos _) (Real.cos_le_one _)
  have hturn : PConstructible ((n : ℝ) * (2 * Real.pi)) :=
    PConstructible.mul (int_Pconstructible n)
      (PConstructible.mul two_Pconstructible pi_Pconstructible)
  have hres : PConstructible (jacobiAm c u - n * (2 * Real.pi)) := by
    rcases le_total (jacobiAm c u - n * (2 * Real.pi)) Real.pi with hle | hle
    · rw [show jacobiAm c u - n * (2 * Real.pi) = Real.arccos (jacobiCn c u) from by
        rw [← hcos, Real.arccos_cos h0 hle]]
      exact harc
    · have hrefl : Real.arccos (jacobiCn c u)
          = 2 * Real.pi - (jacobiAm c u - n * (2 * Real.pi)) := by
        rw [← hcos, ← Real.cos_two_pi_sub]
        exact Real.arccos_cos (by linarith) (by linarith)
      rw [show jacobiAm c u - n * (2 * Real.pi)
          = 2 * Real.pi - Real.arccos (jacobiCn c u) from by rw [hrefl]; ring]
      exact PConstructible.sub
        (PConstructible.mul two_Pconstructible pi_Pconstructible) harc
  have hsplit : jacobiAm c u = (jacobiAm c u - n * (2 * Real.pi)) + n * (2 * Real.pi) := by
    ring
  rw [hsplit]
  exact PConstructible.add hres hturn

-- Theorem: `cn` is P-constructible as soon as `sn` is. Both square roots of `1 - sn²` are
-- P-constructible and `cn` is one of them, so the unknown sign is free.
theorem jacobiCn_Pconstructible_of_sn {c u : ℝ} (h : PConstructible (jacobiSn c u)) :
    PConstructible (jacobiCn c u) := by
  have hsq : 1 - jacobiSn c u ^ 2 = jacobiCn c u ^ 2 := by
    have := jacobiSn_sq_add_jacobiCn_sq c u
    linarith
  have hroot : PConstructible (Real.sqrt (1 - jacobiSn c u ^ 2)) :=
    sqrt_Pconstructible (PConstructible.sub PConstructible.base_one (sq_Pconstructible h))
  rcases le_total 0 (jacobiCn c u) with hpos | hneg
  · rwa [hsq, Real.sqrt_sq hpos] at hroot
  · rw [hsq, Real.sqrt_sq_eq_abs, abs_of_nonpos hneg] at hroot
    simpa using neg_Pconstructible hroot

-- Theorem: `sn` is P-constructible as soon as `dn` is. At `c = 0` the parameter carries no
-- information — `dn` is identically `1` — but there the amplitude is `u` itself.
theorem jacobiSn_Pconstructible_of_dn {c u : ℝ} (hcP : PConstructible c)
    (huP : PConstructible u) (hc : c < 1) (h : PConstructible (jacobiDn c u)) :
    PConstructible (jacobiSn c u) := by
  rcases eq_or_ne c 0 with rfl | hc0
  · rw [jacobiSn, jacobiAm_zero_param]
    exact sin_Pconstructible huP
  · have hsq : (1 - jacobiDn c u ^ 2) / c = jacobiSn c u ^ 2 := by
      rw [jacobiDn_sq hc]
      field_simp
      ring
    have hroot : PConstructible (Real.sqrt ((1 - jacobiDn c u ^ 2) / c)) :=
      sqrt_Pconstructible (PConstructible.div (PConstructible.sub
        PConstructible.base_one (sq_Pconstructible h)) hcP)
    rcases le_total 0 (jacobiSn c u) with hpos | hneg
    · rwa [hsq, Real.sqrt_sq hpos] at hroot
    · rw [hsq, Real.sqrt_sq_eq_abs, abs_of_nonpos hneg] at hroot
      simpa using neg_Pconstructible hroot

-- Theorem: `dn` is P-constructible as soon as `sn` is, being `√(1 - c sn²)`.
theorem jacobiDn_Pconstructible_of_sn {c u : ℝ} (hcP : PConstructible c)
    (h : PConstructible (jacobiSn c u)) : PConstructible (jacobiDn c u) :=
  sqrt_Pconstructible (PConstructible.sub PConstructible.base_one
    (PConstructible.mul hcP (sq_Pconstructible h)))

end JacobiConstructibility
section EllipseAmplitude

/-! ### The amplitude of `E`, and why it is the one that is reachable

`E` *is* an arc length: `arcLengthOf_ellipseParam` says the arc of the ellipse with
semi-axes `1` and `b = √(1 - c)` swept from the top over `[0, φ]` has length exactly
`E(φ)`. So the constructor that converts a length back into a position —
`PConstructibleCurve.arc_of_length`, the string of known length laid along a drawn curve —
inverts `E` directly, exactly as it inverted the arc length of the circle to give `cos`
and `sin`.

The construction is `cos_sin_Pconstructible_of_mem_Icc` with the circle replaced by the
ellipse. Laying out an arc of length `L` from the top gives a curve but not yet a point;
what pins down its far end is a second arc abutting it, the one that runs backwards from
`(1, 0)` — the end of the horizontal semi-axis, at angle `π/2` — for the complementary
length `E(π/2) - L`. The two together cover the quarter of the ellipse in the first
quadrant and meet only where the first stops, so `inter_x` and `inter_y` read off the
coordinates `(sin φ, b cos φ)` of that point, and `arccos` recovers the angle `φ` itself.

Reduction to the quarter turn is by the two symmetries of `E`: reflection,
`E(π - φ) = E(π) - E(φ)`, folds the second quarter onto the first, and periodicity,
`E(φ + nπ) = E(φ) + n E(π)`, handles the rest of the line. -/

-- Theorem: the second-kind integrand is symmetric about `π/2`.
theorem ellipticEIntegrand_pi_sub (c x : ℝ) :
    ellipticEIntegrand c (Real.pi - x) = ellipticEIntegrand c x := by
  simp [ellipticEIntegrand, Real.sin_pi_sub]

-- Theorem: so `E` reflects, `E(π - φ) = E(π) - E(φ)`.
theorem ellipticE_pi_sub (c φ : ℝ) :
    ellipticE c (Real.pi - φ) = ellipticE c Real.pi - ellipticE c φ := by
  have h := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := Real.pi - φ)
    (ellipticEIntegrand c) Real.pi
  simp only [ellipticEIntegrand_pi_sub, sub_sub_cancel, sub_zero] at h
  have hadj := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_ellipticEIntegrand c 0 φ)
    (intervalIntegrable_ellipticEIntegrand c φ Real.pi)
  simp only [ellipticE]
  linarith

-- Theorem: and the half turn is twice the quarter turn.
theorem ellipticE_pi (c : ℝ) : ellipticE c Real.pi = 2 * ellipticE c (Real.pi / 2) := by
  have h := ellipticE_pi_sub c (Real.pi / 2)
  rw [show Real.pi - Real.pi / 2 = Real.pi / 2 from by ring] at h
  linarith

/-- The inverse of `φ ↦ E(φ, c)`: the angle at which the ellipse has been swept through
arc length `u`. As with `jacobiAm` this is a junk value unless `c < 1`. -/
noncomputable def ellipticEAm (c u : ℝ) : ℝ := Function.invFun (ellipticE c) u

theorem ellipticE_ellipticEAm {c : ℝ} (hc : c < 1) (u : ℝ) :
    ellipticE c (ellipticEAm c u) = u :=
  Function.invFun_eq (surjective_ellipticE hc u)

theorem ellipticEAm_ellipticE {c : ℝ} (hc : c < 1) (φ : ℝ) :
    ellipticEAm c (ellipticE c φ) = φ :=
  Function.leftInverse_invFun (strictMono_ellipticE hc).injective φ

theorem ellipticEAm_eq_of_ellipticE_eq {c u φ : ℝ} (hc : c < 1) (h : ellipticE c φ = u) :
    ellipticEAm c u = φ := by
  rw [← h, ellipticEAm_ellipticE hc]

/-- The same ellipse traced from `(1, 0)`, the end of the horizontal semi-axis: the point
at angle `π/2 - t`, so that `t` runs backwards through the angles. -/
noncomputable def ellipseCoParam (b : ℝ) : ℝ → ℝ × ℝ := fun t => (Real.cos t, b * Real.sin t)

theorem ellipseCoParam_eq (b t : ℝ) :
    ellipseCoParam b t = ellipseParam b (Real.pi / 2 - t) := by
  simp [ellipseCoParam, ellipseParam, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]

-- Theorem: it too is traced at the second-kind integrand for its speed.
theorem speed_ellipseCoParam {c b : ℝ} (hb : b ^ 2 = 1 - c) (t : ℝ) :
    speed (ellipseCoParam b) t = ellipticEIntegrand c (Real.pi / 2 - t) := by
  have hx : HasDerivAt (fun s : ℝ => (ellipseCoParam b s).1) (-Real.sin t) t :=
    Real.hasDerivAt_cos t
  have hy : HasDerivAt (fun s : ℝ => (ellipseCoParam b s).2) (b * Real.cos t) t :=
    (Real.hasDerivAt_sin t).const_mul b
  rw [speed, hx.deriv, hy.deriv, ellipticEIntegrand, Real.sin_pi_div_two_sub]
  congr 1
  linear_combination Real.sin_sq_add_cos_sq t + Real.cos t ^ 2 * hb

-- Theorem: so the arc it sweeps over `[0, M]` has length `E(π/2) - E(π/2 - M)`.
theorem arcLengthOf_ellipseCoParam {c b : ℝ} (hb : b ^ 2 = 1 - c) (M : ℝ) :
    arcLengthOf (ellipseCoParam b) 0 M
      = ellipticE c (Real.pi / 2) - ellipticE c (Real.pi / 2 - M) := by
  rw [arcLengthOf]
  simp only [speed_ellipseCoParam hb]
  have h := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := M)
    (ellipticEIntegrand c) (Real.pi / 2)
  rw [sub_zero] at h
  have hadj := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_ellipticEIntegrand c 0 (Real.pi / 2 - M))
    (intervalIntegrable_ellipticEIntegrand c (Real.pi / 2 - M) (Real.pi / 2))
  simp only [ellipticE]
  linarith

-- Theorem: the arc of the ellipse swept from the top over `[0, φ]` is a P-constructible
-- curve as soon as its length `E(φ)` is a P-constructible number. This is
-- `circleArc_PConstructibleCurve` with the circle replaced by the ellipse; the bound
-- `φ ≤ π` is again only what injectivity of the tracing needs.
theorem ellipseArc_PConstructibleCurve {c b φ : ℝ} (hb : b ^ 2 = 1 - c) (hbpos : 0 < b)
    (hbP : PConstructible b) (h0 : 0 ≤ φ) (hpi : φ ≤ Real.pi)
    (hLP : PConstructible (ellipticE c φ)) :
    PConstructibleCurve (ellipseParam b '' Set.Icc 0 φ) := by
  refine PConstructibleCurve.arc_of_length (ellipse_PConstructibleCurve hbP hbpos)
    (ellipseParam b) h0 ?_ ?_ ?_ ?_ ?_ ?_ hLP (arcLengthOf_ellipseParam hb φ)
  · rintro p ⟨θ, _, rfl⟩
    simp only [Set.mem_ofPred_eq, ellipseParam, sub_zero]
    field_simp
    linear_combination Real.sin_sq_add_cos_sq θ
  · intro t₁ ht₁ t₂ ht₂ h
    have hcos : Real.cos t₁ = Real.cos t₂ :=
      mul_left_cancel₀ hbpos.ne' (congrArg Prod.snd h)
    exact Real.injOn_cos (Set.Icc_subset_Icc le_rfl hpi ht₁)
      (Set.Icc_subset_Icc le_rfl hpi ht₂) hcos
  · intro t _
    exact ⟨(Real.hasDerivAt_sin t).differentiableAt,
      ((Real.hasDerivAt_cos t).const_mul b).differentiableAt⟩
  · rw [show speed (ellipseParam b) = ellipticEIntegrand c from
      funext (speed_ellipseParam_eq hb)]
    exact intervalIntegrable_ellipticEIntegrand c 0 φ
  · simpa [ellipseParam] using zero_Pconstructible
  · simpa [ellipseParam] using hbP

-- Theorem: the same for the arc swept backwards from `(1, 0)`.
theorem ellipseCoArc_PConstructibleCurve {c b M : ℝ} (hb : b ^ 2 = 1 - c) (hbpos : 0 < b)
    (hbP : PConstructible b) (h0 : 0 ≤ M) (hpi : M ≤ Real.pi)
    (hLP : PConstructible (ellipticE c (Real.pi / 2) - ellipticE c (Real.pi / 2 - M))) :
    PConstructibleCurve (ellipseCoParam b '' Set.Icc 0 M) := by
  refine PConstructibleCurve.arc_of_length (ellipse_PConstructibleCurve hbP hbpos)
    (ellipseCoParam b) h0 ?_ ?_ ?_ ?_ ?_ ?_ hLP (arcLengthOf_ellipseCoParam hb M)
  · rintro p ⟨t, _, rfl⟩
    simp only [Set.mem_ofPred_eq, ellipseCoParam, sub_zero]
    field_simp
    linear_combination Real.sin_sq_add_cos_sq t
  · intro t₁ ht₁ t₂ ht₂ h
    exact Real.injOn_cos (Set.Icc_subset_Icc le_rfl hpi ht₁)
      (Set.Icc_subset_Icc le_rfl hpi ht₂) (congrArg Prod.fst h)
  · intro t _
    exact ⟨(Real.hasDerivAt_cos t).differentiableAt,
      ((Real.hasDerivAt_sin t).const_mul b).differentiableAt⟩
  · rw [show speed (ellipseCoParam b)
        = fun t => ellipticEIntegrand c (Real.pi / 2 - t) from
      funext (speed_ellipseCoParam hb)]
    exact ((continuous_ellipticEIntegrand c).comp (by fun_prop)).intervalIntegrable 0 M
  · simpa [ellipseCoParam] using PConstructible.base_one
  · simpa [ellipseCoParam] using zero_Pconstructible

-- Theorem: for `0 ≤ L ≤ E(π/2)` the angle at which the ellipse has been swept through arc
-- length `L` is P-constructible.
--
-- The two arcs meet only at that angle: a common point is `(sin θ₁, b cos θ₁)` for some
-- `θ₁ ≤ φ` on the first arc and `(sin θ₂, b cos θ₂)` for some `θ₂ ≥ φ` on the second, and
-- since `cos` is injective on `[0, π]` the two angles agree, which forces both to be `φ`.
theorem ellipticEAm_Pconstructible_of_mem_Icc {c L : ℝ} (hcP : PConstructible c)
    (hLP : PConstructible L) (hc : c < 1) (h0 : 0 ≤ L)
    (hK : L ≤ ellipticE c (Real.pi / 2)) : PConstructible (ellipticEAm c L) := by
  have hpi := Real.pi_pos
  have hb : Real.sqrt (1 - c) ^ 2 = 1 - c := Real.sq_sqrt (by linarith)
  have hbpos : 0 < Real.sqrt (1 - c) := Real.sqrt_pos.mpr (by linarith)
  have hbP : PConstructible (Real.sqrt (1 - c)) :=
    sqrt_Pconstructible (PConstructible.sub PConstructible.base_one hcP)
  set b := Real.sqrt (1 - c) with hbdef
  set φ := ellipticEAm c L with hφdef
  have hEφ : ellipticE c φ = L := ellipticE_ellipticEAm hc L
  have hmono := strictMono_ellipticE hc
  have hφ0 : 0 ≤ φ := by
    refine hmono.le_iff_le.mp ?_
    rw [ellipticE_zero_right, hEφ]
    exact h0
  have hφ2 : φ ≤ Real.pi / 2 := by
    refine hmono.le_iff_le.mp ?_
    rw [hEφ]
    exact hK
  have hA : PConstructibleCurve (ellipseParam b '' Set.Icc 0 φ) :=
    ellipseArc_PConstructibleCurve hb hbpos hbP hφ0 (by linarith) (by rw [hEφ]; exact hLP)
  have hKP : PConstructible (ellipticE c (Real.pi / 2)) :=
    ellipticE_Pconstructible hcP pi_div_two_Pconstructible hc
  have hB : PConstructibleCurve (ellipseCoParam b '' Set.Icc 0 (Real.pi / 2 - φ)) := by
    refine ellipseCoArc_PConstructibleCurve hb hbpos hbP (by linarith) (by linarith) ?_
    rw [show Real.pi / 2 - (Real.pi / 2 - φ) = φ from by ring, hEφ]
    exact PConstructible.sub hKP hLP
  have hinter : ellipseParam b '' Set.Icc 0 φ ∩
      ellipseCoParam b '' Set.Icc 0 (Real.pi / 2 - φ) = {(Real.sin φ, b * Real.cos φ)} := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_Icc, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨θ₁, ⟨hθ₁0, hθ₁φ⟩, rfl⟩, t, ⟨ht0, htM⟩, heq⟩
      rw [ellipseCoParam_eq] at heq
      have hcos : Real.cos (Real.pi / 2 - t) = Real.cos θ₁ :=
        mul_left_cancel₀ hbpos.ne' (congrArg Prod.snd heq)
      have hang : Real.pi / 2 - t = θ₁ :=
        Real.injOn_cos (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)
          (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩) hcos
      rw [show θ₁ = φ from by linarith]
      simp [ellipseParam]
    · rintro rfl
      refine ⟨⟨φ, ⟨hφ0, le_rfl⟩, rfl⟩, Real.pi / 2 - φ, ⟨by linarith, le_rfl⟩, ?_⟩
      simp [ellipseCoParam, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
  have hy := PConstructible.inter_y hA hB hinter
  have hcos : PConstructible (Real.cos φ) := by
    rw [show Real.cos φ = b * Real.cos φ / b from by field_simp]
    exact PConstructible.div hy hbP
  have harc := arccos_Pconstructible_of_mem_Icc hcos (Real.neg_one_le_cos φ)
    (Real.cos_le_one φ)
  rwa [Real.arccos_cos hφ0 (by linarith)] at harc

-- Theorem: every real number sits a whole number of periods `p` away from one in `[0, p]`.
-- This is `exists_int_half_turns` with `π` replaced by an arbitrary positive period; here
-- the period is `2 E(π/2)`, the length of half the ellipse, and not `π`.
theorem exists_int_mul_mem_Icc {p : ℝ} (hp : 0 < p) (x : ℝ) :
    ∃ n : ℤ, 0 ≤ x - n * p ∧ x - n * p ≤ p := by
  refine ⟨⌊x / p⌋, ?_, ?_⟩
  · have h := mul_le_mul_of_nonneg_right (Int.floor_le (x / p)) hp.le
    rw [div_mul_cancel₀ _ hp.ne'] at h
    linarith
  · have h := mul_lt_mul_of_pos_right (Int.lt_floor_add_one (x / p)) hp
    rw [div_mul_cancel₀ _ hp.ne'] at h
    linarith

-- Theorem: the quarter turn has positive length.
theorem ellipticE_pi_div_two_pos {c : ℝ} (hc : c < 1) : 0 < ellipticE c (Real.pi / 2) := by
  have h := strictMono_ellipticE hc (show (0 : ℝ) < Real.pi / 2 by linarith [Real.pi_pos])
  rwa [ellipticE_zero_right] at h

-- Theorem: **the amplitude of `E` is P-constructible at every P-constructible argument.**
-- Equivalently: the point reached after travelling a prescribed P-constructible distance
-- along a drawable ellipse, from the end of a semi-axis, is a P-constructible point.
--
-- Reduction to the quarter turn settled above is in two steps. Periodicity takes `u` into
-- `[0, 2 E(π/2)]`, the length of half the ellipse, at the cost of a whole number of half
-- turns of the angle; reflection about `π/2` folds the upper half of what is left onto the
-- lower, at the cost of subtracting from `π`.
theorem ellipticEAm_Pconstructible {c u : ℝ} (hcP : PConstructible c)
    (huP : PConstructible u) (hc : c < 1) : PConstructible (ellipticEAm c u) := by
  have hKpos := ellipticE_pi_div_two_pos hc
  have hKP : PConstructible (ellipticE c (Real.pi / 2)) :=
    ellipticE_Pconstructible hcP pi_div_two_Pconstructible hc
  obtain ⟨n, hr0, hr2⟩ :=
    exists_int_mul_mem_Icc (show (0 : ℝ) < 2 * ellipticE c (Real.pi / 2) by linarith) u
  have hrP : PConstructible (u - n * (2 * ellipticE c (Real.pi / 2))) :=
    PConstructible.sub huP (PConstructible.mul (int_Pconstructible n)
      (PConstructible.mul two_Pconstructible hKP))
  have hkey : ellipticEAm c u
      = ellipticEAm c (u - n * (2 * ellipticE c (Real.pi / 2))) + n * Real.pi :=
    ellipticEAm_eq_of_ellipticE_eq hc (by
      rw [ellipticE_add_int_mul_pi, ellipticE_ellipticEAm hc, ellipticE_pi]
      ring)
  rw [hkey]
  refine PConstructible.add ?_ (PConstructible.mul (int_Pconstructible n) pi_Pconstructible)
  rcases le_total (u - n * (2 * ellipticE c (Real.pi / 2))) (ellipticE c (Real.pi / 2))
    with hle | hle
  · exact ellipticEAm_Pconstructible_of_mem_Icc hcP hrP hc hr0 hle
  · have hrefl : ellipticEAm c (u - n * (2 * ellipticE c (Real.pi / 2)))
        = Real.pi - ellipticEAm c (2 * ellipticE c (Real.pi / 2)
            - (u - n * (2 * ellipticE c (Real.pi / 2)))) :=
      ellipticEAm_eq_of_ellipticE_eq hc (by
        rw [ellipticE_pi_sub, ellipticE_ellipticEAm hc, ellipticE_pi]
        ring)
    rw [hrefl]
    exact PConstructible.sub pi_Pconstructible
      (ellipticEAm_Pconstructible_of_mem_Icc hcP
        (PConstructible.sub (PConstructible.mul two_Pconstructible hKP) hrP) hc
        (by linarith) (by linarith))

-- Theorem: so the arc-length parametrization of the ellipse is P-constructible in both
-- coordinates: `(sin, b cos)` of the amplitude, the point itself.
theorem ellipseParam_ellipticEAm_Pconstructible {c u : ℝ} (hcP : PConstructible c)
    (huP : PConstructible u) (hc : c < 1) :
    PConstructible (Real.sin (ellipticEAm c u)) ∧
      PConstructible (Real.sqrt (1 - c) * Real.cos (ellipticEAm c u)) :=
  ⟨sin_Pconstructible (ellipticEAm_Pconstructible hcP huP hc),
    PConstructible.mul (sqrt_Pconstructible (PConstructible.sub PConstructible.base_one hcP))
      (cos_Pconstructible (ellipticEAm_Pconstructible hcP huP hc))⟩

end EllipseAmplitude

section Outlook

/-! ### Where this leaves `sn`, `cn`, `dn`

Collecting what is settled: the four Jacobi functions are equiconstructible with one
another at every argument, they are P-constructible at every argument *presented* as
`F(φ)` for a P-constructible angle `φ`, and the corresponding question for the second-kind
integral — the amplitude of `E` — has the positive answer proved above. -/

-- Theorem: at an argument presented as a first-kind integral of a P-constructible angle,
-- the amplitude is that angle, so all four functions are P-constructible there. The
-- arguments this covers are dense, but presenting `u` as `F(φ)` is precisely what is not
-- available for a `u` given in advance.
theorem jacobiAm_ellipticF_Pconstructible {c φ : ℝ} (hφP : PConstructible φ) (hc : c < 1) :
    PConstructible (jacobiAm c (ellipticF c φ)) := by
  rw [jacobiAm_ellipticF hc]
  exact hφP

-- Theorem: `sn` and the amplitude stand or fall together, with no side conditions at all.
theorem jacobiAm_Pconstructible_iff_sn {c u : ℝ} :
    PConstructible (jacobiAm c u) ↔ PConstructible (jacobiSn c u) :=
  ⟨jacobiSn_Pconstructible_of_am, fun h =>
    jacobiAm_Pconstructible_of_cn (jacobiCn_Pconstructible_of_sn h)⟩

-- Theorem: and so do `cn` and the amplitude.
theorem jacobiAm_Pconstructible_iff_cn {c u : ℝ} :
    PConstructible (jacobiAm c u) ↔ PConstructible (jacobiCn c u) :=
  ⟨jacobiCn_Pconstructible_of_am, jacobiAm_Pconstructible_of_cn⟩

-- Theorem: and so do `dn` and the amplitude, this time needing the parameter and the
-- argument, since at `c = 0` the value of `dn` carries no information about `u`.
theorem jacobiAm_Pconstructible_iff_dn {c u : ℝ} (hcP : PConstructible c)
    (huP : PConstructible u) (hc : c < 1) :
    PConstructible (jacobiAm c u) ↔ PConstructible (jacobiDn c u) :=
  ⟨jacobiDn_Pconstructible_of_am hcP, fun h =>
    jacobiAm_Pconstructible_of_cn (jacobiCn_Pconstructible_of_sn
      (jacobiSn_Pconstructible_of_dn hcP huP hc h))⟩

/-! #### Why the first kind resists, where the second kind did not

The gap between `ellipticEAm_Pconstructible` and the missing `jacobiAm_Pconstructible` is
not a gap in the bookkeeping, and it is worth writing down what it is.

Everything the drawing program can do to produce a number is one of four things:
arithmetic; reading a coordinate off a crossing of two drawn curves; measuring the length
of a drawn arc; and — the converse of measuring — laying out an arc of prescribed length
along a drawn curve and finding where it ends. The first two are algebraic in what they
consume, `crossing_Pconstructible` being exactly the statement that a crossing solves a
polynomial. So a transcendental function can be *inverted* only by the fourth, and the
fourth inverts one thing: the arc length function of a drawable curve.

That is why `arccos` and the amplitude of `E` are reachable. Arc length along the unit
circle is the angle, so laying out a length recovers an angle, which is
`cos_sin_Pconstructible`. Arc length along the ellipse is `E` on the nose
(`arcLengthOf_ellipseParam`), so laying out a length recovers the amplitude of `E`, which
is the theorem above.

`F` is not an arc length, and the section heading on the first-kind integral in
`Pptc.Basic` says so in as many words. `ellipticF_Pconstructible_of_pos` reaches it by
measuring the Bézier arc `J` and then *removing*, by two integrations by parts, a multiple
of `E` and an algebraic boundary term `tan φ · Δ(φ)`. Subtraction is available going
forwards and unavailable going backwards: laying out an arc of length `L` along the Bézier
gives the `T` with `J(T) = L`, not the `T` with `J(T) - (algebraic in T) = L`, and it is
the second equation that the amplitude solves.

Nor does some other curve help. An arc length is `∫√(x'² + y'²)`, so along a rationally
parametrized curve it is `∫ R w dt` for a rational `R`, where `w² = Q` is the quartic of
the associated elliptic curve: a differential with poles, whose reduction always leaves a
boundary term behind. `F` is `∫ dt / w`, the differential with no poles at all. Curves
whose arc length is a first-kind integral on the nose do exist — the lemniscate is the
classical one, with `ds = dr/√(1 - r⁴)` — but they are not rationally parametrized, and
every algebraic curve this program draws is: conics, polynomial graphs, power laws
`y = a x^b` with `b` rational, cubic Béziers, and affine images of those. `offset` does
produce non-rational curves, but no new arc lengths: an offset at distance `d` has length
`s - d · (turning angle)`, and the turning angle is elementary.

The same verdict covers what would have come after `sn`. The lemniscatic sine is the
amplitude at the lemniscatic modulus, and the Weierstrass function inverts
`∫ dz/√(4z³ - g₂ z - g₃)`, which is again the differential with no poles. Those are the
same question in other coordinates, not further targets.

None of this is a proof that `sn` is *not* P-constructible. That would take a genuine
independence argument, and nothing here supplies one. What it says is where a construction
cannot come from, and so what would have to change for one to exist: a constructor that
draws a curve of positive genus, or an identity expressing `am` in terms of quantities
already in hand. -/

end Outlook

end Pconstructible
