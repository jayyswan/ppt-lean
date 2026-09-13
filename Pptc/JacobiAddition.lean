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

import Pptc.Jacobi
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.Order.MonotoneContinuity

/-! # Pptc.JacobiAddition

Derivatives of the Jacobi amplitude and of `sn`, `cn`, `dn`, the first step of the
addition theorem. Phase 2 shows a certain expression has derivative zero, which needs
these four. The amplitude inverts the strictly monotone first-kind integral `F`, so its
derivative is the reciprocal of the derivative of `F`; the other three follow by the
chain rule. The results are also worth having on their own.
-/

namespace Pconstructible

section Derivatives

/-! ### The amplitude is continuous

`F(·, c)` is a strictly monotone surjection of the line (proved in `Jacobi.lean`), so it
is an order isomorphism; an order isomorphism between linearly ordered spaces with the
order topology is a homeomorphism, hence so is its inverse. The inverse of that order
isomorphism is `jacobiAm c`, because both are left inverses of the injective `F`. -/

-- Theorem: the amplitude is continuous for `c < 1`.
theorem continuous_jacobiAm {c : ℝ} (hc : c < 1) : Continuous (jacobiAm c) := by
  have hsymm : jacobiAm c = ⇑(StrictMono.orderIsoOfSurjective (ellipticF c)
      (strictMono_ellipticF hc) (surjective_ellipticF hc)).symm := by
    funext u
    refine (strictMono_ellipticF hc).injective ?_
    rw [StrictMono.orderIsoOfSurjective_self_symm_apply (ellipticF c)
      (strictMono_ellipticF hc) (surjective_ellipticF hc) u, ellipticF_jacobiAm hc u]
  rw [hsymm]
  exact OrderIso.continuous _

/-! ### The four derivatives

`am` is differentiated by the inverse function theorem at the point where `F` takes the
value `u`. The chain rule then gives `sn = sin ∘ am`, `cn = cos ∘ am` and
`dn = Δ ∘ am`. -/

-- Theorem: the amplitude is differentiable, with derivative `dn`.
theorem hasDerivAt_jacobiAm {c : ℝ} (hc : c < 1) (u : ℝ) :
    HasDerivAt (jacobiAm c) (jacobiDn c u) u := by
  have h := HasDerivAt.of_local_left_inverse (continuous_jacobiAm hc).continuousAt
    (hasDerivAt_ellipticF hc (jacobiAm c u)) (ellipticFIntegrand_pos hc _).ne'
    (Filter.Eventually.of_forall fun y => ellipticF_jacobiAm hc y)
  simpa [jacobiDn, ellipticFIntegrand, inv_inv] using h

-- Theorem: `sn` is differentiable, with derivative `cn * dn`.
theorem hasDerivAt_jacobiSn {c : ℝ} (hc : c < 1) (u : ℝ) :
    HasDerivAt (jacobiSn c) (jacobiCn c u * jacobiDn c u) u := by
  exact (Real.hasDerivAt_sin (jacobiAm c u)).comp u (hasDerivAt_jacobiAm hc u)

-- Theorem: `cn` is differentiable, with derivative `-(sn * dn)`.
theorem hasDerivAt_jacobiCn {c : ℝ} (hc : c < 1) (u : ℝ) :
    HasDerivAt (jacobiCn c) (-(jacobiSn c u * jacobiDn c u)) u := by
  refine ((Real.hasDerivAt_cos (jacobiAm c u)).comp u
    (hasDerivAt_jacobiAm hc u)).congr_deriv ?_
  rw [jacobiSn]
  ring

-- Theorem: `dn` is differentiable, with derivative `-(c * sn * cn)`.
theorem hasDerivAt_jacobiDn {c : ℝ} (hc : c < 1) (u : ℝ) :
    HasDerivAt (jacobiDn c) (-(c * jacobiSn c u * jacobiCn c u)) u := by
  have hD : ellipticEIntegrand c (jacobiAm c u) ≠ 0 :=
    (ellipticEIntegrand_pos hc _).ne'
  have h := (hasDerivAt_ellipticEIntegrand c (jacobiAm c u)
    (one_sub_mul_sin_sq_pos hc _).ne').comp u (hasDerivAt_jacobiAm hc u)
  refine h.congr_deriv ?_
  simp only [jacobiSn, jacobiCn, jacobiDn]
  field_simp [hD]

end Derivatives

section Addition

/-! ### The addition theorem for `cn`

Fix `w = u + v` and put

  `N(x) = cn x · cn(w−x) − sn x · sn(w−x) · dn x · dn(w−x)`,
  `D(x) = 1 − c · sn²x · sn²(w−x)`.

Both are built from `am` at `x` and at `w−x`. Along `x ↦ (am x, am(w−x))` the sum of the
two first-kind integrals is the constant `F(w)`, and the addition formula is the algebraic
first integral of that flow: clearing the denominator `D²` in the derivative of `N/D` leaves
a polynomial identity in `sn, cn, dn, c` using only `sn² + cn² = 1` and `dn² = 1 − c sn²`.
So `N/D` has derivative zero, hence is constant; its values at `x = 0` and `x = u` are
`cn(w)` and the right-hand side of the addition theorem. -/

-- Theorem: the cleared first-integral identity behind the addition theorem for `cn`.
private theorem add_deriv_zero (s1 c1 d1 s2 c2 d2 c : ℝ)
    (h1 : s1 ^ 2 + c1 ^ 2 = 1) (h2 : s2 ^ 2 + c2 ^ 2 = 1)
    (h3 : d1 ^ 2 = 1 - c * s1 ^ 2) (h4 : d2 ^ 2 = 1 - c * s2 ^ 2) :
    (-s1 * d1 * c2 + c1 * s2 * d2 - c1 * s2 * d1 ^ 2 * d2 + s1 * c2 * d1 * d2 ^ 2
        + c * s1 ^ 2 * s2 * c1 * d2 - c * s1 * s2 ^ 2 * d1 * c2)
      * (1 - c * s1 ^ 2 * s2 ^ 2)
    - (c1 * c2 - s1 * s2 * d1 * d2)
      * (-2 * c * s1 * c1 * d1 * s2 ^ 2 + 2 * c * s1 ^ 2 * s2 * c2 * d2) = 0 := by
  have hN' : (-s1 * d1 * c2 + c1 * s2 * d2 - c1 * s2 * d1 ^ 2 * d2 + s1 * c2 * d1 * d2 ^ 2
        + c * s1 ^ 2 * s2 * c1 * d2 - c * s1 * s2 ^ 2 * d1 * c2)
      = 2 * c * s1 * s2 * (s1 * c1 * d2 - s2 * c2 * d1) := by
    linear_combination (-c1 * s2 * d2) * h3 + (s1 * c2 * d1) * h4
  have hD' : -2 * c * s1 * c1 * d1 * s2 ^ 2 + 2 * c * s1 ^ 2 * s2 * c2 * d2
      = 2 * c * s1 * s2 * (s1 * c2 * d2 - c1 * s2 * d1) := by ring
  have hPD : (s1 * c1 * d2 - s2 * c2 * d1) * (1 - c * s1 ^ 2 * s2 ^ 2)
      = (c1 * c2 - s1 * s2 * d1 * d2) * (s1 * c2 * d2 - c1 * s2 * d1) := by
    linear_combination (c2 * s2 * d1) * h1 + (-(s1 * c1 * d2)) * h2
      + (-(s1 * s2 ^ 2 * c1 * d2)) * h3 + (s1 ^ 2 * s2 * c2 * d1) * h4
  rw [hN', hD']
  linear_combination (2 * c * s1 * s2) * hPD

-- Theorem: the denominator `1 - c sn²x sn²(w-x)` of the first integral is positive.
private theorem jacobiQuot_denom_pos {c w x : ℝ} (hc : c < 1) :
    0 < 1 - c * jacobiSn c x ^ 2 * jacobiSn c (w - x) ^ 2 := by
  have hs1 : jacobiSn c x ^ 2 ≤ 1 := by
    have h := jacobiSn_sq_add_jacobiCn_sq c x
    nlinarith [sq_nonneg (jacobiCn c x)]
  have hs2 : jacobiSn c (w - x) ^ 2 ≤ 1 := by
    have h := jacobiSn_sq_add_jacobiCn_sq c (w - x)
    nlinarith [sq_nonneg (jacobiCn c (w - x))]
  rcases le_total c 0 with hc0 | hc0
  · have hle : c * jacobiSn c x ^ 2 * jacobiSn c (w - x) ^ 2 ≤ 0 := by
      have hnn : 0 ≤ jacobiSn c x ^ 2 * jacobiSn c (w - x) ^ 2 :=
        mul_nonneg (sq_nonneg _) (sq_nonneg _)
      nlinarith [hc0, hnn]
    linarith
  · have hle1 : c * jacobiSn c x ^ 2 ≤ c := by
      simpa using mul_le_mul_of_nonneg_left hs1 hc0
    have hle2 : c * jacobiSn c x ^ 2 * jacobiSn c (w - x) ^ 2 ≤ c :=
      calc c * jacobiSn c x ^ 2 * jacobiSn c (w - x) ^ 2
          ≤ c * jacobiSn c (w - x) ^ 2 :=
            mul_le_mul_of_nonneg_right hle1 (sq_nonneg _)
        _ ≤ c * 1 := mul_le_mul_of_nonneg_left hs2 hc0
        _ = c := mul_one c
    linarith

-- Theorem: `x ↦ N/D` has derivative zero everywhere (Euler's argument).
private theorem hasDerivAt_jacobiQuot {c w : ℝ} (hc : c < 1) (x : ℝ) :
    HasDerivAt (fun y : ℝ => (jacobiCn c y * jacobiCn c (w - y)
        - jacobiSn c y * jacobiSn c (w - y) * jacobiDn c y * jacobiDn c (w - y))
      / (1 - c * jacobiSn c y ^ 2 * jacobiSn c (w - y) ^ 2)) 0 x := by
  have hsn1 : HasDerivAt (fun y : ℝ => jacobiSn c y) (jacobiCn c x * jacobiDn c x) x :=
    hasDerivAt_jacobiSn hc x
  have hcn1 : HasDerivAt (fun y : ℝ => jacobiCn c y) (-(jacobiSn c x * jacobiDn c x)) x :=
    hasDerivAt_jacobiCn hc x
  have hdn1 : HasDerivAt (fun y : ℝ => jacobiDn c y) (-(c * jacobiSn c x * jacobiCn c x)) x :=
    hasDerivAt_jacobiDn hc x
  have hsub : HasDerivAt (fun y : ℝ => w - y) (-1) x := (hasDerivAt_id x).const_sub w
  have hsn2 : HasDerivAt (fun y : ℝ => jacobiSn c (w - y))
      (-(jacobiCn c (w - x) * jacobiDn c (w - x))) x := by
    have h := (hasDerivAt_jacobiSn hc (w - x)).comp x hsub
    simpa only [Function.comp_def, mul_neg, mul_one] using h
  have hcn2 : HasDerivAt (fun y : ℝ => jacobiCn c (w - y))
      (jacobiSn c (w - x) * jacobiDn c (w - x)) x := by
    have h := (hasDerivAt_jacobiCn hc (w - x)).comp x hsub
    simpa only [Function.comp_def, mul_neg, mul_one, neg_neg] using h
  have hdn2 : HasDerivAt (fun y : ℝ => jacobiDn c (w - y))
      (c * jacobiSn c (w - x) * jacobiCn c (w - x)) x := by
    have h := (hasDerivAt_jacobiDn hc (w - x)).comp x hsub
    simpa only [Function.comp_def, mul_neg, mul_one, neg_neg] using h
  have hN : HasDerivAt (fun y : ℝ => jacobiCn c y * jacobiCn c (w - y)
      - jacobiSn c y * jacobiSn c (w - y) * jacobiDn c y * jacobiDn c (w - y))
      (-jacobiSn c x * jacobiDn c x * jacobiCn c (w - x)
        + jacobiCn c x * jacobiSn c (w - x) * jacobiDn c (w - x)
        - jacobiCn c x * jacobiSn c (w - x) * jacobiDn c x ^ 2 * jacobiDn c (w - x)
        + jacobiSn c x * jacobiCn c (w - x) * jacobiDn c x * jacobiDn c (w - x) ^ 2
        + c * jacobiSn c x ^ 2 * jacobiSn c (w - x) * jacobiCn c x * jacobiDn c (w - x)
        - c * jacobiSn c x * jacobiSn c (w - x) ^ 2 * jacobiDn c x
          * jacobiCn c (w - x)) x := by
    have h := (hcn1.mul hcn2).sub ((((hsn1.mul hsn2).mul hdn1).mul hdn2))
    refine h.congr_deriv ?_
    simp only [Pi.mul_apply]
    ring
  have hsq1 : HasDerivAt (fun y : ℝ => jacobiSn c y ^ 2)
      (2 * jacobiSn c x * (jacobiCn c x * jacobiDn c x)) x := by
    have hf : jacobiSn c ^ 2 = fun y : ℝ => jacobiSn c y ^ 2 :=
      funext fun y => Pi.pow_apply (jacobiSn c) 2 y
    have h := (hasDerivAt_jacobiSn hc x).pow 2
    rw [hf] at h
    refine h.congr_deriv ?_
    ring_nf
  have hsq2 : HasDerivAt (fun y : ℝ => jacobiSn c (w - y) ^ 2)
      (2 * jacobiSn c (w - x) * (-(jacobiCn c (w - x) * jacobiDn c (w - x)))) x := by
    have hf : (fun y : ℝ => jacobiSn c (w - y)) ^ 2 = fun y : ℝ => jacobiSn c (w - y) ^ 2 :=
      funext fun y => Pi.pow_apply (fun y : ℝ => jacobiSn c (w - y)) 2 y
    have h := hsn2.pow 2
    rw [hf] at h
    refine h.congr_deriv ?_
    ring_nf
  have hcs : HasDerivAt (fun y : ℝ => c * jacobiSn c y ^ 2 * jacobiSn c (w - y) ^ 2)
      ((0 * jacobiSn c x ^ 2 + c * (2 * jacobiSn c x * (jacobiCn c x * jacobiDn c x)))
          * jacobiSn c (w - x) ^ 2
        + (c * jacobiSn c x ^ 2) * (2 * jacobiSn c (w - x)
            * (-(jacobiCn c (w - x) * jacobiDn c (w - x))))) x :=
    ((hasDerivAt_const x c).mul hsq1).mul hsq2
  have hD : HasDerivAt (fun y : ℝ => 1 - c * jacobiSn c y ^ 2 * jacobiSn c (w - y) ^ 2)
      (-2 * c * jacobiSn c x * jacobiCn c x * jacobiDn c x * jacobiSn c (w - x) ^ 2
        + 2 * c * jacobiSn c x ^ 2 * jacobiSn c (w - x) * jacobiCn c (w - x)
          * jacobiDn c (w - x)) x := by
    have h := (hasDerivAt_const x (1 : ℝ)).sub hcs
    refine h.congr_deriv ?_
    ring
  have hq := hN.div hD (ne_of_gt (jacobiQuot_denom_pos (w := w) hc))
  refine hq.congr_deriv ?_
  have hnum : (-jacobiSn c x * jacobiDn c x * jacobiCn c (w - x)
        + jacobiCn c x * jacobiSn c (w - x) * jacobiDn c (w - x)
        - jacobiCn c x * jacobiSn c (w - x) * jacobiDn c x ^ 2 * jacobiDn c (w - x)
        + jacobiSn c x * jacobiCn c (w - x) * jacobiDn c x * jacobiDn c (w - x) ^ 2
        + c * jacobiSn c x ^ 2 * jacobiSn c (w - x) * jacobiCn c x * jacobiDn c (w - x)
        - c * jacobiSn c x * jacobiSn c (w - x) ^ 2 * jacobiDn c x
          * jacobiCn c (w - x))
      * (1 - c * jacobiSn c x ^ 2 * jacobiSn c (w - x) ^ 2)
      - (jacobiCn c x * jacobiCn c (w - x)
          - jacobiSn c x * jacobiSn c (w - x) * jacobiDn c x * jacobiDn c (w - x))
        * (-2 * c * jacobiSn c x * jacobiCn c x * jacobiDn c x * jacobiSn c (w - x) ^ 2
            + 2 * c * jacobiSn c x ^ 2 * jacobiSn c (w - x) * jacobiCn c (w - x)
              * jacobiDn c (w - x)) = 0 :=
    add_deriv_zero (jacobiSn c x) (jacobiCn c x) (jacobiDn c x) (jacobiSn c (w - x))
      (jacobiCn c (w - x)) (jacobiDn c (w - x)) c
      (jacobiSn_sq_add_jacobiCn_sq c x) (jacobiSn_sq_add_jacobiCn_sq c (w - x))
      (jacobiDn_sq hc x) (jacobiDn_sq hc (w - x))
  rw [hnum, zero_div]

-- Theorem: the addition theorem for `cn`.
theorem jacobiCn_add {c : ℝ} (hc : c < 1) (u v : ℝ) :
    jacobiCn c (u + v) =
      (jacobiCn c u * jacobiCn c v - jacobiSn c u * jacobiSn c v * jacobiDn c u * jacobiDn c v)
        / (1 - c * jacobiSn c u ^ 2 * jacobiSn c v ^ 2) := by
  set w : ℝ := u + v with hw
  have hwu : w - u = v := by rw [hw]; ring
  let f : ℝ → ℝ := fun x => (jacobiCn c x * jacobiCn c (w - x)
        - jacobiSn c x * jacobiSn c (w - x) * jacobiDn c x * jacobiDn c (w - x))
      / (1 - c * jacobiSn c x ^ 2 * jacobiSn c (w - x) ^ 2)
  have hderiv : ∀ x : ℝ, HasDerivAt f 0 x := fun x => hasDerivAt_jacobiQuot hc x
  have hconst : f 0 = f u := is_const_of_deriv_eq_zero (f := f)
    (fun x => (hderiv x).differentiableAt) (fun x => (hderiv x).deriv) 0 u
  have h0 : f 0 = jacobiCn c w := by
    simp only [f, jacobiSn_zero hc, jacobiCn_zero hc, jacobiDn_zero hc]
    norm_num
  have hu : f u = (jacobiCn c u * jacobiCn c v
        - jacobiSn c u * jacobiSn c v * jacobiDn c u * jacobiDn c v)
      / (1 - c * jacobiSn c u ^ 2 * jacobiSn c v ^ 2) := by
    simp only [f, hwu]
  rw [← h0, hconst, hu]

-- Theorem: the amplitudes at which `am` is P-constructible are closed under addition.
theorem jacobiAm_Pconstructible_add {c u v : ℝ} (hcP : PConstructible c) (hc : c < 1)
    (hu : PConstructible (jacobiAm c u)) (hv : PConstructible (jacobiAm c v)) :
    PConstructible (jacobiAm c (u + v)) := by
  refine jacobiAm_Pconstructible_of_cn ?_
  rw [jacobiCn_add hc u v]
  have hsu := jacobiSn_Pconstructible_of_am hu
  have hcu := jacobiCn_Pconstructible_of_am hu
  have hdu := jacobiDn_Pconstructible_of_am hcP hu
  have hsv := jacobiSn_Pconstructible_of_am hv
  have hcv := jacobiCn_Pconstructible_of_am hv
  have hdv := jacobiDn_Pconstructible_of_am hcP hv
  pconstructible

end Addition

end Pconstructible

