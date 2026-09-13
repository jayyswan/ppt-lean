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

end Pconstructible

