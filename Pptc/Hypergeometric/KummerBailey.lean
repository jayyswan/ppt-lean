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

-- Targeted imports rather than `import Mathlib`; see the note in `Pptc.Defs`.
-- `Pfaff` supplies Pfaff's transformation and the continuity of `hyp` at `-1`,
-- `GaussSecond` Gauss's second summation theorem, and `GammaRational` the
-- P-constructibility of `Γ` at rationals (which pulls in `GammaFunctional`).
import Pptc.Hypergeometric.GaussSecond
import Pptc.Hypergeometric.Pfaff
import Pptc.GammaRational

/-! # Kummer's and Bailey's summation theorems

Two classical evaluations of the Gauss hypergeometric function,

`₂F₁(A, B; 1 + A - B; -1) = Γ(1 + A - B) Γ(1 + A/2) / (Γ(1 + A) Γ(1 + A/2 - B))`
(Kummer, DLMF 15.4.26) and

`₂F₁(a, 1 - a; c; 1/2) = Γ(c/2) Γ((c + 1)/2) / (Γ((a + c)/2) Γ((1 - a + c)/2))`
(Bailey, DLMF 15.4.30), with the P-constructibility of both left-hand sides at rational
parameters.

## How the proofs fit together

The whole file rests on one new limit statement.

**Pfaff at `1/2`.** Letting `z → 1/2⁻` in Pfaff's transformation
`₂F₁(a, b; c; z) = (1 - z)^(-a) ₂F₁(a, c - b; c; z/(z - 1))` is legitimate because
`1/2` lies strictly inside the unit disc where `₂F₁(a, b; c; ·)` is analytic, because
`(1 - z)^(-a) → 2^a`, and because `z/(z - 1) → -1` from above, where the series for
`₂F₁(a, c - b; c; ·)` is continuous once `0 < c - a - (c - b) = b - a` (the Weierstrass
M-test bound of `Pfaff.lean`). Uniqueness of limits gives
`₂F₁(a, b; c; 1/2) = 2^a ₂F₁(a, c - b; c; -1)`.

**Kummer.** Apply Pfaff at `1/2` with `(a, b, c) = (A, 1 + A - 2B, 1 + A - B)`: the right
argument becomes `B` and the convergence hypothesis is exactly `1 - 2B > 0`. The left side
is Gauss's second theorem (`hyp_second`) at `(A, 1 + A - 2B)`, whose three Gamma arguments
are `1 + A - B`, `(A + 1)/2` and `1 + A/2 - B`. Dividing by `2^A` and applying Legendre's
duplication formula at `s = (A + 1)/2`,
`Γ((A+1)/2) Γ(1 + A/2) = Γ(1 + A) 2^(-A) √π`, turns the quotient into Kummer's.

**Bailey.** Rewrite `₂F₁(a, 1 - a; c; ·) = ₂F₁(1 - a, a; c; ·)` and apply Pfaff at `1/2`
in the *second* parameter: this gives `2^(1-a) ₂F₁(1 - a, c - a; c; -1)`. Swapping the
parameters again makes it `₂F₁(c - a, 1 - a; c; -1)`, which is Kummer with `A = c - a`,
`B = 1 - a`; its condition `1 - 2B > 0` is `a > 1/2`. Legendre's duplication formula twice
(at `c/2` and at `(c - a + 1)/2`) turns `2^(1-a)` times the Kummer value into Bailey's
quotient. The left-hand side is invariant under `a ↦ 1 - a`, so the case `a < 1/2` reduces
to the previous one applied to `1 - a`.

## The gap at `a = 1/2`

The theorem `hyp_bailey` assumes `a ≠ 1/2`. The value `₂F₁(½, ½; c; ½)` is *not* covered:
it needs Bailey's own quadratic transformation
`₂F₁(a, 1-a; c; z) = (1-z)^(c-1) ₂F₁((c-a)/2, (c+a-1)/2; c; 4z(1-z))`,
a separate and much larger argument.

Also note that the hypotheses `1 + c - a ≠ -(n)` and `a + c ≠ -(n)` are genuinely
needed and are *not* implied by the other pole conditions. Without them the statement is
false in degenerate half-integer cases: for instance `a = 3/4`, `c = -1/4` makes
`1 + c - a = 0`, so the right-hand side has a pole at `Γ(1 + c - a) = Γ(0)` (in the
Kummer intermediate) while the left-hand side `₂F₁(3/4, 1/4; -1/4; 1/2)` is a perfectly
finite number.
-/

open scoped Topology ENNReal

namespace Pconstructible

noncomputable section

/-! ### Pfaff's transformation at `1/2`

The limit `z → 1/2⁻` of Pfaff's transformation. -/

-- Theorem: Pfaff's transformation at `z = 1/2`,
-- `₂F₁(a,b;c;1/2) = 2^a ₂F₁(a,c-b;c;-1)` when `b > a`.
theorem hyp_pfaff_half {a b c : ℝ} (hc : ∀ n : ℕ, c ≠ -(n : ℝ)) (hba : 0 < b - a) :
    hyp a b c (1 / 2) = 2 ^ a * hyp a (c - b) c (-1) := by
  -- The left-hand side is analytic at `1/2`, which lies inside the unit disc.
  have hL : Filter.Tendsto (fun z : ℝ => hyp a b c z) (𝓝[<] (1 / 2))
      (𝓝 (hyp a b c (1 / 2))) := by
    let S : FormalMultilinearSeries ℝ ℝ ℝ := ordinaryHypergeometricSeries ℝ a b c
    have hrad : (1 : ℝ≥0∞) ≤ S.radius :=
      one_le_hypergeometric_radius (a := a) (b := b) (c := c) hc
    have hpos : 0 < S.radius := lt_of_lt_of_le (by norm_num) hrad
    have hball : AnalyticOnNhd ℝ (fun z : ℝ => hyp a b c z) (Metric.eball 0 (1 : ℝ≥0∞)) :=
      ((S.hasFPowerSeriesOnBall hpos).analyticOnNhd).mono (Metric.eball_subset_eball hrad)
    have hmem : (1 / 2 : ℝ) ∈ Metric.eball 0 (1 : ℝ≥0∞) := by
      rw [mem_eball_zero_iff, enorm_eq_nnnorm]
      simp only [← ENNReal.coe_one, ENNReal.coe_lt_coe]
      norm_num
    exact ((hball (1 / 2) hmem).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  -- `z / (z - 1) → -1` from above.
  have harg : Filter.Tendsto (fun z : ℝ => z / (z - 1)) (𝓝[<] (1 / 2))
      (𝓝[Set.Ioi (-1)] (-1)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hcont : ContinuousAt (fun z : ℝ => z / (z - 1)) (1 / 2) :=
        continuousAt_id.div (continuousAt_id.sub continuousAt_const) (by norm_num)
      have h1 : Filter.Tendsto (fun z : ℝ => z / (z - 1)) (𝓝 (1 / 2)) (𝓝 (-1)) := by
        have := hcont.tendsto
        convert this using 2
        norm_num
      exact h1.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      have hden : z - 1 < 0 := by linarith [show z < 1 / 2 from hz]
      change -1 < z / (z - 1)
      rw [lt_div_iff_of_neg hden]
      linarith [show z < 1 / 2 from hz]
  -- Continuity at `-1` for the parameters on the right (this is where `b - a > 0` enters).
  have hR2 : Filter.Tendsto (fun z : ℝ => hyp a (c - b) c (z / (z - 1))) (𝓝[<] (1 / 2))
      (𝓝 (hyp a (c - b) c (-1))) := by
    have hcab : 0 < c - a - (c - b) := by linarith
    exact (tendsto_hyp_nhdsWithin_neg_one (A := a) (B := c - b) (C := c) hcab hc).comp harg
  -- The prefactor `(1 - z)^(-a) → 2^a`.
  have hpre : Filter.Tendsto (fun z : ℝ => (1 - z) ^ (-a)) (𝓝[<] (1 / 2)) (𝓝 (2 ^ a)) := by
    have hcont : ContinuousAt (fun z : ℝ => (1 - z) ^ (-a)) (1 / 2) :=
      ContinuousAt.rpow_const (continuousAt_const.sub continuousAt_id) (Or.inl (by norm_num))
    have hval : (1 - (1 / 2 : ℝ)) ^ (-a) = 2 ^ a := by
      rw [show (1 : ℝ) - 1 / 2 = (2 : ℝ)⁻¹ by norm_num,
        Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), inv_inv]
    rw [← hval]
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  -- Pfaff on a left-neighbourhood of `1/2`.
  have heq : (fun z : ℝ => hyp a b c z) =ᶠ[𝓝[<] (1 / 2)]
      fun z : ℝ => (1 - z) ^ (-a) * hyp a (c - b) c (z / (z - 1)) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds (by norm_num : (-1 : ℝ) < 1 / 2)).filter_mono nhdsWithin_le_nhds]
      with z hz hz1
    exact hyp_pfaff hc hz1 hz
  exact tendsto_nhds_unique hL ((hpre.mul hR2).congr' heq.symm)

/-! ### Kummer's theorem at `-1` -/

-- Theorem: Kummer's summation theorem,
-- `₂F₁(A,B;1+A-B;-1) = Γ(1+A-B) Γ(1+A/2) / (Γ(1+A) Γ(1+A/2-B))`.
theorem hyp_kummer {A B : ℝ} (h : 0 < 1 - 2 * B)
    (h1 : ∀ n : ℕ, 1 + A - B ≠ -(n : ℝ))
    (h2 : ∀ n : ℕ, (A + 1) / 2 ≠ -(n : ℝ))
    (h3 : ∀ n : ℕ, 1 + A / 2 - B ≠ -(n : ℝ))
    (h4 : ∀ n : ℕ, 1 + A ≠ -(n : ℝ)) :
    hyp A B (1 + A - B) (-1) =
      Real.Gamma (1 + A - B) * Real.Gamma (1 + A / 2) /
        (Real.Gamma (1 + A) * Real.Gamma (1 + A / 2 - B)) := by
  -- Gauss's second theorem at `(A, 1 + A - 2B)`.
  have hAB : ∀ n : ℕ, (A + (1 + A - 2 * B) + 1) / 2 ≠ -(n : ℝ) := by
    intro n
    rw [show (A + (1 + A - 2 * B) + 1) / 2 = 1 + A - B by ring]
    exact h1 n
  have hB : ∀ n : ℕ, ((1 + A - 2 * B) + 1) / 2 ≠ -(n : ℝ) := by
    intro n
    rw [show ((1 + A - 2 * B) + 1) / 2 = 1 + A / 2 - B by ring]
    exact h3 n
  have hsecond := hyp_second (A := A) (B := 1 + A - 2 * B) hAB h2 hB
  rw [show (A + (1 + A - 2 * B) + 1) / 2 = 1 + A - B by ring,
    show ((1 + A - 2 * B) + 1) / 2 = 1 + A / 2 - B by ring] at hsecond
  -- Pfaff at `1/2` with the same parameters.
  have hba : 0 < (1 + A - 2 * B) - A := by linarith
  have hpf := hyp_pfaff_half (a := A) (b := 1 + A - 2 * B) (c := 1 + A - B) h1 hba
  rw [show (1 + A - B) - (1 + A - 2 * B) = B by ring] at hpf
  -- Equate the two expressions for the value at `1/2`.
  have hmain : (2 : ℝ) ^ A * hyp A B (1 + A - B) (-1) =
      Real.sqrt Real.pi * Real.Gamma (1 + A - B) /
        (Real.Gamma ((A + 1) / 2) * Real.Gamma (1 + A / 2 - B)) := by
    rw [← hpf]
    exact hsecond
  -- Legendre's duplication formula at `s = (A + 1)/2`.
  have hdup : Real.Gamma ((A + 1) / 2) * Real.Gamma (1 + A / 2) =
      Real.Gamma (1 + A) * ((2 : ℝ) ^ A)⁻¹ * Real.sqrt Real.pi := by
    have hd := Real.Gamma_mul_Gamma_add_half ((A + 1) / 2)
    rw [show 1 - 2 * ((A + 1) / 2) = -A by ring,
      show (A + 1) / 2 + 1 / 2 = 1 + A / 2 by ring,
      show 2 * ((A + 1) / 2) = 1 + A by ring,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)] at hd
    exact hd
  have hp : (2 : ℝ) ^ A ≠ 0 := (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) A).ne'
  have hp1 : (2 : ℝ) ^ A * ((2 : ℝ) ^ A)⁻¹ = 1 := mul_inv_cancel₀ hp
  have hdupP : Real.Gamma ((A + 1) / 2) * Real.Gamma (1 + A / 2) * (2 : ℝ) ^ A =
      Real.Gamma (1 + A) * Real.sqrt Real.pi := by
    have hd := hdup
    field_simp at hd
    rw [show (2 + A) / 2 = 1 + A / 2 by ring] at hd
    -- `hd : Γ((A+1)/2) * Γ(1+A/2) * 2^A = Γ(1+A) * √π`
    exact hd
  have hG2 : Real.Gamma ((A + 1) / 2) ≠ 0 := by
    intro h0
    obtain ⟨m, hm⟩ := (Real.Gamma_eq_zero_iff ((A + 1) / 2)).1 h0
    exact h2 m hm
  have hG3 : Real.Gamma (1 + A / 2 - B) ≠ 0 := by
    intro h0
    obtain ⟨m, hm⟩ := (Real.Gamma_eq_zero_iff (1 + A / 2 - B)).1 h0
    exact h3 m hm
  have hG4 : Real.Gamma (1 + A) ≠ 0 := by
    intro h0
    obtain ⟨m, hm⟩ := (Real.Gamma_eq_zero_iff (1 + A)).1 h0
    exact h4 m hm
  have hdiv : hyp A B (1 + A - B) (-1) =
      (Real.sqrt Real.pi * Real.Gamma (1 + A - B) /
        (Real.Gamma ((A + 1) / 2) * Real.Gamma (1 + A / 2 - B))) / (2 : ℝ) ^ A := by
    rw [eq_div_iff hp]
    rw [mul_comm (hyp A B (1 + A - B) (-1)) ((2 : ℝ) ^ A)]
    exact hmain
  rw [hdiv, div_div, div_eq_div_iff (mul_ne_zero (mul_ne_zero hG2 hG3) hp)
    (mul_ne_zero hG4 hG3)]
  linear_combination (-(Real.Gamma (1 + A - B) * Real.Gamma (1 + A / 2 - B))) * hdupP

/-! ### Bailey's theorem at `1/2` -/

-- Theorem: the case `1/2 < a` of Bailey's summation theorem,
-- `₂F₁(a,1-a;c;1/2) = Γ(c/2) Γ((c+1)/2) / (Γ((a+c)/2) Γ((1-a+c)/2))`.
theorem hyp_bailey_of_one_half_lt {a c : ℝ} (ha : 1 / 2 < a)
    (hc : ∀ n : ℕ, c ≠ -(n : ℝ))
    (h1 : ∀ n : ℕ, c / 2 ≠ -(n : ℝ))
    (h2 : ∀ n : ℕ, (c + 1) / 2 ≠ -(n : ℝ))
    (h3 : ∀ n : ℕ, (a + c) / 2 ≠ -(n : ℝ))
    (h4 : ∀ n : ℕ, (1 - a + c) / 2 ≠ -(n : ℝ))
    (h5 : ∀ n : ℕ, 1 + c - a ≠ -(n : ℝ)) :
    hyp a (1 - a) c (1 / 2) =
      Real.Gamma (c / 2) * Real.Gamma ((c + 1) / 2) /
        (Real.Gamma ((a + c) / 2) * Real.Gamma ((1 - a + c) / 2)) := by
  -- Kummer with `A = c - a`, `B = 1 - a`.
  have hk1 : ∀ n : ℕ, 1 + (c - a) - (1 - a) ≠ -(n : ℝ) := by
    intro n
    rw [show 1 + (c - a) - (1 - a) = c by ring]
    exact hc n
  have hk2 : ∀ n : ℕ, ((c - a) + 1) / 2 ≠ -(n : ℝ) := by
    intro n
    rw [show ((c - a) + 1) / 2 = (1 - a + c) / 2 by ring]
    exact h4 n
  have hk3 : ∀ n : ℕ, 1 + (c - a) / 2 - (1 - a) ≠ -(n : ℝ) := by
    intro n
    rw [show 1 + (c - a) / 2 - (1 - a) = (a + c) / 2 by ring]
    exact h3 n
  have hk4 : ∀ n : ℕ, 1 + (c - a) ≠ -(n : ℝ) := by
    intro n
    rw [show 1 + (c - a) = 1 + c - a by ring]
    exact h5 n
  have hk := hyp_kummer (A := c - a) (B := 1 - a) (by linarith) hk1 hk2 hk3 hk4
  rw [show 1 + (c - a) - (1 - a) = c by ring,
    show 1 + (c - a) = 1 + c - a by ring,
    show 1 + (c - a) / 2 - (1 - a) = (a + c) / 2 by ring] at hk
  -- The chain of transformations.
  have hchain : hyp a (1 - a) c (1 / 2) =
      2 ^ (1 - a) * (Real.Gamma c * Real.Gamma (1 + (c - a) / 2) /
        (Real.Gamma (1 + c - a) * Real.Gamma ((a + c) / 2))) := by
    calc hyp a (1 - a) c (1 / 2)
        = hyp (1 - a) a c (1 / 2) := hyp_comm a (1 - a) c (1 / 2)
      _ = 2 ^ (1 - a) * hyp (1 - a) (c - a) c (-1) := by
            refine hyp_pfaff_half (a := 1 - a) (b := a) (c := c) hc ?_
            linarith
      _ = 2 ^ (1 - a) * hyp (c - a) (1 - a) c (-1) := by
            rw [hyp_comm (1 - a) (c - a) c (-1)]
      _ = 2 ^ (1 - a) * (Real.Gamma c * Real.Gamma (1 + (c - a) / 2) /
            (Real.Gamma (1 + c - a) * Real.Gamma ((a + c) / 2))) := by
            rw [hk]
  -- Legendre's duplication at `c/2`.
  have hdup1 : Real.Gamma (c / 2) * Real.Gamma ((c + 1) / 2) =
      Real.Gamma c * (2 : ℝ) ^ (1 - c) * Real.sqrt Real.pi := by
    have hd := Real.Gamma_mul_Gamma_add_half (c / 2)
    rw [show c / 2 + 1 / 2 = (c + 1) / 2 by ring,
      show 2 * (c / 2) = c by ring] at hd
    exact hd
  -- Legendre's duplication at `(c - a + 1)/2`.
  have hdup2 : Real.Gamma ((1 - a + c) / 2) * Real.Gamma (1 + (c - a) / 2) =
      Real.Gamma (1 + c - a) * (2 : ℝ) ^ (a - c) * Real.sqrt Real.pi := by
    have hd := Real.Gamma_mul_Gamma_add_half ((c - a + 1) / 2)
    rw [show 1 - 2 * ((c - a + 1) / 2) = a - c by ring,
      show (c - a + 1) / 2 + 1 / 2 = 1 + (c - a) / 2 by ring,
      show 2 * ((c - a + 1) / 2) = 1 + c - a by ring,
      show (c - a + 1) / 2 = (1 - a + c) / 2 by ring] at hd
    exact hd
  -- `2^(1-a) * 2^(a-c) = 2^(1-c)`.
  have hpow : (2 : ℝ) ^ (1 - a) * (2 : ℝ) ^ (a - c) = (2 : ℝ) ^ (1 - c) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  -- The pole conditions on `c/2` and `(c+1)/2` keep the two sides finite; they are in fact
  -- implied by `hc`, but are stated separately to mirror the classical theorem.
  have hGc2 : Real.Gamma (c / 2) ≠ 0 := by
    intro h0
    obtain ⟨m, hm⟩ := (Real.Gamma_eq_zero_iff (c / 2)).1 h0
    exact h1 m hm
  have hGch : Real.Gamma ((c + 1) / 2) ≠ 0 := by
    intro h0
    obtain ⟨m, hm⟩ := (Real.Gamma_eq_zero_iff ((c + 1) / 2)).1 h0
    exact h2 m hm
  have hGac : Real.Gamma ((a + c) / 2) ≠ 0 := by
    intro h0
    obtain ⟨m, hm⟩ := (Real.Gamma_eq_zero_iff ((a + c) / 2)).1 h0
    exact h3 m hm
  have hGah : Real.Gamma ((1 - a + c) / 2) ≠ 0 := by
    intro h0
    obtain ⟨m, hm⟩ := (Real.Gamma_eq_zero_iff ((1 - a + c) / 2)).1 h0
    exact h4 m hm
  have hGe : Real.Gamma (1 + c - a) ≠ 0 := by
    intro h0
    obtain ⟨m, hm⟩ := (Real.Gamma_eq_zero_iff (1 + c - a)).1 h0
    exact h5 m hm
  rw [hchain]
  have hstep : 2 ^ (1 - a) * (Real.Gamma c * Real.Gamma (1 + (c - a) / 2) /
      (Real.Gamma (1 + c - a) * Real.Gamma ((a + c) / 2)))
      = 2 ^ (1 - a) * (Real.Gamma c * Real.Gamma (1 + (c - a) / 2)) /
        (Real.Gamma (1 + c - a) * Real.Gamma ((a + c) / 2)) := by
    ring
  rw [hstep]
  rw [div_eq_div_iff (mul_ne_zero hGe hGac) (mul_ne_zero hGac hGah)]
  linear_combination
    (2 ^ (1 - a) * Real.Gamma c * Real.Gamma ((a + c) / 2)) * hdup2
    + (Real.Gamma c * Real.Gamma ((a + c) / 2) * Real.Gamma (1 + c - a) *
        Real.sqrt Real.pi) * hpow
    - (Real.Gamma (1 + c - a) * Real.Gamma ((a + c) / 2)) * hdup1

/-! ### Bailey's theorem: the remaining case -/

-- Theorem: Bailey's summation theorem,
-- `₂F₁(a,1-a;c;1/2) = Γ(c/2) Γ((c+1)/2) / (Γ((a+c)/2) Γ((1-a+c)/2))` for `a ≠ 1/2`.
theorem hyp_bailey {a c : ℝ} (ha : a ≠ 1 / 2)
    (hc : ∀ n : ℕ, c ≠ -(n : ℝ))
    (h1 : ∀ n : ℕ, c / 2 ≠ -(n : ℝ))
    (h2 : ∀ n : ℕ, (c + 1) / 2 ≠ -(n : ℝ))
    (h3 : ∀ n : ℕ, (a + c) / 2 ≠ -(n : ℝ))
    (h4 : ∀ n : ℕ, (1 - a + c) / 2 ≠ -(n : ℝ))
    (h5 : ∀ n : ℕ, 1 + c - a ≠ -(n : ℝ))
    (h6 : ∀ n : ℕ, a + c ≠ -(n : ℝ)) :
    hyp a (1 - a) c (1 / 2) =
      Real.Gamma (c / 2) * Real.Gamma ((c + 1) / 2) /
        (Real.Gamma ((a + c) / 2) * Real.Gamma ((1 - a + c) / 2)) := by
  rcases lt_or_gt_of_ne ha with hlt | hgt
  · -- `a < 1/2`: apply the previous case to `1 - a`.
    have hb := hyp_bailey_of_one_half_lt (a := 1 - a) (c := c) (by linarith) hc h1 h2
      h4 (by
        intro n
        rw [show (1 - (1 - a) + c) / 2 = (a + c) / 2 by ring]
        exact h3 n)
      (by
        intro n
        rw [show 1 + c - (1 - a) = a + c by ring]
        exact h6 n)
    rw [show 1 - (1 - a) = a by ring] at hb
    rw [hyp_comm a (1 - a) c (1 / 2), hb]
    rw [mul_comm (Real.Gamma (((1 - a) + c) / 2)) (Real.Gamma ((a + c) / 2))]
  · exact hyp_bailey_of_one_half_lt hgt hc h1 h2 h3 h4 h5

/-! ### P-constructibility at rational parameters -/

-- Theorem: for rational `A`, `B` with `1 - 2B > 0` and the four pole conditions,
-- `₂F₁(A,B;1+A-B;-1)` is P-constructible.
theorem hyp_kummer_rat_Pconstructible {A B : ℚ}
    (h : 0 < 1 - 2 * (B : ℝ))
    (h1 : ∀ n : ℕ, 1 + (A : ℝ) - (B : ℝ) ≠ -(n : ℝ))
    (h2 : ∀ n : ℕ, ((A : ℝ) + 1) / 2 ≠ -(n : ℝ))
    (h3 : ∀ n : ℕ, 1 + (A : ℝ) / 2 - (B : ℝ) ≠ -(n : ℝ))
    (h4 : ∀ n : ℕ, 1 + (A : ℝ) ≠ -(n : ℝ)) :
    PConstructible (hyp (A : ℝ) (B : ℝ) (1 + (A : ℝ) - (B : ℝ)) (-1)) := by
  rw [hyp_kummer h h1 h2 h3 h4]
  rw [show 1 + (A : ℝ) - (B : ℝ) = ((1 + A - B : ℚ) : ℝ) by push_cast; ring,
    show 1 + (A : ℝ) / 2 - (B : ℝ) = ((1 + A / 2 - B : ℚ) : ℝ) by push_cast; ring,
    show 1 + (A : ℝ) = ((1 + A : ℚ) : ℝ) by push_cast; ring,
    show 1 + (A : ℝ) / 2 = ((1 + A / 2 : ℚ) : ℝ) by push_cast; ring]
  exact PConstructible.div
    (PConstructible.mul (Gamma_rat_Pconstructible (1 + A - B))
      (Gamma_rat_Pconstructible (1 + A / 2)))
    (PConstructible.mul (Gamma_rat_Pconstructible (1 + A))
      (Gamma_rat_Pconstructible (1 + A / 2 - B)))

-- Theorem: for rational `a`, `c` with `a ≠ 1/2` and the six pole conditions,
-- `₂F₁(a,1-a;c;1/2)` is P-constructible.
theorem hyp_bailey_rat_Pconstructible {a c : ℚ}
    (ha : (a : ℝ) ≠ 1 / 2)
    (hc : ∀ n : ℕ, (c : ℝ) ≠ -(n : ℝ))
    (h1 : ∀ n : ℕ, (c : ℝ) / 2 ≠ -(n : ℝ))
    (h2 : ∀ n : ℕ, ((c : ℝ) + 1) / 2 ≠ -(n : ℝ))
    (h3 : ∀ n : ℕ, ((a : ℝ) + (c : ℝ)) / 2 ≠ -(n : ℝ))
    (h4 : ∀ n : ℕ, (1 - (a : ℝ) + (c : ℝ)) / 2 ≠ -(n : ℝ))
    (h5 : ∀ n : ℕ, 1 + (c : ℝ) - (a : ℝ) ≠ -(n : ℝ))
    (h6 : ∀ n : ℕ, (a : ℝ) + (c : ℝ) ≠ -(n : ℝ)) :
    PConstructible (hyp (a : ℝ) (1 - (a : ℝ)) (c : ℝ) (1 / 2)) := by
  rw [hyp_bailey ha hc h1 h2 h3 h4 h5 h6]
  rw [show (c : ℝ) / 2 = ((c / 2 : ℚ) : ℝ) by push_cast; ring,
    show ((c : ℝ) + 1) / 2 = (((c + 1) / 2 : ℚ) : ℝ) by push_cast; ring,
    show ((a : ℝ) + (c : ℝ)) / 2 = (((a + c) / 2 : ℚ) : ℝ) by push_cast; ring,
    show (1 - (a : ℝ) + (c : ℝ)) / 2 = (((1 - a + c) / 2 : ℚ) : ℝ) by push_cast; ring]
  exact PConstructible.div
    (PConstructible.mul (Gamma_rat_Pconstructible (c / 2))
      (Gamma_rat_Pconstructible ((c + 1) / 2)))
    (PConstructible.mul (Gamma_rat_Pconstructible ((a + c) / 2))
      (Gamma_rat_Pconstructible ((1 - a + c) / 2)))

end

end Pconstructible
