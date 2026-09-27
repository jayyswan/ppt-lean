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

-- Targeted imports rather than `import Mathlib`; see the note in `Pptc.Defs`.
import Pptc.TotallyReal.YSpace
import Pptc.TotallyReal.SignChange
import Pptc.TotallyReal.OpenTube
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Topology.Order.IntermediateValue

/-! # Pptc.TotallyReal.Certificate

**The odd Tschirnhaus lemma** (PLAN §2.4), together with everything it rests on.

## What is being built

Let `X = V ∩ {S₃ = 0}` be the set of y-vectors with `S₁ = S₃ = 0`, where `V = {S₁ = 0}`
and `S_k(y) = Σᵢ yᵢ^k`. The goal is a y-vector `y ∈ X` with `S₅(y) = 0` whose entries are
pairwise distinct, reached from a P-constructible `b`-vector. Newton
(`TotallyReal/Newton.lean`) then turns that into the resolvent shape
`t·R(t²) − e₇` resp. `Q(t²) − e₇·t`, which `TotallyReal/Engines.lean` inverts.

| step | equation | degree |
|---|---|---|
| 1 | `S₃(a + λ b) = 0` | 3 |
| 2 | `Q(w̃₁ + x w̃₂) = 0`, with `w̃ⱼ = Ywⱼ − (⟨YP², Ywⱼ⟩/⟨YP², Yg⟩)·Yg` | 2 |
| 3 | `S₃(pt(μ)) = 0`, with `pt(μ) = Yq₀ − (2⟨YP, Yq₀, d⟩/⟨YP, d, d⟩)·d`, `d = μ w̃₁ + w̃₃` | 6 |
| 4 | `S₅(YP + κ v) = 0` | 5 |

Steps 1–3 put the whole line `YP + κ v` inside `X`; step 4 cuts that line with `S₅ = 0`.

## Why the degrees are what they are

The forms `S_k` and the conic `Q_P` live in *y-space*, and the `y`-vectors are affine in
the six inputs with P-constructible scalars, so each step is a genuine polynomial in the
step variable: `S₃` is cubic, `Q_P` is quadratic in `x` (it is a quadratic form
evaluated at an affine function of `x`), step 3 is `S₃` of a rational function of a
degree-1-in-`μ` direction — so after clearing the denominator `⟨P, d(μ), d(μ)⟩³`, which is
degree `≤ 6` — and `S₅` is quintic. `chainStep3Cleared` is the polynomial form;
`root_Pconstructible_le_six_coeffs` is the engine that `≤ 6` demands.

## Non-degeneracy

`chainProjN` and `chainConicPt` divide, so the chain is only defined near configurations
with `⟨YP², Yg⟩ ≠ 0` and `⟨YP, d, d⟩ ≠ 0`. Both are open conditions and both hold at the
certified centres (`⟨P², g⟩ = 244` for `n = 7` and `71/2` for `n = 8`).

## The chain is written twice

Once in y-space (`ChainYInputs`, `chainStepᵢ`) — that is what the algebra, the
certificate and the openness argument talk about, and what the rational centre data of
PLAN §2.4 describes. Once as a lift to `b`-vectors (`ChainBInputs`, `ChainB.out`) — that
is what carries P-constructibility, since the input y-vectors are generally *not*
P-constructible entrywise while the `b`-vectors are. `chainBLift_yvec` says the two
agree.

## A note on names

The four step roots are called `lam`, `x`, `mu`, `kappa` rather than `λ`, `x`, `μ`, `κ`,
because `λ` is a reserved token in Lean 4 and cannot be used as a binder name.
-/

namespace Pconstructible

open Polynomial

noncomputable section

variable {n : ℕ}

/-! ### The four step functions, in y-space -/

/-- Step 1: solve `S₃(a + λ b) = 0` in `λ`. The inputs `a`, `b` are y-vectors. -/
def chainStep1 (a b : Fin n → ℝ) (lam : ℝ) : ℝ := psumY (a + lam • b) 3

/-- The projection of `w` into `N_P = {v : Σᵢ (YP i)² Yv i = 0}` along `g`. -/
def chainProjN (P g w : Fin n → ℝ) : Fin n → ℝ :=
  w - (yNBY P w / yNBY P g) • g

/-- Step 2: solve `Q_P(w̃₁ + x w̃₂) = 0` in `x`, with `w̃ⱼ` the `N_P`-projections. -/
def chainStep2 (P g w₁ w₂ : Fin n → ℝ) (x : ℝ) : ℝ :=
  yConicY P (chainProjN P g w₁ + x • chainProjN P g w₂)

/-- The second intersection of the line `Yq₀ + s·Yd` with the conic `Q_P`, given `Yq₀`
on the conic. This is the reflection of `Yq₀` in the direction `Yd`, scaled — the
standard second-intersection formula for a quadratic form. -/
def chainConicPt (P q₀ d : Fin n → ℝ) : Fin n → ℝ :=
  q₀ - (2 * yBdotY P q₀ d / yBdotY P d d) • d

/-- Step 3: solve `S₃(pt(μ)) = 0` in `μ`, along the line of `chainConicPt`'s with
direction `μ · w̃₁ + w̃₃`. This is a *rational* function of `μ`; `chainStep3Cleared` is
the polynomial version, and it is the one the degree bound applies to. -/
def chainStep3 (P q₀ w₁ w₃ : Fin n → ℝ) (mu : ℝ) : ℝ :=
  psumY (chainConicPt P q₀ (mu • w₁ + w₃)) 3

/-- The step-3 equation with the denominator `⟨P, d, d⟩³` cleared.

`chainConicPt P q₀ d` is `q₀ − 2⟨P,q₀,d⟩/⟨P,d,d⟩ · d`, so multiplying by `⟨P,d,d⟩`
gives `⟨P,d,d⟩·q₀ − 2⟨P,q₀,d⟩·d`, and cubing and summing keeps the same degree. With `d`
linear in `μ` this is a polynomial of degree `6` in `μ` — the largest degree the chain
ever reaches, and the reason `root_Pconstructible_le_six_coeffs` is the engine. -/
def chainStep3Cleared (P q₀ d : Fin n → ℝ) : ℝ :=
  ∑ i, (q₀ i * (yBdotY P d d) - 2 * yBdotY P q₀ d * d i) ^ 3

/-- Clearing the denominator is harmless away from the conic's isotropic directions. -/
theorem chainStep3Cleared_eq {P q₀ d : Fin n → ℝ} (hden : yBdotY P d d ≠ 0) :
    chainStep3Cleared P q₀ d = (yBdotY P d d) ^ 3 * psumY (chainConicPt P q₀ d) 3 := by
  -- pointwise: `B * (q0 - (2C/B) * d) = B * q0 - 2C * d`, with B = `yBdotY P d d`
  have hpt : ∀ i : Fin n, (yBdotY P d d) * (chainConicPt P q₀ d) i
      = q₀ i * (yBdotY P d d) - 2 * yBdotY P q₀ d * d i := by
    intro i
    simp only [chainConicPt, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp [hden]
  have key : ∀ i : Fin n, (q₀ i * (yBdotY P d d) - 2 * yBdotY P q₀ d * d i) ^ 3
      = ((chainConicPt P q₀ d) i) ^ 3 * (yBdotY P d d) ^ 3 := by
    intro i
    calc (q₀ i * (yBdotY P d d) - 2 * yBdotY P q₀ d * d i) ^ 3
        = ((yBdotY P d d) * (chainConicPt P q₀ d) i) ^ 3 := by rw [hpt i]
      _ = ((chainConicPt P q₀ d) i) ^ 3 * (yBdotY P d d) ^ 3 := by ring
  have hsum : ∑ i : Fin n, (q₀ i * (yBdotY P d d) - 2 * yBdotY P q₀ d * d i) ^ 3
      = (∑ i : Fin n, ((chainConicPt P q₀ d) i) ^ 3) * (yBdotY P d d) ^ 3 := by
    calc ∑ i : Fin n, (q₀ i * (yBdotY P d d) - 2 * yBdotY P q₀ d * d i) ^ 3
        = ∑ i : Fin n, ((chainConicPt P q₀ d) i) ^ 3 * (yBdotY P d d) ^ 3 :=
          Finset.sum_congr rfl (fun i _ => key i)
      _ = (∑ i : Fin n, ((chainConicPt P q₀ d) i) ^ 3) * (yBdotY P d d) ^ 3 := by
        rw [Finset.sum_mul]
  simp only [chainStep3Cleared, psumY, psumFinY]
  rw [hsum, mul_comm]

/-- The version that relates the cleared form to `chainStep3` itself. -/
theorem chainStep3Cleared_eq' {P q₀ w₁ w₃ : Fin n → ℝ} {mu : ℝ}
    (hden : yBdotY P (mu • w₁ + w₃) (mu • w₁ + w₃) ≠ 0) :
    chainStep3Cleared P q₀ (mu • w₁ + w₃)
      = (yBdotY P (mu • w₁ + w₃) (mu • w₁ + w₃)) ^ 3
        * chainStep3 P q₀ w₁ w₃ mu := by
  -- `chainStep3 P q0 w1 w3 mu` unfolds to `psumY (chainConicPt P q0 (mu • w1 + w3)) 3`
  exact chainStep3Cleared_eq hden

/-- Step 4: solve `S₅(YP + κ v) = 0` in `κ`. -/
def chainStep4 (P v : Fin n → ℝ) (kappa : ℝ) : ℝ := psumY (P + kappa • v) 5

/-! ### The algebra of the chain

**Proof pattern used throughout.** Each of these is proved by

1. a pointwise identity `key : ∀ i, … = …`, closed by `ring`;
2. summing it with `Finset.sum_congr rfl key` (or `Finset.sum_mul` / `Finset.mul_sum`
   together with `Finset.sum_add_distrib`) to get `hsum : ∑ i, … = …`;
3. `simp only [<the y-space defs>, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]`
   on the goal, so that the `def`s become explicit `∑`s and `hsum` matches, then `rw [hsum]`.

Each expansion is one `simp only` that unfolds the pairings, pushes scalar factors inside
the sums (`Finset.mul_sum`) and merges the resulting sums (`← Finset.sum_add_distrib` /
`← Finset.sum_sub_distrib`), followed by `Finset.sum_congr rfl` with a pointwise `ring`. -/

/-- The cubic power sum along a line, in the order the chain uses. -/
theorem psumY_cube_eq (P v : Fin n → ℝ) (s : ℝ) :
    psumY (P + s • v) 3
      = psumY P 3 + 3 * s * yNBY P v + 3 * s ^ 2 * yConicY P v + s ^ 3 * psumY v 3 := by
  simp only [psumY, psumFinY, yNBY, ymoment2Y, yConicY, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `S₁` is linear, so `S₁(P + s v) = S₁ P + s S₁ v`. -/
theorem psumY_one_eq (P v : Fin n → ℝ) (s : ℝ) :
    psumY (P + s • v) 1 = psumY P 1 + s * psumY v 1 := by
  simp only [psumY, psumFinY, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The pointwise expansion of the conic form along `q₀ − c d`. -/
theorem yConicY_sub_smul (P q₀ d : Fin n → ℝ) (c : ℝ) :
    yConicY P (q₀ - c • d) = yConicY P q₀ - 2 * c * yBdotY P q₀ d + c ^ 2 * yBdotY P d d := by
  simp only [yConicY, ymoment2Y, yBdotY, ymoment3Y, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The second intersection lies on the conic. -/
theorem chainConicPt_on_conic {P q₀ d : Fin n → ℝ} (hden : yBdotY P d d ≠ 0)
    (hq₀ : yConicY P q₀ = 0) : yConicY P (chainConicPt P q₀ d) = 0 := by
  simp only [chainConicPt]
  rw [yConicY_sub_smul, hq₀]
  field_simp [hden]; ring

/-- `yNBY` is additive/scalable in its *second* argument only — it squares the first. -/
theorem yNBY_add_right (P u v : Fin n → ℝ) : yNBY P (u + v) = yNBY P u + yNBY P v := by
  simp only [yNBY, ymoment2Y, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem yNBY_sub_right (P u v : Fin n → ℝ) : yNBY P (u - v) = yNBY P u - yNBY P v := by
  simp only [yNBY, ymoment2Y, Pi.sub_apply, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem yNBY_smul_right (P u : Fin n → ℝ) (s : ℝ) : yNBY P (s • u) = s * yNBY P u := by
  simp only [yNBY, ymoment2Y, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The projection lands in `N_P`. -/
theorem chainProjN_mem_N {P g w : Fin n → ℝ} (hden : yNBY P g ≠ 0) :
    yNBY P (chainProjN P g w) = 0 := by
  rw [chainProjN, yNBY_sub_right, yNBY_smul_right]
  rw [div_mul_cancel₀ (yNBY P w) hden]
  ring

/-! ### The chain, bundled -/

/-- The six starting points of the chain, as y-vectors.

A nested product rather than a structure, so that the product topology and all the
`Prod` topology instances apply to it directly — Lemma C needs `IsOpen` and `Continuous`
on this type, and this Mathlib version has no `Equiv.inducedTopology` to transport a
topology onto a structure. Use the accessors `I.a`, `I.b`, `I.g`, `I.w1`, `I.w2`,
`I.w3` rather than the raw projections. -/
abbrev ChainYInputs (n : ℕ) :=
  (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ)

namespace ChainYInputs

/-- The first input, the direction `b` in step 1. -/
def a {n : ℕ} (I : ChainYInputs n) : Fin n → ℝ := I.1
/-- The second input. -/
def b {n : ℕ} (I : ChainYInputs n) : Fin n → ℝ := I.2.1
/-- The projection direction. -/
def g {n : ℕ} (I : ChainYInputs n) : Fin n → ℝ := I.2.2.1
/-- The first direction in step 2. -/
def w1 {n : ℕ} (I : ChainYInputs n) : Fin n → ℝ := I.2.2.2.1
/-- The second direction in step 2. -/
def w2 {n : ℕ} (I : ChainYInputs n) : Fin n → ℝ := I.2.2.2.2.1
/-- The third direction, used in step 3. -/
def w3 {n : ℕ} (I : ChainYInputs n) : Fin n → ℝ := I.2.2.2.2.2

/-- Rebuild a `ChainYInputs` from its six fields. -/
def mk {n : ℕ} (a : Fin n → ℝ) (b : Fin n → ℝ) (g : Fin n → ℝ) (w1 w2 w3 : Fin n → ℝ) :
    ChainYInputs n := (a, b, g, w1, w2, w3)

end ChainYInputs

/-- `P = a + λ₀ b`, the centre of the conic. -/
def chainP (I : ChainYInputs n) (lam : ℝ) : Fin n → ℝ := I.a + lam • I.b

/-- `w̃ⱼ = chainProjN P g Ywⱼ`. -/
def chainWt (I : ChainYInputs n) (lam : ℝ) (j : Fin 3) : Fin n → ℝ :=
  match j with
  | 0 => chainProjN (chainP I lam) I.g I.w1
  | 1 => chainProjN (chainP I lam) I.g I.w2
  | 2 => chainProjN (chainP I lam) I.g I.w3

def chainW1 (I : ChainYInputs n) (lam : ℝ) : Fin n → ℝ := chainWt I lam 0
def chainW2 (I : ChainYInputs n) (lam : ℝ) : Fin n → ℝ := chainWt I lam 1
def chainW3 (I : ChainYInputs n) (lam : ℝ) : Fin n → ℝ := chainWt I lam 2

/-- `q₀ = w̃₁ + x₂ w̃₂`, a point of the conic. -/
def chainQ0 (I : ChainYInputs n) (lam x : ℝ) : Fin n → ℝ := chainW1 I lam + x • chainW2 I lam

/-- The direction `d(μ) = μ w̃₁ + w̃₃`. -/
def chainD (I : ChainYInputs n) (lam mu : ℝ) : Fin n → ℝ :=
  mu • chainW1 I lam + chainW3 I lam

/-- `v = pt(μ)`, the second intersection of the line `chainD I lam mu` from `q₀` with
the conic. -/
def chainV (I : ChainYInputs n) (lam x mu : ℝ) : Fin n → ℝ :=
  chainConicPt (chainP I lam) (chainQ0 I lam x) (chainD I lam mu)

/-- The output y-vector `y = P + κ₀ v`. -/
def chainY (I : ChainYInputs n) (lam x mu kappa : ℝ) : Fin n → ℝ :=
  chainP I lam + kappa • chainV I lam x mu

def chainStep1' (I : ChainYInputs n) (lam : ℝ) : ℝ := chainStep1 I.a I.b lam

def chainStep2' (I : ChainYInputs n) (lam x : ℝ) : ℝ :=
  chainStep2 (chainP I lam) I.g (chainW1 I lam) (chainW2 I lam) x

def chainStep3' (I : ChainYInputs n) (lam x mu : ℝ) : ℝ :=
  chainStep3 (chainP I lam) (chainQ0 I lam x) (chainW1 I lam) (chainW3 I lam) mu

def chainStep4' (I : ChainYInputs n) (lam x mu kappa : ℝ) : ℝ :=
  chainStep4 (chainP I lam) (chainV I lam x mu) kappa

/-- A configuration is **good at** `(λ, x, μ, κ)` if all four steps vanish, the two
denominators are nonzero, and the output has pairwise distinct entries. -/
def ChainGood (I : ChainYInputs n) (lam x mu kappa : ℝ) : Prop :=
  chainStep1' I lam = 0 ∧ chainStep2' I lam x = 0 ∧ chainStep3' I lam x mu = 0 ∧
    chainStep4' I lam x mu kappa = 0 ∧ yNBY (chainP I lam) I.g ≠ 0 ∧
    yBdotY (chainP I lam) (chainD I lam mu) (chainD I lam mu) ≠ 0 ∧
    Function.Injective (chainY I lam x mu kappa)

/-! ### Lemma C: chain openness (PLAN §2.5)



The statement below is "Lemma C" of the plan, instantiated at the four concrete step

functions. Working backwards through the chain: the endpoint values of step `k` are

continuous and of opposite signs at the centre, so their signs survive on a neighbourhood

of `(I₀, x*₁, …, x*_{k−1})`; shrinking the earlier radii and the neighbourhood puts

everything inside those neighbourhoods, and then the IVT applies forwards.



The only wrinkle is that `chainStep2'` and `chainStep3'` are not defined everywhere —

`chainProjN` and `chainConicPt` divide. Restrict to the open set where both

denominators are nonzero, which contains the centre, and everything below is ordinary

continuity plus `intermediate_value_Icc`. -/

/- #### The compactness lemmas that Lemma C needs

The sign conditions of step `k` are asserted *uniformly* over the box of the earlier step

parameters, so what has to be shown is that they hold *simultaneously* for a whole

neighbourhood of the centre configuration — and for that one needs compactness, in the two

places below. `exists_tube_prod` is the classical tube lemma; it is what turns "for every

earlier parameter" into "uniformly in the earlier parameters". -/

/-! ### Continuity of the four step functions in their own step variable

Lemma C is applied one step at a time. Once the input `I` and the *earlier* parameters are
fixed, each step function is a one-dimensional rational function of its own parameter, and
the only thing an `intermediate_value_Icc` needs is the continuity proved below. Continuity
in `I` is a separate matter: it is needed only to move *sign conditions* from `I₀` to a
neighbouring input, never to produce a root.

The non-degeneracy conditions are the obvious ones: step 2 divides by `yNBY P g` and step 3
by `yBdotY P d d`, so their statements carry them; steps 1 and 4 divide by nothing. In each
case the denominator does not involve the step's own variable, so the condition is one on
the *earlier* parameters alone. -/

/-- Step 1 is a cubic in `λ`; `chainStep1` has no denominator. -/
theorem continuous_chainStep1' (I : ChainYInputs n) : Continuous (chainStep1' I) := by
  unfold chainStep1' chainStep1
  simp only [psumY, psumFinY, Pi.add_apply, Pi.smul_apply]
  fun_prop

/-- Step 2 is a quadratic in `x` with constant coefficients, so it is continuous for every
`I` and every `lam` — the `chainProjN` division sits inside `chainW1`/`chainW2`, which do not
depend on `x`. The `yNBY P g ≠ 0` hypothesis is therefore not needed here (it is kept as the
usable form, and it *is* needed by `exists_chain_roots_at_centre` itself, because the
`lam`-root it produces is what step 3 then divides by). -/
theorem continuous_chainStep2' (I : ChainYInputs n) (lam : ℝ)
    (_hden : yNBY (chainP I lam) I.g ≠ 0) :
    Continuous fun x => chainStep2' I lam x := by
  unfold chainStep2' chainStep2
  simp only [yConicY, ymoment2Y, Pi.add_apply, Pi.smul_apply]
  fun_prop

/-- Step 3 is rational in `μ` with the single denominator `yBdotY P d d`, so it is continuous
on every set on which that denominator does not vanish. -/
theorem continuousOn_chainStep3' (I : ChainYInputs n) (lam x : ℝ) {S : Set ℝ}
    (hS : ∀ mu ∈ S, yBdotY (chainP I lam) (chainD I lam mu) (chainD I lam mu) ≠ 0) :
    ContinuousOn (fun mu => chainStep3' I lam x mu) S := by
  -- the direction `d(μ)` is affine in `μ`, so the two pairings with it are continuous
  have hd : Continuous fun mu : ℝ => mu • chainW1 I lam + chainW3 I lam := by fun_prop
  have hnum : Continuous fun mu : ℝ =>
      2 * yBdotY (chainP I lam) (chainQ0 I lam x) (mu • chainW1 I lam + chainW3 I lam) := by
    unfold yBdotY ymoment3Y
    simp only [Pi.smul_apply, Pi.add_apply]
    fun_prop
  have hden : Continuous fun mu : ℝ =>
      yBdotY (chainP I lam) (mu • chainW1 I lam + chainW3 I lam)
        (mu • chainW1 I lam + chainW3 I lam) := by
    unfold yBdotY ymoment3Y
    simp only [Pi.smul_apply, Pi.add_apply]
    fun_prop
  -- one division, at the only place the step is not regular
  have hstep : ContinuousOn (fun mu : ℝ =>
      (2 * yBdotY (chainP I lam) (chainQ0 I lam x) (mu • chainW1 I lam + chainW3 I lam)) /
        yBdotY (chainP I lam) (mu • chainW1 I lam + chainW3 I lam)
          (mu • chainW1 I lam + chainW3 I lam)) S :=
    hnum.continuousOn.div hden.continuousOn hS
  have hpt : ContinuousOn (fun mu : ℝ =>
      chainQ0 I lam x - ((2 * yBdotY (chainP I lam) (chainQ0 I lam x)
        (mu • chainW1 I lam + chainW3 I lam)) /
        yBdotY (chainP I lam) (mu • chainW1 I lam + chainW3 I lam)
          (mu • chainW1 I lam + chainW3 I lam)) • (mu • chainW1 I lam + chainW3 I lam)) S :=
    continuousOn_const.sub (hstep.smul hd.continuousOn)
  -- `chainConicPt` is that point, and `psumY · 3` is continuous in the point
  have hc : Continuous (fun v : Fin n → ℝ => psumY v 3) := by
    unfold psumY psumFinY
    fun_prop
  exact hc.comp_continuousOn hpt

/-- Step 4 is a quintic in `κ`; `chainStep4` has no denominator. -/
theorem continuous_chainStep4' (I : ChainYInputs n) (lam x mu : ℝ) :
    Continuous fun kappa => chainStep4' I lam x mu kappa := by
  unfold chainStep4' chainStep4
  simp only [psumY, psumFinY, Pi.add_apply, Pi.smul_apply]
  fun_prop

/-! ### The part of Lemma C that *is* provable: a solution at the centre

Everything below is the `I₀`-half of `exists_chain_roots`: the four one-dimensional
`intermediate_value_Icc` applications that produce the four roots at the centre
configuration. The input direction, on which the rest of Lemma C depends, is where the
statement above fails. -/

/-- **A strict sign change at the two endpoints of an interval produces a root in its
interior.** Immediate from the open-interval intermediate value theorem: the endpoint values
are strictly opposite, so `0` lies in the open interval between them. -/
theorem exists_zero_of_sign_change_on {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (hs : f a * f b < 0) :
    ∃ t ∈ Set.Ioo a b, f t = 0 := by
  rcases mul_neg_iff.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact intermediate_value_Ioo' hab hf ⟨h2, h1⟩
  · exact intermediate_value_Ioo hab hf ⟨h1, h2⟩

/-- **A solution of the four chain equations at the centre, in the four open boxes** — the
`I₀`-half of `exists_chain_roots`, and the whole of it once the sign conditions are known to
hold near `I₀`. The two extra hypotheses `hpole2`, `hpole3` are exactly the non-degeneracy
conditions of the WARNING above: without them the step-`μ` interval may contain a pole of
`yBdotY P d d`, and a strict sign change at its two endpoints then yields no root. -/
theorem exists_chain_roots_at_centre (I₀ : ChainYInputs n)
    (c₁ c₂ c₃ c₄ eps₁ eps₂ eps₃ eps₄ : ℝ)
    (heps : 0 < eps₁ ∧ 0 < eps₂ ∧ 0 < eps₃ ∧ 0 < eps₄)
    (h1 : chainStep1' I₀ (c₁ - eps₁) * chainStep1' I₀ (c₁ + eps₁) < 0)
    (h2 : ∀ lam : ℝ, |lam - c₁| < eps₁ →
        chainStep2' I₀ lam (c₂ - eps₂) * chainStep2' I₀ lam (c₂ + eps₂) < 0)
    (h3 : ∀ lam x : ℝ, |lam - c₁| < eps₁ → |x - c₂| < eps₂ →
        chainStep3' I₀ lam x (c₃ - eps₃) * chainStep3' I₀ lam x (c₃ + eps₃) < 0)
    (h4 : ∀ lam x mu : ℝ, |lam - c₁| < eps₁ → |x - c₂| < eps₂ → |mu - c₃| < eps₃ →
        chainStep4' I₀ lam x mu (c₄ - eps₄) * chainStep4' I₀ lam x mu (c₄ + eps₄) < 0)
    (hpole2 : ∀ lam : ℝ, |lam - c₁| ≤ eps₁ → yNBY (chainP I₀ lam) I₀.g ≠ 0)
    (hpole3 : ∀ lam x mu : ℝ, |lam - c₁| ≤ eps₁ → |x - c₂| ≤ eps₂ → |mu - c₃| ≤ eps₃ →
        yBdotY (chainP I₀ lam) (chainD I₀ lam mu) (chainD I₀ lam mu) ≠ 0) :
    ∃ lam x mu kappa : ℝ,
      |lam - c₁| < eps₁ ∧ |x - c₂| < eps₂ ∧ |mu - c₃| < eps₃ ∧ |kappa - c₄| < eps₄ ∧
      chainStep1' I₀ lam = 0 ∧ chainStep2' I₀ lam x = 0 ∧ chainStep3' I₀ lam x mu = 0 ∧
      chainStep4' I₀ lam x mu kappa = 0 := by
  -- step 1: `chainStep1` has no denominator
  obtain ⟨lam, hlam, hstep1⟩ :=
    exists_zero_of_sign_change_on (a := c₁ - eps₁) (b := c₁ + eps₁) (by linarith [heps.1])
      (continuous_chainStep1' I₀).continuousOn h1
  have hlam' : |lam - c₁| < eps₁ := by
    rw [abs_lt]; constructor <;> linarith [hlam.1, hlam.2]
  -- step 2: the only non-degeneracy needed is `hpole2`, and `h2` then applies
  obtain ⟨x, hx, hstep2⟩ :=
    exists_zero_of_sign_change_on (a := c₂ - eps₂) (b := c₂ + eps₂) (by linarith [heps.2.1])
      (continuous_chainStep2' I₀ lam (hpole2 lam hlam'.le)).continuousOn (h2 lam hlam')
  have hx' : |x - c₂| < eps₂ := by
    rw [abs_lt]; constructor <;> linarith [hx.1, hx.2]
  -- step 3: `hpole3` is needed on the whole closed interval, hence the `ContinuousOn`
  have hS : ∀ mu ∈ Set.Icc (c₃ - eps₃) (c₃ + eps₃),
      yBdotY (chainP I₀ lam) (chainD I₀ lam mu) (chainD I₀ lam mu) ≠ 0 := by
    intro mu hmu
    apply hpole3 lam x mu
    · exact hlam'.le
    · exact hx'.le
    · rw [abs_le]; obtain ⟨hm1, hm2⟩ := Set.mem_Icc.mp hmu
      exact ⟨by linarith, by linarith⟩
  obtain ⟨mu, hmu, hstep3⟩ :=
    exists_zero_of_sign_change_on (a := c₃ - eps₃) (b := c₃ + eps₃) (by linarith [heps.2.2.1])
      (continuousOn_chainStep3' I₀ lam x hS) (h3 lam x hlam' hx')
  have hmu' : |mu - c₃| < eps₃ := by
    rw [abs_lt]; constructor <;> linarith [hmu.1, hmu.2]
  -- step 4: `chainStep4` has no denominator
  obtain ⟨kappa, hkappa, hstep4⟩ :=
    exists_zero_of_sign_change_on (a := c₄ - eps₄) (b := c₄ + eps₄) (by linarith [heps.2.2.2])
      (continuous_chainStep4' I₀ lam x mu).continuousOn (h4 lam x mu hlam' hx' hmu')
  have hkappa' : |kappa - c₄| < eps₄ := by
    rw [abs_lt]; constructor <;> linarith [hkappa.1, hkappa.2]
  exact ⟨lam, x, mu, kappa, hlam', hx', hmu', hkappa', hstep1, hstep2, hstep3, hstep4⟩

/-! ### Continuity ingredients for the local chain lemma

The step functions `chainStep2'`, `chainStep3'`, `chainStep4'` are rational: they are
continuous exactly where their denominators do not vanish. The lemmas below record that,
in the joint `(I, earlier parameters)` form the tube argument needs, together with the
elementary "a strict inequality at a point persists on a coordinate box" facts. -/

/-- From `U ∈ 𝓝 a` in `ℝ`, extract a positive radius whose open interval lies in `U`. -/
private lemma nhds_real_ball {a : ℝ} {U : Set ℝ} (hU : U ∈ nhds a) :
    ∃ δ > 0, ∀ t : ℝ, |t - a| < δ → t ∈ U := by
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU
  exact ⟨ε, hε, fun t ht => hεU (by rwa [Metric.mem_ball, Real.dist_eq])⟩

/-- A strict inequality at a point of `ℝ × ℝ` persists on a coordinate box. -/
private lemma exists_box_pair {φ : ℝ → ℝ → ℝ} {a b : ℝ}
    (hφ : ContinuousAt (Function.uncurry φ) (a, b)) (h0 : φ a b < 0) :
    ∃ δ₁ > 0, ∃ δ₂ > 0, ∀ lam x : ℝ, |lam - a| < δ₁ → |x - b| < δ₂ → φ lam x < 0 := by
  have hs : (Function.uncurry φ) ⁻¹' (Set.Iio (0 : ℝ)) ∈ nhds (a, b) :=
    hφ.preimage_mem_nhds (isOpen_Iio.mem_nhds (show Function.uncurry φ (a, b) < 0 from h0))
  rw [nhds_prod_eq] at hs
  obtain ⟨U, hU, V, hV, hUV⟩ := Filter.mem_prod_iff.mp hs
  obtain ⟨δ₁, hδ₁, hU'⟩ := nhds_real_ball hU
  obtain ⟨δ₂, hδ₂, hV'⟩ := nhds_real_ball hV
  exact ⟨δ₁, hδ₁, δ₂, hδ₂, fun lam x hl hx => by
    have hmem : (lam, x) ∈ U ×ˢ V := ⟨hU' lam hl, hV' x hx⟩
    have := hUV hmem
    simpa [Function.uncurry] using this⟩

/-- The three-variable analogue of `exists_box_pair`. -/
private lemma exists_box_triple {ψ : ℝ × ℝ × ℝ → ℝ} {a b c : ℝ}
    (hψ : ContinuousAt ψ (a, b, c)) (h0 : ψ (a, b, c) < 0) :
    ∃ δ₁ > 0, ∃ δ₂ > 0, ∃ δ₃ > 0, ∀ lam x mu : ℝ,
      |lam - a| < δ₁ → |x - b| < δ₂ → |mu - c| < δ₃ → ψ (lam, x, mu) < 0 := by
  have hs : ψ ⁻¹' (Set.Iio (0 : ℝ)) ∈ nhds (a, b, c) :=
    hψ.preimage_mem_nhds (isOpen_Iio.mem_nhds h0)
  rw [nhds_prod_eq] at hs
  obtain ⟨U, hU, V, hV, hUV⟩ := Filter.mem_prod_iff.mp hs
  obtain ⟨δ₁, hδ₁, hU'⟩ := nhds_real_ball hU
  rw [nhds_prod_eq] at hV
  obtain ⟨V₁, hV₁, V₂, hV₂, hV₁₂⟩ := Filter.mem_prod_iff.mp hV
  obtain ⟨δ₂, hδ₂, hV₁'⟩ := nhds_real_ball hV₁
  obtain ⟨δ₃, hδ₃, hV₂'⟩ := nhds_real_ball hV₂
  exact ⟨δ₁, hδ₁, δ₂, hδ₂, δ₃, hδ₃, fun lam x mu hl hx hm => by
    have hmem : (lam, (x, mu)) ∈ U ×ˢ V := ⟨hU' lam hl, hV₁₂ ⟨hV₁' x hx, hV₂' mu hm⟩⟩
    exact hUV hmem⟩

/-- The step-1 denominator `yNBY (chainP I lam) I.g`, jointly continuous in `(I, lam)`. -/
private lemma continuous_joint_den1 :
    Continuous (fun p : ChainYInputs n × ℝ => yNBY (chainP p.1 p.2) p.1.g) := by
  simp only [yNBY, ymoment2Y, chainP, ChainYInputs.g, ChainYInputs.a, ChainYInputs.b]
  fun_prop

/-- `chainStep2' I lam x`, continuous at a point where the `lam`-denominator is nonzero. -/
private lemma continuousAt_chainStep2'_fixed (I₀ : ChainYInputs n) (lam x : ℝ)
    (h : yNBY (chainP I₀ lam) I₀.g ≠ 0) :
    ContinuousAt (fun p : ChainYInputs n × ℝ => chainStep2' p.1 p.2 x) (I₀, lam) := by
  simp only [chainStep2', chainStep2, chainProjN, chainP, chainW1, chainW2, chainWt,
    ChainYInputs.g, ChainYInputs.a, ChainYInputs.b, ChainYInputs.w1, ChainYInputs.w2,
    yConicY, ymoment2Y, yNBY]
  fun_prop (disch := assumption)

/-- `chainStep3' I lam x mu`, continuous at a point where both denominators are nonzero. -/
private lemma continuousAt_chainStep3'_fixed (I₀ : ChainYInputs n) (lam x mu : ℝ)
    (h1 : yNBY (chainP I₀ lam) I₀.g ≠ 0)
    (h2 : yBdotY (chainP I₀ lam) (chainD I₀ lam mu) (chainD I₀ lam mu) ≠ 0) :
    ContinuousAt (fun q : ChainYInputs n × (ℝ × ℝ) =>
      chainStep3' q.1 q.2.1 q.2.2 mu) (I₀, (lam, x)) := by
  simp only [chainStep3', chainStep3, chainConicPt, chainQ0, chainW1, chainW2,
    chainW3, chainWt, chainProjN, chainP, ChainYInputs.g, ChainYInputs.a, ChainYInputs.b,
    ChainYInputs.w1, ChainYInputs.w2, ChainYInputs.w3, psumY, psumFinY, ymoment2Y,
    yBdotY, ymoment3Y, yNBY]
  fun_prop (disch := assumption)

/-- `chainStep4' I lam x mu kappa`, continuous at a point where both denominators are
nonzero. -/
private lemma continuousAt_chainStep4'_fixed (I₀ : ChainYInputs n) (lam x mu kappa : ℝ)
    (h1 : yNBY (chainP I₀ lam) I₀.g ≠ 0)
    (h2 : yBdotY (chainP I₀ lam) (chainD I₀ lam mu) (chainD I₀ lam mu) ≠ 0) :
    ContinuousAt (fun q : ChainYInputs n × (ℝ × ℝ × ℝ) =>
      chainStep4' q.1 q.2.1 q.2.2.1 q.2.2.2 kappa) (I₀, (lam, x, mu)) := by
  simp only [chainStep4', chainStep4, chainV, chainConicPt, chainD, chainQ0, chainW1,
    chainW2, chainW3, chainWt, chainProjN, chainP, ChainYInputs.g, ChainYInputs.a,
    ChainYInputs.b, ChainYInputs.w1, ChainYInputs.w2, ChainYInputs.w3, psumY, psumFinY,
    ymoment2Y, yBdotY, ymoment3Y, yNBY]
  fun_prop (disch := assumption)

/-- The step-3 denominator expression, continuous at points where `yNBY (chainP I lam) I.g`
is nonzero. -/
private lemma continuousAt_den2 (I₀ : ChainYInputs n) (lam mu : ℝ)
    (h : yNBY (chainP I₀ lam) I₀.g ≠ 0) :
    ContinuousAt (fun q : ChainYInputs n × (ℝ × ℝ) =>
      yBdotY (chainP q.1 q.2.1) (chainD q.1 q.2.1 q.2.2)
        (chainD q.1 q.2.1 q.2.2)) (I₀, (lam, mu)) := by
  simp only [yBdotY, ymoment3Y, chainD, chainP, ChainYInputs.g, ChainYInputs.a,
    ChainYInputs.b, ChainYInputs.w1, ChainYInputs.w3, chainW1, chainW3, chainWt,
    chainProjN, yNBY, ymoment2Y, Pi.add_apply, Pi.smul_apply]
  fun_prop (disch := assumption)

/-- `exists_nhds_forall_ne` with only *pointwise* continuity at the points `(x₀, y)`,
`y ∈ K`; the nonvanishing counterpart of `exists_nhds_forall_lt_of_continuousAt`. -/
private theorem exists_nhds_forall_ne_of_continuousAt {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {K : Set Y} (hK : IsCompact K) {φ : X → Y → ℝ} {x₀ : X}
    (hφ : ∀ y ∈ K, ContinuousAt (Function.uncurry φ) (x₀, y))
    (h0 : ∀ y ∈ K, φ x₀ y ≠ 0) :
    ∃ U ∈ nhds x₀, ∀ x ∈ U, ∀ y ∈ K, φ x y ≠ 0 := by
  rw [← Filter.eventually_iff_exists_mem]
  exact hK.eventually_forall_of_forall_eventually fun y hy =>
    (hφ y hy).preimage_mem_nhds (isOpen_compl_singleton.mem_nhds (h0 y hy))

/-- Membership in `Icc (c - δ) (c + δ)` is `|t - c| ≤ δ`. -/
private lemma mem_Icc_abs {c δ t : ℝ} (_hδ : 0 ≤ δ) :
    t ∈ Set.Icc (c - δ) (c + δ) ↔ |t - c| ≤ δ := by
  simp [abs_sub_le_iff, and_comm, add_comm]

/-- **Local Lemma C** (PLAN-addendum §2.1). Below the centre sign data `hs1`–`hs4` and the
two denominator nonvanishing conditions `hden1`, `hden2` at `I₀`, the four chain roots exist
for every configuration in an open neighbourhood `U` of `I₀`, within the prescribed open
boxes.

Unlike `exists_chain_roots`, no *uniform* sign data and no `hpole1`/`hpole2` are assumed:
the radii are shrunk adaptively so that the step-3 pole — the only obstruction at `I₀` — stays
outside the `μ`-window, and the centre sign data then opens up by continuity. -/
theorem exists_chain_roots_local (I₀ : ChainYInputs n)
    (c₁ c₂ c₃ c₄ ε₁ ε₂ ε₃ ε₄ : ℝ)
    (heps : 0 < ε₁ ∧ 0 < ε₂ ∧ 0 < ε₃ ∧ 0 < ε₄)
    (hs1 : ∀ δ, 0 < δ → δ < ε₁ →
      chainStep1' I₀ (c₁ - δ) * chainStep1' I₀ (c₁ + δ) < 0)
    (hs2 : ∀ δ, 0 < δ → δ < ε₂ →
      chainStep2' I₀ c₁ (c₂ - δ) * chainStep2' I₀ c₁ (c₂ + δ) < 0)
    (hs3 : ∀ δ, 0 < δ → δ < ε₃ →
      chainStep3' I₀ c₁ c₂ (c₃ - δ) * chainStep3' I₀ c₁ c₂ (c₃ + δ) < 0)
    (hs4 : ∀ δ, 0 < δ → δ < ε₄ →
      chainStep4' I₀ c₁ c₂ c₃ (c₄ - δ) * chainStep4' I₀ c₁ c₂ c₃ (c₄ + δ) < 0)
    (hden1 : yNBY (chainP I₀ c₁) I₀.g ≠ 0)
    (hden2 : yBdotY (chainP I₀ c₁) (chainD I₀ c₁ c₃) (chainD I₀ c₁ c₃) ≠ 0) :
    ∃ U : Set (ChainYInputs n), IsOpen U ∧ I₀ ∈ U ∧
      ∀ I ∈ U, ∃ lam x mu kappa : ℝ,
        |lam - c₁| < ε₁ ∧ |x - c₂| < ε₂ ∧ |mu - c₃| < ε₃ ∧ |kappa - c₄| < ε₄ ∧
        chainStep1' I lam = 0 ∧ chainStep2' I lam x = 0 ∧ chainStep3' I lam x mu = 0 ∧
        chainStep4' I lam x mu kappa = 0 ∧
        yNBY (chainP I lam) I.g ≠ 0 ∧
        yBdotY (chainP I lam) (chainD I lam mu) (chainD I lam mu) ≠ 0 := by
  -- ## Continuity of the two centre denominators
  have hden1_cont : Continuous (fun lam : ℝ => yNBY (chainP I₀ lam) I₀.g) := by
    simp only [yNBY, ymoment2Y, chainP, ChainYInputs.g, ChainYInputs.a, ChainYInputs.b]
    fun_prop
  have hden2_cont : Continuous (fun mu : ℝ =>
      yBdotY (chainP I₀ c₁) (chainD I₀ c₁ mu) (chainD I₀ c₁ mu)) := by
    simp only [yBdotY, ymoment3Y, chainD, chainP, chainW1, chainW3, chainWt, chainProjN,
      ChainYInputs.g, ChainYInputs.a, ChainYInputs.b, ChainYInputs.w1, ChainYInputs.w3,
      yNBY, ymoment2Y]
    fun_prop (disch := assumption)
  -- ## The two radii supplied by the centre denominators
  have hU1 : {lam : ℝ | yNBY (chainP I₀ lam) I₀.g ≠ 0} ∈ nhds c₁ :=
    hden1_cont.continuousAt.preimage_mem_nhds
      (isOpen_compl_singleton.mem_nhds (show yNBY (chainP I₀ c₁) I₀.g ≠ (0 : ℝ) from hden1))
  obtain ⟨r1, hr1pos, hr1⟩ := nhds_real_ball hU1
  have hU2 : {mu : ℝ | yBdotY (chainP I₀ c₁) (chainD I₀ c₁ mu) (chainD I₀ c₁ mu) ≠ 0}
      ∈ nhds c₃ :=
    hden2_cont.continuousAt.preimage_mem_nhds
      (isOpen_compl_singleton.mem_nhds
        (show yBdotY (chainP I₀ c₁) (chainD I₀ c₁ c₃) (chainD I₀ c₁ c₃) ≠ (0 : ℝ)
          from hden2))
  obtain ⟨r2, hr2pos, hr2⟩ := nhds_real_ball hU2
  -- ## The outer radius `δ₄` and the step-4 box at the centre
  set δ₄ : ℝ := ε₄ / 2 with hδ₄def
  have hδ₄pos : 0 < δ₄ := by rw [hδ₄def]; linarith [heps.2.2.2]
  have hδ₄lt : δ₄ < ε₄ := by rw [hδ₄def]; linarith [heps.2.2.2]
  have hcont4 : ContinuousAt (fun y : ℝ × ℝ × ℝ =>
      chainStep4' I₀ y.1 y.2.1 y.2.2 (c₄ - δ₄) *
        chainStep4' I₀ y.1 y.2.1 y.2.2 (c₄ + δ₄)) (c₁, c₂, c₃) := by
    simp only [chainStep4', chainStep4, chainV, chainConicPt, chainD, chainQ0, chainW1,
      chainW2, chainW3, chainWt, chainProjN, chainP, ChainYInputs.g, ChainYInputs.a,
      ChainYInputs.b, ChainYInputs.w1, ChainYInputs.w2, ChainYInputs.w3, psumY, psumFinY,
      ymoment2Y, yBdotY, ymoment3Y, yNBY]
    fun_prop (disch := assumption)
  obtain ⟨re1, hre1pos, re2, hre2pos, re3, hre3pos, hbox4⟩ :=
    exists_box_triple (a := c₁) (b := c₂) (c := c₃)
      (ψ := fun y : ℝ × ℝ × ℝ => chainStep4' I₀ y.1 y.2.1 y.2.2 (c₄ - δ₄) *
        chainStep4' I₀ y.1 y.2.1 y.2.2 (c₄ + δ₄)) hcont4
      (hs4 δ₄ hδ₄pos hδ₄lt)
  -- ## The step-3 window radius `δ₃`
  set δ₃ : ℝ := min (min (ε₃ / 2) (r2 / 2)) (re3 / 2) with hδ₃def
  have hδ₃pos : 0 < δ₃ := by
    rw [hδ₃def]
    exact lt_min (lt_min (by linarith [heps.2.2.1]) (by linarith)) (by linarith)
  have hδ₃ltε : δ₃ < ε₃ := by
    rw [hδ₃def]
    have h1 := min_le_left (min (ε₃ / 2) (r2 / 2)) (re3 / 2)
    have h2 := min_le_left (ε₃ / 2) (r2 / 2)
    linarith [heps.2.2.1]
  have hδ₃ltr2 : δ₃ < r2 := by
    rw [hδ₃def]
    have h1 := min_le_left (min (ε₃ / 2) (r2 / 2)) (re3 / 2)
    have h2 := min_le_right (ε₃ / 2) (r2 / 2)
    linarith [hr2pos]
  have hδ₃ltre3 : δ₃ < re3 := by
    rw [hδ₃def]
    have h1 := min_le_right (min (ε₃ / 2) (r2 / 2)) (re3 / 2)
    linarith [hre3pos]
  set K₃ : Set ℝ := Set.Icc (c₃ - δ₃) (c₃ + δ₃) with hK₃def
  have hK3 : IsCompact K₃ := by rw [hK₃def]; exact isCompact_Icc
  have hδ₃nn : (0 : ℝ) ≤ δ₃ := le_of_lt hδ₃pos
  -- ## The step-3 sign box at the centre, fixing `δ₃`
  have hden2m : yBdotY (chainP I₀ c₁) (chainD I₀ c₁ (c₃ - δ₃))
      (chainD I₀ c₁ (c₃ - δ₃)) ≠ 0 := by
    refine hr2 (c₃ - δ₃) ?_
    rw [show c₃ - δ₃ - c₃ = -δ₃ by ring, abs_neg, abs_of_pos hδ₃pos]
    exact hδ₃ltr2
  have hden2p : yBdotY (chainP I₀ c₁) (chainD I₀ c₁ (c₃ + δ₃))
      (chainD I₀ c₁ (c₃ + δ₃)) ≠ 0 := by
    refine hr2 (c₃ + δ₃) ?_
    rw [show c₃ + δ₃ - c₃ = δ₃ by ring, abs_of_pos hδ₃pos]
    exact hδ₃ltr2
  have hcont3 : ContinuousAt (Function.uncurry (fun lam x : ℝ =>
      chainStep3' I₀ lam x (c₃ - δ₃) * chainStep3' I₀ lam x (c₃ + δ₃))) (c₁, c₂) := by
    change ContinuousAt (fun p : ℝ × ℝ =>
      chainStep3' I₀ p.1 p.2 (c₃ - δ₃) * chainStep3' I₀ p.1 p.2 (c₃ + δ₃)) (c₁, c₂)
    simp only [chainStep3', chainStep3, chainConicPt, chainQ0, chainW1, chainW2,
      chainW3, chainWt, chainProjN, chainP, ChainYInputs.g, ChainYInputs.a, ChainYInputs.b,
      ChainYInputs.w1, ChainYInputs.w2, ChainYInputs.w3, psumY, psumFinY, ymoment2Y,
      yBdotY, ymoment3Y, yNBY]
    fun_prop (disch := assumption)
  obtain ⟨rd1, hrd1pos, rd2, hrd2pos, hbox3⟩ :=
    exists_box_pair (a := c₁) (b := c₂)
      (φ := fun lam x : ℝ => chainStep3' I₀ lam x (c₃ - δ₃) *
        chainStep3' I₀ lam x (c₃ + δ₃)) hcont3
      (hs3 δ₃ hδ₃pos hδ₃ltε)
  -- ## The second radius `δ₂`
  set δ₂ : ℝ := min (min (ε₂ / 2) (rd2 / 2)) (re2 / 2) with hδ₂def
  have hδ₂pos : 0 < δ₂ := by
    rw [hδ₂def]
    exact lt_min (lt_min (by linarith [heps.2.1]) (by linarith)) (by linarith)
  have hδ₂ltε : δ₂ < ε₂ := by
    rw [hδ₂def]
    have h1 := min_le_left (min (ε₂ / 2) (rd2 / 2)) (re2 / 2)
    have h2 := min_le_left (ε₂ / 2) (rd2 / 2)
    linarith [heps.2.1]
  have hδ₂ltrd2 : δ₂ < rd2 := by
    rw [hδ₂def]
    have h1 := min_le_left (min (ε₂ / 2) (rd2 / 2)) (re2 / 2)
    have h2 := min_le_right (ε₂ / 2) (rd2 / 2)
    linarith [hrd2pos]
  have hδ₂ltre2 : δ₂ < re2 := by
    rw [hδ₂def]
    have h1 := min_le_right (min (ε₂ / 2) (rd2 / 2)) (re2 / 2)
    linarith [hre2pos]
  -- ## The step-2 sign neighbourhood at the centre
  have hstep2_cont : ContinuousAt (fun lam : ℝ =>
      chainStep2' I₀ lam (c₂ - δ₂) * chainStep2' I₀ lam (c₂ + δ₂)) c₁ := by
    simp only [chainStep2', chainStep2, chainProjN, chainP, chainW1, chainW2, chainWt,
      ChainYInputs.g, ChainYInputs.a, ChainYInputs.b, ChainYInputs.w1, ChainYInputs.w2,
      yConicY, ymoment2Y, yNBY]
    fun_prop (disch := assumption)
  have hstep2_val : chainStep2' I₀ c₁ (c₂ - δ₂) * chainStep2' I₀ c₁ (c₂ + δ₂) < 0 :=
    hs2 δ₂ hδ₂pos hδ₂ltε
  have hU2s : {lam : ℝ |
      chainStep2' I₀ lam (c₂ - δ₂) * chainStep2' I₀ lam (c₂ + δ₂) < 0} ∈ nhds c₁ :=
    hstep2_cont.preimage_mem_nhds (isOpen_Iio.mem_nhds hstep2_val)
  obtain ⟨rs1, hrs1pos, hrs1⟩ := nhds_real_ball hU2s
  -- ## `yBdotY` stays nonzero on `K₃` for `lam` near `c₁`
  obtain ⟨Ut, hUt, hUt'⟩ :=
    exists_nhds_forall_ne_of_continuousAt (K := K₃) hK3
      (φ := fun lam mu => yBdotY (chainP I₀ lam) (chainD I₀ lam mu) (chainD I₀ lam mu))
      (x₀ := c₁)
      (fun mu hmu => by
        change ContinuousAt (fun p : ℝ × ℝ =>
          yBdotY (chainP I₀ p.1) (chainD I₀ p.1 p.2) (chainD I₀ p.1 p.2)) (c₁, mu)
        simp only [yBdotY, ymoment3Y, chainD, chainP, ChainYInputs.g, ChainYInputs.a,
          ChainYInputs.b, ChainYInputs.w1, ChainYInputs.w3, chainW1, chainW3, chainWt,
          chainProjN, yNBY, ymoment2Y, Pi.add_apply, Pi.smul_apply]
        fun_prop (disch := assumption))
      (fun mu hmu => hr2 mu (lt_of_le_of_lt ((mem_Icc_abs hδ₃nn).mp hmu) hδ₃ltr2))
  obtain ⟨rt1, hrt1pos, hrt1⟩ := nhds_real_ball hUt
  -- ## The first radius `δ₁`
  set δ₁ : ℝ :=
    min (min (min (min (min (ε₁ / 2) (r1 / 2)) (rt1 / 2)) (rd1 / 2)) (re1 / 2)) (rs1 / 2)
    with hδ₁def
  have hδ₁pos : 0 < δ₁ := by
    rw [hδ₁def]
    exact lt_min
      (lt_min (lt_min (lt_min (lt_min (by linarith [heps.1]) (by linarith)) (by linarith))
        (by linarith)) (by linarith)) (by linarith)
  have hδ₁ltε : δ₁ < ε₁ := by
    rw [hδ₁def]
    have h1 := min_le_left
      (min (min (min (min (ε₁ / 2) (r1 / 2)) (rt1 / 2)) (rd1 / 2)) (re1 / 2)) (rs1 / 2)
    have h2 := min_le_left
      (min (min (min (ε₁ / 2) (r1 / 2)) (rt1 / 2)) (rd1 / 2)) (re1 / 2)
    have h3 := min_le_left (min (min (ε₁ / 2) (r1 / 2)) (rt1 / 2)) (rd1 / 2)
    have h4 := min_le_left (min (ε₁ / 2) (r1 / 2)) (rt1 / 2)
    have h5 := min_le_left (ε₁ / 2) (r1 / 2)
    linarith [heps.1]
  have hδ₁ltr1 : δ₁ < r1 := by
    rw [hδ₁def]
    have h1 := min_le_left
      (min (min (min (min (ε₁ / 2) (r1 / 2)) (rt1 / 2)) (rd1 / 2)) (re1 / 2)) (rs1 / 2)
    have h2 := min_le_left
      (min (min (min (ε₁ / 2) (r1 / 2)) (rt1 / 2)) (rd1 / 2)) (re1 / 2)
    have h3 := min_le_left (min (min (ε₁ / 2) (r1 / 2)) (rt1 / 2)) (rd1 / 2)
    have h4 := min_le_left (min (ε₁ / 2) (r1 / 2)) (rt1 / 2)
    have h5 := min_le_right (ε₁ / 2) (r1 / 2)
    linarith [hr1pos]
  have hδ₁ltrt1 : δ₁ < rt1 := by
    rw [hδ₁def]
    have h1 := min_le_left
      (min (min (min (min (ε₁ / 2) (r1 / 2)) (rt1 / 2)) (rd1 / 2)) (re1 / 2)) (rs1 / 2)
    have h2 := min_le_left
      (min (min (min (ε₁ / 2) (r1 / 2)) (rt1 / 2)) (rd1 / 2)) (re1 / 2)
    have h3 := min_le_left (min (min (ε₁ / 2) (r1 / 2)) (rt1 / 2)) (rd1 / 2)
    have h4 := min_le_right (min (ε₁ / 2) (r1 / 2)) (rt1 / 2)
    linarith [hrt1pos]
  have hδ₁ltrd1 : δ₁ < rd1 := by
    rw [hδ₁def]
    have h1 := min_le_left
      (min (min (min (min (ε₁ / 2) (r1 / 2)) (rt1 / 2)) (rd1 / 2)) (re1 / 2)) (rs1 / 2)
    have h2 := min_le_left
      (min (min (min (ε₁ / 2) (r1 / 2)) (rt1 / 2)) (rd1 / 2)) (re1 / 2)
    have h3 := min_le_right (min (min (ε₁ / 2) (r1 / 2)) (rt1 / 2)) (rd1 / 2)
    linarith [hrd1pos]
  have hδ₁ltre1 : δ₁ < re1 := by
    rw [hδ₁def]
    have h1 := min_le_left
      (min (min (min (min (ε₁ / 2) (r1 / 2)) (rt1 / 2)) (rd1 / 2)) (re1 / 2)) (rs1 / 2)
    have h2 := min_le_right
      (min (min (min (ε₁ / 2) (r1 / 2)) (rt1 / 2)) (rd1 / 2)) (re1 / 2)
    linarith [hre1pos]
  have hδ₁ltrs1 : δ₁ < rs1 := by
    rw [hδ₁def]
    have h1 := min_le_right
      (min (min (min (min (ε₁ / 2) (r1 / 2)) (rt1 / 2)) (rd1 / 2)) (re1 / 2)) (rs1 / 2)
    linarith [hrs1pos]
  -- ## The final boxes and the membership rewrites
  set K₁ : Set ℝ := Set.Icc (c₁ - δ₁) (c₁ + δ₁) with hK₁def
  set K₂ : Set ℝ := Set.Icc (c₂ - δ₂) (c₂ + δ₂) with hK₂def
  have hK1 : IsCompact K₁ := by rw [hK₁def]; exact isCompact_Icc
  have hK2 : IsCompact K₂ := by rw [hK₂def]; exact isCompact_Icc
  have hδ₁nn : (0 : ℝ) ≤ δ₁ := le_of_lt hδ₁pos
  have hδ₂nn : (0 : ℝ) ≤ δ₂ := le_of_lt hδ₂pos
  have hK1m : ∀ lam, lam ∈ K₁ ↔ |lam - c₁| ≤ δ₁ := by
    intro lam; rw [hK₁def]; exact mem_Icc_abs hδ₁nn
  have hK2m : ∀ x, x ∈ K₂ ↔ |x - c₂| ≤ δ₂ := by
    intro x; rw [hK₂def]; exact mem_Icc_abs hδ₂nn
  have hK3m : ∀ mu, mu ∈ K₃ ↔ |mu - c₃| ≤ δ₃ := by
    intro mu; rw [hK₃def]; exact mem_Icc_abs hδ₃nn
  -- ## The centre conditions over the closed boxes
  have j1 : ∀ lam, |lam - c₁| ≤ δ₁ → yNBY (chainP I₀ lam) I₀.g ≠ 0 :=
    fun lam hl => hr1 lam (lt_of_le_of_lt hl hδ₁ltr1)
  have j2 : ∀ lam mu, |lam - c₁| ≤ δ₁ → |mu - c₃| ≤ δ₃ →
      yBdotY (chainP I₀ lam) (chainD I₀ lam mu) (chainD I₀ lam mu) ≠ 0 :=
    fun lam mu hl hm => hUt' lam (hrt1 lam (lt_of_le_of_lt hl hδ₁ltrt1)) mu ((hK3m mu).mpr hm)
  have j3 : ∀ lam, |lam - c₁| ≤ δ₁ →
      chainStep2' I₀ lam (c₂ - δ₂) * chainStep2' I₀ lam (c₂ + δ₂) < 0 :=
    fun lam hl => hrs1 lam (lt_of_le_of_lt hl hδ₁ltrs1)
  have j4 : ∀ lam x, |lam - c₁| ≤ δ₁ → |x - c₂| ≤ δ₂ →
      chainStep3' I₀ lam x (c₃ - δ₃) * chainStep3' I₀ lam x (c₃ + δ₃) < 0 :=
    fun lam x hl hx => hbox3 lam x (lt_of_le_of_lt hl hδ₁ltrd1) (lt_of_le_of_lt hx hδ₂ltrd2)
  have j5 : ∀ lam x mu, |lam - c₁| ≤ δ₁ → |x - c₂| ≤ δ₂ → |mu - c₃| ≤ δ₃ →
      chainStep4' I₀ lam x mu (c₄ - δ₄) * chainStep4' I₀ lam x mu (c₄ + δ₄) < 0 :=
    fun lam x mu hl hx hm => hbox4 lam x mu (lt_of_le_of_lt hl hδ₁ltre1)
      (lt_of_le_of_lt hx hδ₂ltre2) (lt_of_le_of_lt hm hδ₃ltre3)
  -- (a) step-2 sign, uniform over `K₁`
  obtain ⟨Ua, hUa, hUa'⟩ :=
    exists_nhds_forall_lt_of_continuousAt (K := K₁) hK1
      (φ := fun I lam => chainStep2' I lam (c₂ - δ₂) * chainStep2' I lam (c₂ + δ₂))
      (x₀ := I₀)
      (fun lam hlam => by
        change ContinuousAt (fun q : ChainYInputs n × ℝ =>
          chainStep2' q.1 q.2 (c₂ - δ₂) * chainStep2' q.1 q.2 (c₂ + δ₂)) (I₀, lam)
        have hden := j1 lam ((hK1m lam).mp hlam)
        exact (continuousAt_chainStep2'_fixed I₀ lam (c₂ - δ₂) hden).mul
          (continuousAt_chainStep2'_fixed I₀ lam (c₂ + δ₂) hden))
      (fun lam hlam => j3 lam ((hK1m lam).mp hlam))
  -- (b) `yNBY` nonvanishing, uniform over `K₁`
  obtain ⟨Ub, hUb, hUb'⟩ :=
    exists_nhds_forall_ne (K := K₁) hK1
      (φ := fun I lam => yNBY (chainP I lam) I.g) continuous_joint_den1
      (fun lam hlam => j1 lam ((hK1m lam).mp hlam))
  -- (c) step-3 sign, uniform over `K₁ × K₂`
  obtain ⟨Uc, hUc, hUc'⟩ :=
    exists_nhds_forall_lt_of_continuousAt (K := K₁ ×ˢ K₂) (hK1.prod hK2)
      (φ := fun I y => chainStep3' I y.1 y.2 (c₃ - δ₃) * chainStep3' I y.1 y.2 (c₃ + δ₃))
      (x₀ := I₀)
      (fun y hy => by
        change ContinuousAt (fun q : ChainYInputs n × (ℝ × ℝ) =>
          chainStep3' q.1 q.2.1 q.2.2 (c₃ - δ₃) *
            chainStep3' q.1 q.2.1 q.2.2 (c₃ + δ₃)) (I₀, y)
        obtain ⟨hl, hx⟩ := hy
        have hden := j1 y.1 ((hK1m y.1).mp hl)
        exact (continuousAt_chainStep3'_fixed I₀ y.1 y.2 (c₃ - δ₃) hden
            (j2 y.1 (c₃ - δ₃) ((hK1m y.1).mp hl) (by
              rw [show c₃ - δ₃ - c₃ = -δ₃ by ring, abs_neg, abs_of_pos hδ₃pos]))).mul
          (continuousAt_chainStep3'_fixed I₀ y.1 y.2 (c₃ + δ₃) hden
            (j2 y.1 (c₃ + δ₃) ((hK1m y.1).mp hl) (by
              rw [show c₃ + δ₃ - c₃ = δ₃ by ring, abs_of_pos hδ₃pos]))))
      (fun y hy => by
        obtain ⟨hl, hx⟩ := hy
        exact j4 y.1 y.2 ((hK1m y.1).mp hl) ((hK2m y.2).mp hx))
  -- (d) step-3 denominator nonvanishing, uniform over `K₁ × K₃`
  obtain ⟨Ud, hUd, hUd'⟩ :=
    exists_nhds_forall_ne_of_continuousAt (K := K₁ ×ˢ K₃) (hK1.prod hK3)
      (φ := fun I y => yBdotY (chainP I y.1) (chainD I y.1 y.2) (chainD I y.1 y.2))
      (x₀ := I₀)
      (fun y hy => by
        change ContinuousAt (fun q : ChainYInputs n × (ℝ × ℝ) =>
          yBdotY (chainP q.1 q.2.1) (chainD q.1 q.2.1 q.2.2)
            (chainD q.1 q.2.1 q.2.2)) (I₀, y)
        exact continuousAt_den2 I₀ y.1 y.2 (j1 y.1 ((hK1m y.1).mp hy.1)))
      (fun y hy => j2 y.1 y.2 ((hK1m y.1).mp hy.1) ((hK3m y.2).mp hy.2))
  -- (e) step-4 sign, uniform over `K₁ × (K₂ × K₃)`
  obtain ⟨Ue, hUe, hUe'⟩ :=
    exists_nhds_forall_lt_of_continuousAt (K := K₁ ×ˢ (K₂ ×ˢ K₃)) (hK1.prod (hK2.prod hK3))
      (φ := fun I y => chainStep4' I y.1 y.2.1 y.2.2 (c₄ - δ₄) *
        chainStep4' I y.1 y.2.1 y.2.2 (c₄ + δ₄))
      (x₀ := I₀)
      (fun (y : ℝ × ℝ × ℝ) hy => by
        change ContinuousAt (fun q : ChainYInputs n × (ℝ × ℝ × ℝ) =>
          chainStep4' q.1 q.2.1 q.2.2.1 q.2.2.2 (c₄ - δ₄) *
            chainStep4' q.1 q.2.1 q.2.2.1 q.2.2.2 (c₄ + δ₄)) (I₀, y)
        have hden := j1 y.1 ((hK1m y.1).mp hy.1)
        exact (continuousAt_chainStep4'_fixed I₀ y.1 y.2.1 y.2.2 (c₄ - δ₄) hden
            (j2 y.1 y.2.2 ((hK1m y.1).mp hy.1) ((hK3m y.2.2).mp hy.2.2))).mul
          (continuousAt_chainStep4'_fixed I₀ y.1 y.2.1 y.2.2 (c₄ + δ₄) hden
            (j2 y.1 y.2.2 ((hK1m y.1).mp hy.1) ((hK3m y.2.2).mp hy.2.2))))
      (fun (y : ℝ × ℝ × ℝ) hy => by
        exact j5 y.1 y.2.1 y.2.2 ((hK1m y.1).mp hy.1) ((hK2m y.2.1).mp hy.2.1)
          ((hK3m y.2.2).mp hy.2.2))
  -- (f) step-1 sign at the two fixed points
  have hf_cont : Continuous (fun I : ChainYInputs n =>
      chainStep1' I (c₁ - δ₁) * chainStep1' I (c₁ + δ₁)) := by
    simp only [chainStep1', chainStep1, psumY, psumFinY, ChainYInputs.a, ChainYInputs.b,
      Pi.add_apply, Pi.smul_apply]
    fun_prop
  have hf_val : chainStep1' I₀ (c₁ - δ₁) * chainStep1' I₀ (c₁ + δ₁) < 0 :=
    hs1 δ₁ hδ₁pos hδ₁ltε
  set Uf : Set (ChainYInputs n) :=
    {I | chainStep1' I (c₁ - δ₁) * chainStep1' I (c₁ + δ₁) < 0} with hUfdef
  have hUf : Uf ∈ nhds I₀ := by
    rw [hUfdef]
    exact hf_cont.continuousAt.preimage_mem_nhds (isOpen_Iio.mem_nhds hf_val)
  -- ## Assemble the neighbourhood and apply the forward IVT lemma
  have hV : (Ua ∩ Ub ∩ Uc ∩ Ud ∩ Ue ∩ Uf) ∈ nhds I₀ :=
    Filter.inter_mem (Filter.inter_mem (Filter.inter_mem (Filter.inter_mem
      (Filter.inter_mem hUa hUb) hUc) hUd) hUe) hUf
  refine ⟨interior (Ua ∩ Ub ∩ Uc ∩ Ud ∩ Ue ∩ Uf), isOpen_interior,
    mem_interior_iff_mem_nhds.mpr hV, ?_⟩
  intro I hI
  have hIV : I ∈ Ua ∩ Ub ∩ Uc ∩ Ud ∩ Ue ∩ Uf := interior_subset hI
  rw [Set.mem_inter_iff, Set.mem_inter_iff, Set.mem_inter_iff, Set.mem_inter_iff,
    Set.mem_inter_iff] at hIV
  obtain ⟨⟨⟨⟨⟨hIa, hIb⟩, hIc⟩, hId⟩, hIe⟩, hIf⟩ := hIV
  obtain ⟨lam, x, mu, kappa, hlam, hx, hmu, hkappa, e1, e2, e3, e4⟩ :=
    exists_chain_roots_at_centre I c₁ c₂ c₃ c₄ δ₁ δ₂ δ₃ δ₄
      ⟨hδ₁pos, hδ₂pos, hδ₃pos, hδ₄pos⟩
      (by simpa [hUfdef] using hIf)
      (fun lam hl => hUa' I hIa lam ((hK1m lam).mpr (le_of_lt hl)))
      (fun lam x hl hx => hUc' I hIc (lam, x) ⟨(hK1m lam).mpr (le_of_lt hl),
        (hK2m x).mpr (le_of_lt hx)⟩)
      (fun lam x mu hl hx hm => hUe' I hIe (lam, (x, mu))
        ⟨(hK1m lam).mpr (le_of_lt hl), (hK2m x).mpr (le_of_lt hx),
          (hK3m mu).mpr (le_of_lt hm)⟩)
      (fun lam hl => hUb' I hIb lam ((hK1m lam).mpr hl))
      (fun lam x mu hl hx hm => hUd' I hId (lam, mu)
        ⟨(hK1m lam).mpr hl, (hK3m mu).mpr hm⟩)
  exact ⟨lam, x, mu, kappa, lt_trans hlam hδ₁ltε, lt_trans hx hδ₂ltε,
    lt_trans hmu hδ₃ltε, lt_trans hkappa hδ₄lt, e1, e2, e3, e4,
    hUb' I hIb lam ((hK1m lam).mpr (le_of_lt hlam)),
    hUd' I hId (lam, mu)
      ⟨(hK1m lam).mpr (le_of_lt hlam), (hK3m mu).mpr (le_of_lt hmu)⟩⟩

/-! ### The rational certificates (PLAN §2.4)



The centre data below are *y*-vectors, not `b`-vectors. That is the point: the chain

algebra and the openness argument are properties of y-space alone, independent of `q`, so

one rational configuration suffices to open up an open set that `YSpace`'s density

argument can then reach with a P-constructible `b`. -/



/-- The `n = 7` centre: `β* = (1, −1, 2, −2, 3, −3, 0)`,

`v* = (−6, −5, 3, 2, 3, −4, 7)`, `P = β* + v* = (−5, −6, 5, 0, 6, −7, 7)`. -/
def centre7a : Fin 7 → ℝ := ![(-5 : ℝ), -6, 5, 0, 6, -7, 7]

def centre7b : Fin 7 → ℝ := ![6, -1, 1, 0, 3, 0, -9]

def centre7g : Fin 7 → ℝ := ![2, 1, -1, -6, 1, -2 / 3, 11 / 3]

def centre7w1 : Fin 7 → ℝ :=
  ![(-495 : ℝ) / 74, -379 / 74, 1489 / 444, 293 / 148, 565 / 148, -397 / 148, 593 / 111]

def centre7w2 : Fin 7 → ℝ :=
  ![51 / 37, 9 / 37, -157 / 222, 3 / 74, -121 / 74, -195 / 74, 368 / 111]

def centre7w3 : Fin 7 → ℝ :=
  ![239 / 148, -535 / 74, 425 / 148, 463 / 148, -1901 / 148, -8071 / 444, 13603 / 444]



def centre7 : ChainYInputs 7 :=
  (centre7a, centre7b, centre7g, centre7w1, centre7w2, centre7w3)


/-- The certified roots for `n = 7`: `λ₀ = 0`, `x₂ = 1/2`, `μ₀ = 8064/617`,

`κ₀ = −9136536/1150016105`. -/
def centre7roots : ℝ × ℝ × ℝ × ℝ :=
  (0, 1 / 2, 8064 / 617, -1)



/-- All four step equations vanish at the certified roots for `n = 7`, so the chain

really does reach a good output. Closed by one `norm_num` per clause.



**Why the plan's `κ₀` had to be corrected.** PLAN §2.4 lists `κ₀ = -9136536/1150016105`, but

that is the root of the step-4 polynomial evaluated with the **denominator-cleared** conic

point

`v_clear = ⟨P, d, d⟩·v = q₀·⟨P, d, d⟩ - 2·⟨P, q₀, d⟩·d` — the vector appearing inside

`chainStep3Cleared` — rather than with `chainConicPt` itself; the plan's own listed step-4

derivative `-5750080525/761378` is exactly `d/dκ Σᵢ (Pᵢ + κ v_clear i)⁵` at that `κ`, which

pins the mix-up. At the plan's value step 4 does *not* vanish:

```
chainStep4' centre7 0 1/2 (8064/617) (-9136536/1150016105)
  = -1703784516280773884693283100658894194915262592
    /16091984241384364559468418508534986804502525
```

The root of step 4 against `chainV` is `κ₀ = -1`, and there

`chainY centre7 0 1/2 (8064/617) (-1) = ![(1 : ℝ), -1, 2, -2, 3, -3, 0] = β*`, exactly as

the `centre7` docstring says. `centre7roots` uses `-1`; with it all four clauses are exact

rational identities. -/
theorem centre7_solves :
    chainStep1' centre7 (centre7roots.1) = 0 ∧
      chainStep2' centre7 centre7roots.1 centre7roots.2.1 = 0 ∧
      chainStep3' centre7 centre7roots.1 centre7roots.2.1 centre7roots.2.2.1 = 0 ∧
      chainStep4' centre7 centre7roots.1 centre7roots.2.1 centre7roots.2.2.1
        centre7roots.2.2.2 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    norm_num [chainStep1', chainStep1, chainStep2', chainStep2, chainStep3', chainStep3,
      chainStep4', chainStep4, psumY, psumFinY, yConicY, yNBY, yBdotY, ymoment2Y, ymoment3Y,
      chainProjN, chainConicPt, chainP, chainQ0, chainD, chainV, chainY, chainW1, chainW2,
      chainW3, chainWt, ChainYInputs.a, ChainYInputs.b, ChainYInputs.g, ChainYInputs.w1,
      ChainYInputs.w2, ChainYInputs.w3, centre7, centre7roots, centre7a, centre7b, centre7g,
      centre7w1, centre7w2, centre7w3, Fin.sum_univ_succ, Pi.add_apply, Pi.smul_apply,
      Pi.sub_apply, smul_eq_mul]



/-- `⟨P², g⟩ = 244 ≠ 0` at the `n = 7` centre, so the projection is defined. -/
theorem centre7_denom1 : yNBY (chainP centre7 centre7roots.1) centre7g ≠ 0 := by
  norm_num [yNBY, ymoment2Y, psumY, psumFinY, chainP, ChainYInputs.a, ChainYInputs.b,
    centre7, centre7roots, centre7a, centre7b, centre7g, Fin.sum_univ_succ]



theorem centre7_denom2 :
    yBdotY (chainP centre7 centre7roots.1) (chainD centre7 centre7roots.1 centre7roots.2.2.1)
      (chainD centre7 centre7roots.1 centre7roots.2.2.1) ≠ 0 := by
  norm_num [yBdotY, ymoment3Y, yNBY, ymoment2Y, psumY, psumFinY, chainProjN, chainD, chainW1,
    chainW3, chainWt, chainP, ChainYInputs.a, ChainYInputs.g, ChainYInputs.w1, ChainYInputs.w3,
    centre7, centre7roots, centre7a, centre7b, centre7g, centre7w1, centre7w3,
    Fin.sum_univ_succ, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]



/-- The `n = 7` output at the certified roots is exactly

`![(1 : ℝ), -1, 2, -2, 3, -3, 0] = β*`, whose seven entries are pairwise distinct, so the

lemma is true. (PLAN §2.4 lists the output for the *plan's* `κ₀`; at the corrected `κ₀ = −1` it

is `β*`, as the `centre7` docstring says.)

The proof has two halves. `key` evaluates the chain output coordinatewise: seven `fin_cases`

plus `norm_num`, because a `![...]` literal is only something `norm_num` can evaluate at a

*concrete* `Fin` index, and each value is reached by unfolding the whole chain. Injectivity of

a concrete `Fin 7 → ℝ` list is then just pairwise distinctness of its entries — `fin_cases` on

the two witnesses and `norm_num` on the resulting equality of two distinct integers. -/
theorem centre7_inj : Function.Injective (chainY centre7 centre7roots.1 centre7roots.2.1
    centre7roots.2.2.1 centre7roots.2.2.2) := by
  have key : chainY centre7 centre7roots.1 centre7roots.2.1 centre7roots.2.2.1
      centre7roots.2.2.2 = (![(1 : ℝ), -1, 2, -2, 3, -3, 0] : Fin 7 → ℝ) := by
    funext i
    fin_cases i <;>
      norm_num [chainY, chainP, chainV, chainConicPt, yBdotY, ymoment3Y, yNBY, ymoment2Y,
        chainQ0, chainD, chainW1, chainW2, chainW3, chainWt, chainProjN, psumFinY,
        ChainYInputs.a, ChainYInputs.b, ChainYInputs.g, ChainYInputs.w1, ChainYInputs.w2,
        ChainYInputs.w3, centre7, centre7a, centre7b, centre7g, centre7w1, centre7w2,
        centre7w3, centre7roots, Fin.sum_univ_succ, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
        smul_eq_mul]
  rw [key]
  intro x y hxy
  fin_cases x <;> fin_cases y <;> first | rfl | (norm_num at hxy)






/-- The `n = 8` centre: `β* = (1, 2, 3, 4, −1, −2, −3, −4)`,

`v* = (−5, −4, −1, −5, 2, 6, 4, 3)`, `P = (−4, −2, 2, −1, 1, 4, 1, −1)`. -/
def centre8a : Fin 8 → ℝ := ![(-4 : ℝ), -2, 2, -1, 1, 4, 1, -1]

def centre8b : Fin 8 → ℝ := ![0, 3, 0, 2, 1, -1, -6, 1]

def centre8g : Fin 8 → ℝ := ![1, -2 / 3, 0, -1, 1, 3 / 2, 2 / 3, -5 / 2]

def centre8w1 : Fin 8 → ℝ :=
  ![(-143 : ℝ) / 21, -113 / 21, -22 / 21, -452 / 63, -18 / 7, 170 / 21, -24 / 7, 1154 / 63]

def centre8w2 : Fin 8 → ℝ :=
  ![38 / 35, 29 / 35, 1 / 35, 137 / 105, 96 / 35, -44 / 35, 156 / 35, -193 / 21]

def centre8w3 : Fin 8 → ℝ :=
  ![167 / 35, -89 / 35, 184 / 35, -272 / 105, -501 / 35, -186 / 35, -101 / 35, 370 / 21]



def centre8 : ChainYInputs 8 :=
  (centre8a, centre8b, centre8g, centre8w1, centre8w2, centre8w3)


/-- The certified roots for `n = 8`: `λ₀ = 0`, `x₂ = 5/3`, `μ₀ = −5322/2915`,
`κ₀ = −1`.

**CORRECTION TO PLAN §2.4**, exactly as for `centre7roots`: the plan's
`κ₀ = −160325/27427952` is the root against the denominator-cleared conic point, not
against `chainV`. Against `chainV` the root is `κ₀ = −1`, and there
`chainY = β* = (1, 2, 3, 4, −1, −2, −3, −4)` exactly. -/
def centre8roots : ℝ × ℝ × ℝ × ℝ :=
  (0, 5 / 3, -5322 / 2915, -1)



/-- All four step equations vanish at the certified roots for `n = 8`. Closed by one

`norm_num` per clause, exactly as for `n = 7`; and the same `κ₀` correction applies: the

plan's `-160325/27427952` is the root against the denominator-cleared conic point, not

against `chainV`.

```
chainStep4' centre8 0 5/3 (-5322/2915) (-160325/27427952)
  = -9834308341891810502731781571516538125
    /1940335890025012126126570523329429504
```

Against `chainV` the root is `κ₀ = -1`, where
`chainY centre8 0 5/3 (-5322/2915) (-1) = ![(1 : ℝ), 2, 3, 4, -1, -2, -3, -4] = β*`. -/
theorem centre8_solves :
    chainStep1' centre8 (centre8roots.1) = 0 ∧
      chainStep2' centre8 centre8roots.1 centre8roots.2.1 = 0 ∧
      chainStep3' centre8 centre8roots.1 centre8roots.2.1 centre8roots.2.2.1 = 0 ∧
      chainStep4' centre8 centre8roots.1 centre8roots.2.1 centre8roots.2.2.1
        centre8roots.2.2.2 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    norm_num [chainStep1', chainStep1, chainStep2', chainStep2, chainStep3', chainStep3,
      chainStep4', chainStep4, psumY, psumFinY, yConicY, yNBY, yBdotY, ymoment2Y, ymoment3Y,
      chainProjN, chainConicPt, chainP, chainQ0, chainD, chainV, chainY, chainW1, chainW2,
      chainW3, chainWt, ChainYInputs.a, ChainYInputs.b, ChainYInputs.g, ChainYInputs.w1,
      ChainYInputs.w2, ChainYInputs.w3, centre8, centre8roots, centre8a, centre8b, centre8g,
      centre8w1, centre8w2, centre8w3, Fin.sum_univ_succ, Pi.add_apply, Pi.smul_apply,
      Pi.sub_apply, smul_eq_mul]



theorem centre8_denom1 : yNBY (chainP centre8 centre8roots.1) centre8g ≠ 0 := by
  norm_num [yNBY, ymoment2Y, psumY, psumFinY, chainP, ChainYInputs.a, ChainYInputs.b,
    centre8, centre8roots, centre8a, centre8b, centre8g, Fin.sum_univ_succ]



theorem centre8_denom2 :
    yBdotY (chainP centre8 centre8roots.1) (chainD centre8 centre8roots.1 centre8roots.2.2.1)
      (chainD centre8 centre8roots.1 centre8roots.2.2.1) ≠ 0 := by
  norm_num [yBdotY, ymoment3Y, yNBY, ymoment2Y, psumY, psumFinY, chainProjN, chainD, chainW1,
    chainW3, chainWt, chainP, ChainYInputs.a, ChainYInputs.g, ChainYInputs.w1, ChainYInputs.w3,
    centre8, centre8roots, centre8a, centre8b, centre8g, centre8w1, centre8w3,
    Fin.sum_univ_succ, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]



/-- The `n = 8` output at the certified roots is exactly

`![(1 : ℝ), 2, 3, 4, -1, -2, -3, -4] = β*`, whose eight entries are pairwise distinct. Same

two-step proof as `centre7_inj`: evaluate the chain output at each of the eight `Fin` indices,

then check pairwise distinctness. -/
theorem centre8_inj : Function.Injective (chainY centre8 centre8roots.1 centre8roots.2.1
    centre8roots.2.2.1 centre8roots.2.2.2) := by
  have key : chainY centre8 centre8roots.1 centre8roots.2.1 centre8roots.2.2.1
      centre8roots.2.2.2 = (![(1 : ℝ), 2, 3, 4, -1, -2, -3, -4] : Fin 8 → ℝ) := by
    funext i
    fin_cases i <;>
      norm_num [chainY, chainP, chainV, chainConicPt, yBdotY, ymoment3Y, yNBY, ymoment2Y,
        chainQ0, chainD, chainW1, chainW2, chainW3, chainWt, chainProjN, psumFinY,
        ChainYInputs.a, ChainYInputs.b, ChainYInputs.g, ChainYInputs.w1, ChainYInputs.w2,
        ChainYInputs.w3, centre8, centre8a, centre8b, centre8g, centre8w1, centre8w2,
        centre8w3, centre8roots, Fin.sum_univ_succ, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
        smul_eq_mul]
  rw [key]
  intro x y hxy
  fin_cases x <;> fin_cases y <;> first | rfl | (norm_num at hxy)




/-! ### Strict sign changes at *every* sufficiently small radius

`signChange_of_factorization_eventually` produces, for each `ε > 0`, *one* radius `δ < ε`
at which the sign change is visible. The hypotheses `hs1`–`hs4` of
`exists_chain_roots_local` need the stronger uniform form: a *single* `ε` below which the
sign change holds at *every* `δ`. The proof is the same continuity-plus-factorization
argument as the existing lemma, read without the intermediate `∃ δ`. -/

private theorem exists_forall_signChange_of_factorization {f G : ℝ → ℝ} {x₀ : ℝ}
    (hG : ContinuousAt G x₀) (hG0 : G x₀ ≠ 0)
    (hfac : ∀ᶠ t in nhds x₀, f t = (t - x₀) * G t) :
    ∃ ε > 0, ∀ δ, 0 < δ → δ < ε → f (x₀ - δ) * f (x₀ + δ) < 0 := by
  -- `G` keeps the sign of `G x₀` on a ball …
  have hpos : ∀ᶠ t in nhds x₀, 0 < G t * G x₀ := by
    have hcont : ContinuousAt (fun t => G t * G x₀) x₀ := hG.mul continuousAt_const
    exact hcont.eventually (isOpen_Ioi.mem_nhds (mul_self_pos.mpr hG0))
  rw [Metric.eventually_nhds_iff] at hpos
  obtain ⟨r₁, hr₁, hball₁⟩ := hpos
  -- … and the factorization holds on a ball.
  rw [Metric.eventually_nhds_iff] at hfac
  obtain ⟨r₂, hr₂, hball₂⟩ := hfac
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, fun δ hδ hδε => ?_⟩
  have hδr₁ : δ < r₁ := lt_of_lt_of_le hδε (min_le_left _ _)
  have hδr₂ : δ < r₂ := lt_of_lt_of_le hδε (min_le_right _ _)
  have hdisk (t : ℝ) (ht : dist t x₀ < r₂) : f t = (t - x₀) * G t := hball₂ (y := t) ht
  have hdistp : dist (x₀ + δ) x₀ < r₂ := by
    rw [Real.dist_eq]
    have h : x₀ + δ - x₀ = δ := by ring
    rw [h, abs_of_pos hδ]; exact hδr₂
  have hdistm : dist (x₀ - δ) x₀ < r₂ := by
    rw [Real.dist_eq]
    have h : x₀ - δ - x₀ = -δ := by ring
    rw [h, abs_neg, abs_of_pos hδ]; exact hδr₂
  have hsignp : 0 < G (x₀ + δ) * G x₀ := by
    apply hball₁ (y := x₀ + δ)
    rw [Real.dist_eq]
    have h : x₀ + δ - x₀ = δ := by ring
    rw [h, abs_of_pos hδ]; exact hδr₁
  have hsignm : 0 < G (x₀ - δ) * G x₀ := by
    apply hball₁ (y := x₀ - δ)
    rw [Real.dist_eq]
    have h : x₀ - δ - x₀ = -δ := by ring
    rw [h, abs_neg, abs_of_pos hδ]; exact hδr₁
  rw [hdisk (x₀ - δ) hdistm, hdisk (x₀ + δ) hdistp]
  have e1 : x₀ - δ - x₀ = -δ := by ring
  have e2 : x₀ + δ - x₀ = δ := by ring
  rw [e1, e2]
  have hprod : 0 < G (x₀ - δ) * G (x₀ + δ) := by
    have hm : 0 < (G (x₀ - δ) * G x₀) * (G (x₀ + δ) * G x₀) := mul_pos hsignm hsignp
    have e : (G (x₀ - δ) * G x₀) * (G (x₀ + δ) * G x₀)
        = (G (x₀ - δ) * G (x₀ + δ)) * (G x₀) ^ 2 := by ring
    rw [e] at hm
    exact pos_of_mul_pos_left hm (sq_nonneg (G x₀))
  have e3 : (-δ * G (x₀ - δ)) * (δ * G (x₀ + δ))
      = -((δ * δ) * (G (x₀ - δ) * G (x₀ + δ))) := by ring
  rw [e3]
  have hq : 0 < (δ * δ) * (G (x₀ - δ) * G (x₀ + δ)) := mul_pos (mul_pos hδ hδ) hprod
  linarith

/-! ### The quintic power sum along a line

The step-4 function is `κ ↦ psumY (P + κ • v) 5`, a quintic. Expanding the fifth power
binomial-wise gives its coefficients as the mixed moments `ymoment2Y u v (5 − j) j`; this
is the degree-5 analogue of `psumY_cube_eq`. -/

private theorem psumY_add_smul_five (u v : Fin n → ℝ) (s : ℝ) :
    psumY (u + s • v) 5 =
      psumY u 5 + 5 * s * ymoment2Y u v 4 1 + 10 * s ^ 2 * ymoment2Y u v 3 2
        + 10 * s ^ 3 * ymoment2Y u v 2 3 + 5 * s ^ 4 * ymoment2Y u v 1 4
        + s ^ 5 * psumY v 5 := by
  simp only [psumY, psumFinY, ymoment2Y, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ### The four centre-`n = 7` sign changes, uniformly in the radius -/

/-- Step 1 at `centre7` is a cubic vanishing at `λ = 0`, with cofactor
`3⟨a², b⟩ + 3λ⟨a, b²⟩ + λ²S₃(b)`; `psumY_cube_eq` writes it in exactly this shape. -/
private theorem centre7_step1_sign :
    ∃ ε > 0, ∀ δ, 0 < δ → δ < ε →
      chainStep1' centre7 (0 - δ) * chainStep1' centre7 (0 + δ) < 0 := by
  have hP3 : psumY centre7a 3 = 0 := by
    norm_num [psumY, psumFinY, centre7a, Fin.sum_univ_succ]
  have hfac : ∀ t : ℝ, chainStep1' centre7 t
      = (t - 0) * (3 * yNBY centre7a centre7b + 3 * t * yConicY centre7a centre7b
          + t ^ 2 * psumY centre7b 3) := by
    intro t
    simp only [chainStep1', chainStep1, centre7, ChainYInputs.a, ChainYInputs.b]
    rw [psumY_cube_eq, hP3]
    ring
  refine exists_forall_signChange_of_factorization (f := chainStep1' centre7)
    (G := fun t => 3 * yNBY centre7a centre7b + 3 * t * yConicY centre7a centre7b
      + t ^ 2 * psumY centre7b 3) ?_ ?_ (Filter.Eventually.of_forall hfac)
  · fun_prop
  · norm_num [yNBY, ymoment2Y, yConicY, psumY, psumFinY, centre7a, centre7b, Fin.sum_univ_succ]

/-- `Q_P(u) = yConicY P u = ∑ᵢ YPᵢ·(Yuᵢ)²` is a **quadratic** form in `u`, *not* a linear
functional: `yConicY P (u + v) ≠ yConicY P u + yConicY P v` in general (the cross term
`2∑ᵢ YPᵢ·Yuᵢ·Yvᵢ` survives). So the right tool is the full expansion along an affine
line, `u + s·w`, whose middle coefficient is the *mixed* pairing `yBdotY P u w`. That is
what makes step 2 a genuine quadratic in `x`, of degree `2`. -/
theorem yConicY_add_smul_right (P u w : Fin n → ℝ) (s : ℝ) :
    yConicY P (u + s • w) = yConicY P u + 2 * s * yBdotY P u w + s ^ 2 * yConicY P w := by
  simp only [yConicY, ymoment2Y, yBdotY, ymoment3Y, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Step 2 at `centre7` is a quadratic vanishing at `x = 1/2`, with linear cofactor
`Q(w̃₂)·x − 2Q(w̃₁)`. The expansion `yConicY_add_smul_right` provides the coefficients. -/
private theorem centre7_step2_sign :
    ∃ ε > 0, ∀ δ, 0 < δ → δ < ε →
      chainStep2' centre7 0 (1 / 2 - δ) * chainStep2' centre7 0 (1 / 2 + δ) < 0 := by
  have hexp : ∀ x : ℝ, chainStep2' centre7 0 x
      = yConicY (chainP centre7 0) (chainProjN (chainP centre7 0) centre7.g (chainW1 centre7 0))
        + 2 * x * yBdotY (chainP centre7 0)
            (chainProjN (chainP centre7 0) centre7.g (chainW1 centre7 0))
            (chainProjN (chainP centre7 0) centre7.g (chainW2 centre7 0))
        + x ^ 2 * yConicY (chainP centre7 0)
            (chainProjN (chainP centre7 0) centre7.g (chainW2 centre7 0)) := by
    intro x
    rw [show chainStep2' centre7 0 x = yConicY (chainP centre7 0)
        (chainProjN (chainP centre7 0) centre7.g (chainW1 centre7 0)
          + x • chainProjN (chainP centre7 0) centre7.g (chainW2 centre7 0)) from rfl,
      yConicY_add_smul_right]
  have hroot : yConicY (chainP centre7 0)
        (chainProjN (chainP centre7 0) centre7.g (chainW1 centre7 0))
      = -yBdotY (chainP centre7 0)
          (chainProjN (chainP centre7 0) centre7.g (chainW1 centre7 0))
          (chainProjN (chainP centre7 0) centre7.g (chainW2 centre7 0))
        - yConicY (chainP centre7 0)
          (chainProjN (chainP centre7 0) centre7.g (chainW2 centre7 0)) / 4 := by
    have h := centre7_solves.2.1
    rw [show centre7roots.1 = (0 : ℝ) from rfl, show centre7roots.2.1 = (1 / 2 : ℝ) from rfl]
      at h
    rw [hexp (1 / 2)] at h
    ring_nf at h ⊢
    linarith [h]
  have hfac : ∀ x : ℝ, chainStep2' centre7 0 x
      = (x - 1 / 2) * (yConicY (chainP centre7 0)
            (chainProjN (chainP centre7 0) centre7.g (chainW2 centre7 0)) * x
          - 2 * yConicY (chainP centre7 0)
            (chainProjN (chainP centre7 0) centre7.g (chainW1 centre7 0))) := by
    intro x
    rw [hexp x, hroot]
    ring
  refine exists_forall_signChange_of_factorization (f := fun x => chainStep2' centre7 0 x)
    (G := fun x => yConicY (chainP centre7 0)
          (chainProjN (chainP centre7 0) centre7.g (chainW2 centre7 0)) * x
        - 2 * yConicY (chainP centre7 0)
          (chainProjN (chainP centre7 0) centre7.g (chainW1 centre7 0)))
    ?_ ?_ (Filter.Eventually.of_forall hfac)
  · fun_prop
  · norm_num [yConicY, ymoment2Y, chainP, chainW1, chainW2, chainWt, chainProjN, yNBY,
      ChainYInputs.a, ChainYInputs.b, ChainYInputs.g, ChainYInputs.w1, ChainYInputs.w2,
      centre7, centre7a, centre7b, centre7g, centre7w1, centre7w2, Fin.sum_univ_succ,
      Pi.add_apply, Pi.sub_apply, smul_eq_mul]

/-- Step 4 at `centre7` is a quintic vanishing at `κ = −1`. Shifting the line to
`(P − v) + (κ + 1)v` makes the vanishing at `κ = −1` the *constant* coefficient, so the
cofactor is read off directly from `psumY_add_smul_five`. -/
private theorem centre7_step4_sign :
    ∃ ε > 0, ∀ δ, 0 < δ → δ < ε →
      chainStep4' centre7 0 (1 / 2) (8064 / 617) (-1 - δ) *
        chainStep4' centre7 0 (1 / 2) (8064 / 617) (-1 + δ) < 0 := by
  have hshift : ∀ κ : ℝ, chainP centre7 0 + κ • chainV centre7 0 (1 / 2) (8064 / 617)
      = (chainP centre7 0 - chainV centre7 0 (1 / 2) (8064 / 617))
        + (κ + 1) • chainV centre7 0 (1 / 2) (8064 / 617) := by
    intro κ
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have h00 : psumY (chainP centre7 0 - chainV centre7 0 (1 / 2) (8064 / 617)) 5 = 0 := by
    have h := centre7_solves.2.2.2
    rw [show centre7roots.1 = (0 : ℝ) from rfl, show centre7roots.2.1 = (1 / 2 : ℝ) from rfl,
      show centre7roots.2.2.1 = (8064 / 617 : ℝ) from rfl,
      show centre7roots.2.2.2 = (-1 : ℝ) from rfl] at h
    rw [show chainStep4' centre7 0 (1 / 2) (8064 / 617) (-1)
        = psumY (chainP centre7 0 + (-1 : ℝ) • chainV centre7 0 (1 / 2) (8064 / 617)) 5
        from rfl] at h
    rw [show chainP centre7 0 + (-1 : ℝ) • chainV centre7 0 (1 / 2) (8064 / 617)
        = chainP centre7 0 - chainV centre7 0 (1 / 2) (8064 / 617) from by
          ext i
          simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          ring] at h
    exact h
  have hM : ymoment2Y (chainP centre7 0 - chainV centre7 0 (1 / 2) (8064 / 617))
      (chainV centre7 0 (1 / 2) (8064 / 617)) 4 1 ≠ 0 := by
    norm_num [ymoment2Y, chainV, chainConicPt, chainQ0, chainD, chainW1, chainW2, chainW3,
      chainWt, chainProjN, yBdotY, ymoment3Y, yNBY, chainP, ChainYInputs.a, ChainYInputs.b,
      ChainYInputs.g, ChainYInputs.w1, ChainYInputs.w2, ChainYInputs.w3, centre7, centre7a,
      centre7b, centre7g, centre7w1, centre7w2, centre7w3, Fin.sum_univ_succ, Pi.add_apply,
      Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  have hfac : ∀ κ : ℝ, chainStep4' centre7 0 (1 / 2) (8064 / 617) κ = (κ - (-1)) *
      (5 * ymoment2Y (chainP centre7 0 - chainV centre7 0 (1 / 2) (8064 / 617))
            (chainV centre7 0 (1 / 2) (8064 / 617)) 4 1
        + (κ + 1) * (10 * ymoment2Y (chainP centre7 0 - chainV centre7 0 (1 / 2) (8064 / 617))
              (chainV centre7 0 (1 / 2) (8064 / 617)) 3 2
          + 10 * (κ + 1) * ymoment2Y (chainP centre7 0 - chainV centre7 0 (1 / 2) (8064 / 617))
              (chainV centre7 0 (1 / 2) (8064 / 617)) 2 3
          + 5 * (κ + 1) ^ 2 * ymoment2Y (chainP centre7 0 - chainV centre7 0 (1 / 2) (8064 / 617))
              (chainV centre7 0 (1 / 2) (8064 / 617)) 1 4
          + (κ + 1) ^ 3 * psumY (chainV centre7 0 (1 / 2) (8064 / 617)) 5)) := by
    intro κ
    rw [show chainStep4' centre7 0 (1 / 2) (8064 / 617) κ
        = psumY (chainP centre7 0 + κ • chainV centre7 0 (1 / 2) (8064 / 617)) 5
        from rfl, hshift κ, psumY_add_smul_five, h00]
    ring
  have hG0 : (fun κ : ℝ =>
        5 * ymoment2Y (chainP centre7 0 - chainV centre7 0 (1 / 2) (8064 / 617))
            (chainV centre7 0 (1 / 2) (8064 / 617)) 4 1
      + (κ + 1) * (10 * ymoment2Y (chainP centre7 0 - chainV centre7 0 (1 / 2) (8064 / 617))
              (chainV centre7 0 (1 / 2) (8064 / 617)) 3 2
          + 10 * (κ + 1) * ymoment2Y (chainP centre7 0 - chainV centre7 0 (1 / 2) (8064 / 617))
              (chainV centre7 0 (1 / 2) (8064 / 617)) 2 3
          + 5 * (κ + 1) ^ 2 * ymoment2Y (chainP centre7 0 - chainV centre7 0 (1 / 2) (8064 / 617))
              (chainV centre7 0 (1 / 2) (8064 / 617)) 1 4
          + (κ + 1) ^ 3 * psumY (chainV centre7 0 (1 / 2) (8064 / 617)) 5)) (-1) ≠ 0 := by
    beta_reduce
    rw [show (-1 : ℝ) + 1 = 0 from by norm_num, zero_mul, add_zero]
    exact mul_ne_zero (by norm_num) hM
  refine exists_forall_signChange_of_factorization
    (f := fun κ => chainStep4' centre7 0 (1 / 2) (8064 / 617) κ)
    (G := fun κ =>
        5 * ymoment2Y (chainP centre7 0 - chainV centre7 0 (1 / 2) (8064 / 617))
            (chainV centre7 0 (1 / 2) (8064 / 617)) 4 1
      + (κ + 1) * (10 * ymoment2Y (chainP centre7 0 - chainV centre7 0 (1 / 2) (8064 / 617))
              (chainV centre7 0 (1 / 2) (8064 / 617)) 3 2
          + 10 * (κ + 1) * ymoment2Y (chainP centre7 0 - chainV centre7 0 (1 / 2) (8064 / 617))
              (chainV centre7 0 (1 / 2) (8064 / 617)) 2 3
          + 5 * (κ + 1) ^ 2 * ymoment2Y (chainP centre7 0 - chainV centre7 0 (1 / 2) (8064 / 617))
              (chainV centre7 0 (1 / 2) (8064 / 617)) 1 4
          + (κ + 1) ^ 3 * psumY (chainV centre7 0 (1 / 2) (8064 / 617)) 5))
    ?_ hG0 (Filter.Eventually.of_forall hfac)
  · fun_prop

/-! #### Step 3 at `centre7`: the cleared polynomial and its cofactor

`chainStep3'` is rational in `μ`; `chainStep3Cleared_eq'` writes it as
`chainStep3Cleared / ⟨P, d, d⟩³`. The cleared polynomial is an exact multiple of
`(μ − μ₀)`, and the quotient below is nonzero at `μ₀` — its value is the plan's step-3
derivative `−108084339737784597018125/8236327287823872`. So the cofactor
`H μ / ⟨P, d, d⟩³` is continuous and nonzero at `μ₀`, which is what the uniform sign-change
lemma needs for a rational step. -/

private def centre7Step3Den (μ : ℝ) : ℝ :=
  yBdotY (chainP centre7 0) (chainD centre7 0 μ) (chainD centre7 0 μ)

private def centre7Step3H (μ : ℝ) : ℝ :=
  (1217220193091875858183375 / 3940955764224 : ℝ)
    + (-1383385010673855567975625 / 11822867292672 : ℝ) * μ
    + (105143813144908518953875 / 5911433646336 : ℝ) * μ ^ 2
    + (-71214796672523190840125 / 53202902817024 : ℝ) * μ ^ 3
    + (291079728186049761875 / 5911433646336 : ℝ) * μ ^ 4
    + (-9285863001067296875 / 13300725704256 : ℝ) * μ ^ 5

private theorem centre7_step3_den_ne : centre7Step3Den (8064 / 617) ≠ 0 := by
  have h := centre7_denom2
  rw [show centre7roots.1 = (0 : ℝ) from rfl,
    show centre7roots.2.2.1 = (8064 / 617 : ℝ) from rfl] at h
  exact h

private theorem centre7_step3_H_ne : centre7Step3H (8064 / 617) ≠ 0 := by
  norm_num [centre7Step3H]

private theorem centre7_step3_cleared (μ : ℝ) :
    chainStep3Cleared (chainP centre7 0) (chainQ0 centre7 0 (1 / 2))
        (μ • chainW1 centre7 0 + chainW3 centre7 0)
      = (μ - 8064 / 617) * centre7Step3H μ := by
  norm_num [centre7Step3H, chainStep3Cleared, chainP, chainQ0, chainW1, chainW2, chainW3,
    chainWt, chainProjN, yBdotY, ymoment3Y, yNBY, ymoment2Y, ChainYInputs.a, ChainYInputs.b,
    ChainYInputs.g, ChainYInputs.w1, ChainYInputs.w2, ChainYInputs.w3, centre7, centre7a,
    centre7b, centre7g, centre7w1, centre7w2, centre7w3, Fin.sum_univ_succ, Pi.add_apply,
    Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

private theorem centre7_step3_sign :
    ∃ ε > 0, ∀ δ, 0 < δ → δ < ε →
      chainStep3' centre7 0 (1 / 2) (8064 / 617 - δ) *
        chainStep3' centre7 0 (1 / 2) (8064 / 617 + δ) < 0 := by
  have hdenc : Continuous (fun μ : ℝ => centre7Step3Den μ) := by
    simp only [centre7Step3Den, yBdotY, ymoment3Y, chainD, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    fun_prop
  have hfac : ∀ᶠ μ in nhds (8064 / 617),
      chainStep3' centre7 0 (1 / 2) μ
        = (μ - 8064 / 617) * (centre7Step3H μ / (centre7Step3Den μ) ^ 3) := by
    have hopen : {μ : ℝ | centre7Step3Den μ ≠ 0} ∈ nhds (8064 / 617) :=
      hdenc.continuousAt.preimage_mem_nhds
        (isOpen_compl_singleton.mem_nhds centre7_step3_den_ne)
    filter_upwards [hopen] with μ hμ
    have hCs : chainStep3 (chainP centre7 0) (chainQ0 centre7 0 (1 / 2)) (chainW1 centre7 0)
          (chainW3 centre7 0) μ
        = chainStep3Cleared (chainP centre7 0) (chainQ0 centre7 0 (1 / 2))
            (μ • chainW1 centre7 0 + chainW3 centre7 0) / (centre7Step3Den μ) ^ 3 := by
      rw [eq_div_iff (pow_ne_zero 3 hμ),
        chainStep3Cleared_eq' (P := chainP centre7 0) (q₀ := chainQ0 centre7 0 (1 / 2))
          (w₁ := chainW1 centre7 0) (w₃ := chainW3 centre7 0) hμ]
      simp only [centre7Step3Den, chainD]
      ring
    rw [show chainStep3' centre7 0 (1 / 2) μ
        = chainStep3 (chainP centre7 0) (chainQ0 centre7 0 (1 / 2)) (chainW1 centre7 0)
            (chainW3 centre7 0) μ from rfl, hCs, centre7_step3_cleared μ]
    ring
  refine exists_forall_signChange_of_factorization
    (f := fun μ => chainStep3' centre7 0 (1 / 2) μ)
    (G := fun μ => centre7Step3H μ / (centre7Step3Den μ) ^ 3) ?_ ?_ hfac
  · have hH : ContinuousAt (fun μ : ℝ => centre7Step3H μ) (8064 / 617) := by
      simp only [centre7Step3H]
      fun_prop
    exact hH.div (hdenc.continuousAt.pow 3) (pow_ne_zero 3 centre7_step3_den_ne)
  · exact div_ne_zero centre7_step3_H_ne (pow_ne_zero 3 centre7_step3_den_ne)

/-! ### Strict sign change at every small radius: the `centre7` certificate -/

/-- **Strict sign change at every sufficiently small radius, at `centre7`.** Each of the
four chain steps, evaluated at the rational centre, is a (rational, for step 3) function of
its step variable with a *simple* zero at the certified root; `∃ ε` below which each product
of the two one-sided values is negative is then the data `exists_chain_roots_local` consumes. -/
theorem centre7_chain_signs :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ δ, 0 < δ → δ < ε →
        chainStep1' centre7 (centre7roots.1 - δ) *
          chainStep1' centre7 (centre7roots.1 + δ) < 0) ∧
      (∀ δ, 0 < δ → δ < ε →
        chainStep2' centre7 centre7roots.1 (centre7roots.2.1 - δ) *
          chainStep2' centre7 centre7roots.1 (centre7roots.2.1 + δ) < 0) ∧
      (∀ δ, 0 < δ → δ < ε →
        chainStep3' centre7 centre7roots.1 centre7roots.2.1 (centre7roots.2.2.1 - δ) *
          chainStep3' centre7 centre7roots.1 centre7roots.2.1 (centre7roots.2.2.1 + δ) < 0) ∧
      (∀ δ, 0 < δ → δ < ε →
        chainStep4' centre7 centre7roots.1 centre7roots.2.1 centre7roots.2.2.1
            (centre7roots.2.2.2 - δ) *
          chainStep4' centre7 centre7roots.1 centre7roots.2.1 centre7roots.2.2.1
            (centre7roots.2.2.2 + δ) < 0) := by
  obtain ⟨ε1, hε1, hs1⟩ := centre7_step1_sign
  obtain ⟨ε2, hε2, hs2⟩ := centre7_step2_sign
  obtain ⟨ε3, hε3, hs3⟩ := centre7_step3_sign
  obtain ⟨ε4, hε4, hs4⟩ := centre7_step4_sign
  refine ⟨min (min ε1 ε2) (min ε3 ε4), lt_min (lt_min hε1 hε2) (lt_min hε3 hε4),
    ?_, ?_, ?_, ?_⟩
  · intro δ hδ hδε
    exact hs1 δ hδ (lt_of_lt_of_le hδε (le_trans (min_le_left _ _) (min_le_left _ _)))
  · intro δ hδ hδε
    exact hs2 δ hδ (lt_of_lt_of_le hδε (le_trans (min_le_left _ _) (min_le_right _ _)))
  · intro δ hδ hδε
    exact hs3 δ hδ (lt_of_lt_of_le hδε (le_trans (min_le_right _ _) (min_le_left _ _)))
  · intro δ hδ hδε
    exact hs4 δ hδ (lt_of_lt_of_le hδε (le_trans (min_le_right _ _) (min_le_right _ _)))

/-! ### The four centre-`n = 8` sign changes, uniformly in the radius -/

private theorem centre8_step1_sign :
    ∃ ε > 0, ∀ δ, 0 < δ → δ < ε →
      chainStep1' centre8 (0 - δ) * chainStep1' centre8 (0 + δ) < 0 := by
  have hP3 : psumY centre8a 3 = 0 := by
    norm_num [psumY, psumFinY, centre8a, Fin.sum_univ_succ]
  have hfac : ∀ t : ℝ, chainStep1' centre8 t
      = (t - 0) * (3 * yNBY centre8a centre8b + 3 * t * yConicY centre8a centre8b
          + t ^ 2 * psumY centre8b 3) := by
    intro t
    simp only [chainStep1', chainStep1, centre8, ChainYInputs.a, ChainYInputs.b]
    rw [psumY_cube_eq, hP3]
    ring
  refine exists_forall_signChange_of_factorization (f := chainStep1' centre8)
    (G := fun t => 3 * yNBY centre8a centre8b + 3 * t * yConicY centre8a centre8b
      + t ^ 2 * psumY centre8b 3) ?_ ?_ (Filter.Eventually.of_forall hfac)
  · fun_prop
  · norm_num [yNBY, ymoment2Y, yConicY, psumY, psumFinY, centre8a, centre8b, Fin.sum_univ_succ]

private theorem centre8_step2_sign :
    ∃ ε > 0, ∀ δ, 0 < δ → δ < ε →
      chainStep2' centre8 0 (5 / 3 - δ) * chainStep2' centre8 0 (5 / 3 + δ) < 0 := by
  have hexp : ∀ x : ℝ, chainStep2' centre8 0 x
      = yConicY (chainP centre8 0) (chainProjN (chainP centre8 0) centre8.g (chainW1 centre8 0))
        + 2 * x * yBdotY (chainP centre8 0)
            (chainProjN (chainP centre8 0) centre8.g (chainW1 centre8 0))
            (chainProjN (chainP centre8 0) centre8.g (chainW2 centre8 0))
        + x ^ 2 * yConicY (chainP centre8 0)
            (chainProjN (chainP centre8 0) centre8.g (chainW2 centre8 0)) := by
    intro x
    rw [show chainStep2' centre8 0 x = yConicY (chainP centre8 0)
        (chainProjN (chainP centre8 0) centre8.g (chainW1 centre8 0)
          + x • chainProjN (chainP centre8 0) centre8.g (chainW2 centre8 0)) from rfl,
      yConicY_add_smul_right]
  have hroot : yConicY (chainP centre8 0)
        (chainProjN (chainP centre8 0) centre8.g (chainW1 centre8 0))
      = -yBdotY (chainP centre8 0)
          (chainProjN (chainP centre8 0) centre8.g (chainW1 centre8 0))
          (chainProjN (chainP centre8 0) centre8.g (chainW2 centre8 0)) * (10 / 3)
        - yConicY (chainP centre8 0)
          (chainProjN (chainP centre8 0) centre8.g (chainW2 centre8 0)) * (25 / 9) := by
    have h := centre8_solves.2.1
    rw [show centre8roots.1 = (0 : ℝ) from rfl, show centre8roots.2.1 = (5 / 3 : ℝ) from rfl]
      at h
    rw [hexp (5 / 3)] at h
    ring_nf at h ⊢
    linarith [h]
  have hfac : ∀ x : ℝ, chainStep2' centre8 0 x
      = (x - 5 / 3) * (yConicY (chainP centre8 0)
            (chainProjN (chainP centre8 0) centre8.g (chainW2 centre8 0)) * x
          + 2 * yBdotY (chainP centre8 0)
            (chainProjN (chainP centre8 0) centre8.g (chainW1 centre8 0))
            (chainProjN (chainP centre8 0) centre8.g (chainW2 centre8 0))
          + (5 / 3) * yConicY (chainP centre8 0)
            (chainProjN (chainP centre8 0) centre8.g (chainW2 centre8 0))) := by
    intro x
    rw [hexp x, hroot]
    ring
  refine exists_forall_signChange_of_factorization (f := fun x => chainStep2' centre8 0 x)
    (G := fun x => yConicY (chainP centre8 0)
          (chainProjN (chainP centre8 0) centre8.g (chainW2 centre8 0)) * x
        + 2 * yBdotY (chainP centre8 0)
          (chainProjN (chainP centre8 0) centre8.g (chainW1 centre8 0))
          (chainProjN (chainP centre8 0) centre8.g (chainW2 centre8 0))
        + (5 / 3) * yConicY (chainP centre8 0)
          (chainProjN (chainP centre8 0) centre8.g (chainW2 centre8 0)))
    ?_ ?_ (Filter.Eventually.of_forall hfac)
  · fun_prop
  · norm_num [yConicY, ymoment2Y, yBdotY, ymoment3Y, chainP, chainW1, chainW2, chainWt,
      chainProjN, yNBY, ChainYInputs.a, ChainYInputs.b, ChainYInputs.g, ChainYInputs.w1,
      ChainYInputs.w2, centre8, centre8a, centre8b, centre8g, centre8w1, centre8w2,
      Fin.sum_univ_succ, Pi.add_apply, Pi.sub_apply, smul_eq_mul]

private theorem centre8_step4_sign :
    ∃ ε > 0, ∀ δ, 0 < δ → δ < ε →
      chainStep4' centre8 0 (5 / 3) (-5322 / 2915) (-1 - δ) *
        chainStep4' centre8 0 (5 / 3) (-5322 / 2915) (-1 + δ) < 0 := by
  have hshift : ∀ κ : ℝ, chainP centre8 0 + κ • chainV centre8 0 (5 / 3) (-5322 / 2915)
      = (chainP centre8 0 - chainV centre8 0 (5 / 3) (-5322 / 2915))
        + (κ + 1) • chainV centre8 0 (5 / 3) (-5322 / 2915) := by
    intro κ
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have h00 : psumY (chainP centre8 0 - chainV centre8 0 (5 / 3) (-5322 / 2915)) 5 = 0 := by
    have h := centre8_solves.2.2.2
    rw [show centre8roots.1 = (0 : ℝ) from rfl, show centre8roots.2.1 = (5 / 3 : ℝ) from rfl,
      show centre8roots.2.2.1 = (-5322 / 2915 : ℝ) from rfl,
      show centre8roots.2.2.2 = (-1 : ℝ) from rfl] at h
    rw [show chainStep4' centre8 0 (5 / 3) (-5322 / 2915) (-1)
        = psumY (chainP centre8 0 + (-1 : ℝ) • chainV centre8 0 (5 / 3) (-5322 / 2915)) 5
        from rfl] at h
    rw [show chainP centre8 0 + (-1 : ℝ) • chainV centre8 0 (5 / 3) (-5322 / 2915)
        = chainP centre8 0 - chainV centre8 0 (5 / 3) (-5322 / 2915) from by
          ext i
          simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          ring] at h
    exact h
  have hM : ymoment2Y (chainP centre8 0 - chainV centre8 0 (5 / 3) (-5322 / 2915))
      (chainV centre8 0 (5 / 3) (-5322 / 2915)) 4 1 ≠ 0 := by
    norm_num [ymoment2Y, chainV, chainConicPt, chainQ0, chainD, chainW1, chainW2, chainW3,
      chainWt, chainProjN, yBdotY, ymoment3Y, yNBY, chainP, ChainYInputs.a, ChainYInputs.b,
      ChainYInputs.g, ChainYInputs.w1, ChainYInputs.w2, ChainYInputs.w3, centre8, centre8a,
      centre8b, centre8g, centre8w1, centre8w2, centre8w3, Fin.sum_univ_succ, Pi.add_apply,
      Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  have hfac : ∀ κ : ℝ, chainStep4' centre8 0 (5 / 3) (-5322 / 2915) κ = (κ - (-1)) *
      (5 * ymoment2Y (chainP centre8 0 - chainV centre8 0 (5 / 3) (-5322 / 2915))
            (chainV centre8 0 (5 / 3) (-5322 / 2915)) 4 1
        + (κ + 1) * (10 * ymoment2Y (chainP centre8 0 - chainV centre8 0 (5 / 3) (-5322 / 2915))
              (chainV centre8 0 (5 / 3) (-5322 / 2915)) 3 2
          + 10 * (κ + 1) * ymoment2Y (chainP centre8 0 - chainV centre8 0 (5 / 3) (-5322 / 2915))
              (chainV centre8 0 (5 / 3) (-5322 / 2915)) 2 3
          + 5 * (κ + 1) ^ 2 * ymoment2Y (chainP centre8 0 - chainV centre8 0 (5 / 3) (-5322 / 2915))
              (chainV centre8 0 (5 / 3) (-5322 / 2915)) 1 4
          + (κ + 1) ^ 3 * psumY (chainV centre8 0 (5 / 3) (-5322 / 2915)) 5)) := by
    intro κ
    rw [show chainStep4' centre8 0 (5 / 3) (-5322 / 2915) κ
        = psumY (chainP centre8 0 + κ • chainV centre8 0 (5 / 3) (-5322 / 2915)) 5
        from rfl, hshift κ, psumY_add_smul_five, h00]
    ring
  have hG0 : (fun κ : ℝ =>
        5 * ymoment2Y (chainP centre8 0 - chainV centre8 0 (5 / 3) (-5322 / 2915))
            (chainV centre8 0 (5 / 3) (-5322 / 2915)) 4 1
      + (κ + 1) * (10 * ymoment2Y (chainP centre8 0 - chainV centre8 0 (5 / 3) (-5322 / 2915))
              (chainV centre8 0 (5 / 3) (-5322 / 2915)) 3 2
          + 10 * (κ + 1) * ymoment2Y (chainP centre8 0 - chainV centre8 0 (5 / 3) (-5322 / 2915))
              (chainV centre8 0 (5 / 3) (-5322 / 2915)) 2 3
          + 5 * (κ + 1) ^ 2 * ymoment2Y (chainP centre8 0 - chainV centre8 0 (5 / 3) (-5322 / 2915))
              (chainV centre8 0 (5 / 3) (-5322 / 2915)) 1 4
          + (κ + 1) ^ 3 * psumY (chainV centre8 0 (5 / 3) (-5322 / 2915)) 5)) (-1) ≠ 0 := by
    beta_reduce
    rw [show (-1 : ℝ) + 1 = 0 from by norm_num, zero_mul, add_zero]
    exact mul_ne_zero (by norm_num) hM
  refine exists_forall_signChange_of_factorization
    (f := fun κ => chainStep4' centre8 0 (5 / 3) (-5322 / 2915) κ)
    (G := fun κ =>
        5 * ymoment2Y (chainP centre8 0 - chainV centre8 0 (5 / 3) (-5322 / 2915))
            (chainV centre8 0 (5 / 3) (-5322 / 2915)) 4 1
      + (κ + 1) * (10 * ymoment2Y (chainP centre8 0 - chainV centre8 0 (5 / 3) (-5322 / 2915))
              (chainV centre8 0 (5 / 3) (-5322 / 2915)) 3 2
          + 10 * (κ + 1) * ymoment2Y (chainP centre8 0 - chainV centre8 0 (5 / 3) (-5322 / 2915))
              (chainV centre8 0 (5 / 3) (-5322 / 2915)) 2 3
          + 5 * (κ + 1) ^ 2 * ymoment2Y (chainP centre8 0 - chainV centre8 0 (5 / 3) (-5322 / 2915))
              (chainV centre8 0 (5 / 3) (-5322 / 2915)) 1 4
          + (κ + 1) ^ 3 * psumY (chainV centre8 0 (5 / 3) (-5322 / 2915)) 5))
    ?_ hG0 (Filter.Eventually.of_forall hfac)
  · fun_prop

/-! #### Step 3 at `centre8`: the cleared polynomial and its cofactor -/

private def centre8Step3Den (μ : ℝ) : ℝ :=
  yBdotY (chainP centre8 0) (chainD centre8 0 μ) (chainD centre8 0 μ)

private def centre8Step3H (μ : ℝ) : ℝ :=
  (113527613262185503744 / 2552563125 : ℝ)
    + (52581523130105335168 / 306307575 : ℝ) * μ
    + (43027571376655747904 / 183784545 : ℝ) * μ ^ 2
    + (2160068939562988256 / 15752961 : ℝ) * μ ^ 3
    + (11446541205829994000 / 330812181 : ℝ) * μ ^ 4
    + (3032083343864862320 / 992436543 : ℝ) * μ ^ 5

private theorem centre8_step3_den_ne : centre8Step3Den (-5322 / 2915) ≠ 0 := by
  have h := centre8_denom2
  rw [show centre8roots.1 = (0 : ℝ) from rfl,
    show centre8roots.2.2.1 = (-5322 / 2915 : ℝ) from rfl] at h
  exact h

private theorem centre8_step3_H_ne : centre8Step3H (-5322 / 2915) ≠ 0 := by
  norm_num [centre8Step3H]

private theorem centre8_step3_cleared (μ : ℝ) :
    chainStep3Cleared (chainP centre8 0) (chainQ0 centre8 0 (5 / 3))
        (μ • chainW1 centre8 0 + chainW3 centre8 0)
      = (μ - (-5322 / 2915)) * centre8Step3H μ := by
  norm_num [centre8Step3H, chainStep3Cleared, chainP, chainQ0, chainW1, chainW2, chainW3,
    chainWt, chainProjN, yBdotY, ymoment3Y, yNBY, ymoment2Y, ChainYInputs.a, ChainYInputs.b,
    ChainYInputs.g, ChainYInputs.w1, ChainYInputs.w2, ChainYInputs.w3, centre8, centre8a,
    centre8b, centre8g, centre8w1, centre8w2, centre8w3, Fin.sum_univ_succ, Pi.add_apply,
    Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

private theorem centre8_step3_sign :
    ∃ ε > 0, ∀ δ, 0 < δ → δ < ε →
      chainStep3' centre8 0 (5 / 3) (-5322 / 2915 - δ) *
        chainStep3' centre8 0 (5 / 3) (-5322 / 2915 + δ) < 0 := by
  have hdenc : Continuous (fun μ : ℝ => centre8Step3Den μ) := by
    simp only [centre8Step3Den, yBdotY, ymoment3Y, chainD, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    fun_prop
  have hfac : ∀ᶠ μ in nhds (-5322 / 2915),
      chainStep3' centre8 0 (5 / 3) μ
        = (μ - (-5322 / 2915)) * (centre8Step3H μ / (centre8Step3Den μ) ^ 3) := by
    have hopen : {μ : ℝ | centre8Step3Den μ ≠ 0} ∈ nhds (-5322 / 2915) :=
      hdenc.continuousAt.preimage_mem_nhds
        (isOpen_compl_singleton.mem_nhds centre8_step3_den_ne)
    filter_upwards [hopen] with μ hμ
    have hCs : chainStep3 (chainP centre8 0) (chainQ0 centre8 0 (5 / 3)) (chainW1 centre8 0)
          (chainW3 centre8 0) μ
        = chainStep3Cleared (chainP centre8 0) (chainQ0 centre8 0 (5 / 3))
            (μ • chainW1 centre8 0 + chainW3 centre8 0) / (centre8Step3Den μ) ^ 3 := by
      rw [eq_div_iff (pow_ne_zero 3 hμ),
        chainStep3Cleared_eq' (P := chainP centre8 0) (q₀ := chainQ0 centre8 0 (5 / 3))
          (w₁ := chainW1 centre8 0) (w₃ := chainW3 centre8 0) hμ]
      simp only [centre8Step3Den, chainD]
      ring
    rw [show chainStep3' centre8 0 (5 / 3) μ
        = chainStep3 (chainP centre8 0) (chainQ0 centre8 0 (5 / 3)) (chainW1 centre8 0)
            (chainW3 centre8 0) μ from rfl, hCs, centre8_step3_cleared μ]
    ring
  refine exists_forall_signChange_of_factorization
    (f := fun μ => chainStep3' centre8 0 (5 / 3) μ)
    (G := fun μ => centre8Step3H μ / (centre8Step3Den μ) ^ 3) ?_ ?_ hfac
  · have hH : ContinuousAt (fun μ : ℝ => centre8Step3H μ) (-5322 / 2915) := by
      simp only [centre8Step3H]
      fun_prop
    exact hH.div (hdenc.continuousAt.pow 3) (pow_ne_zero 3 centre8_step3_den_ne)
  · exact div_ne_zero centre8_step3_H_ne (pow_ne_zero 3 centre8_step3_den_ne)

/-! ### Strict sign change at every small radius: the `centre8` certificate -/

/-- **Strict sign change at every sufficiently small radius, at `centre8`.** -/
theorem centre8_chain_signs :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ δ, 0 < δ → δ < ε →
        chainStep1' centre8 (centre8roots.1 - δ) *
          chainStep1' centre8 (centre8roots.1 + δ) < 0) ∧
      (∀ δ, 0 < δ → δ < ε →
        chainStep2' centre8 centre8roots.1 (centre8roots.2.1 - δ) *
          chainStep2' centre8 centre8roots.1 (centre8roots.2.1 + δ) < 0) ∧
      (∀ δ, 0 < δ → δ < ε →
        chainStep3' centre8 centre8roots.1 centre8roots.2.1 (centre8roots.2.2.1 - δ) *
          chainStep3' centre8 centre8roots.1 centre8roots.2.1 (centre8roots.2.2.1 + δ) < 0) ∧
      (∀ δ, 0 < δ → δ < ε →
        chainStep4' centre8 centre8roots.1 centre8roots.2.1 centre8roots.2.2.1
            (centre8roots.2.2.2 - δ) *
          chainStep4' centre8 centre8roots.1 centre8roots.2.1 centre8roots.2.2.1
            (centre8roots.2.2.2 + δ) < 0) := by
  obtain ⟨ε1, hε1, hs1⟩ := centre8_step1_sign
  obtain ⟨ε2, hε2, hs2⟩ := centre8_step2_sign
  obtain ⟨ε3, hε3, hs3⟩ := centre8_step3_sign
  obtain ⟨ε4, hε4, hs4⟩ := centre8_step4_sign
  refine ⟨min (min ε1 ε2) (min ε3 ε4), lt_min (lt_min hε1 hε2) (lt_min hε3 hε4),
    ?_, ?_, ?_, ?_⟩
  · intro δ hδ hδε
    exact hs1 δ hδ (lt_of_lt_of_le hδε (le_trans (min_le_left _ _) (min_le_left _ _)))
  · intro δ hδ hδε
    exact hs2 δ hδ (lt_of_lt_of_le hδε (le_trans (min_le_left _ _) (min_le_right _ _)))
  · intro δ hδ hδε
    exact hs3 δ hδ (lt_of_lt_of_le hδε (le_trans (min_le_right _ _) (min_le_left _ _)))
  · intro δ hδ hδε
    exact hs4 δ hδ (lt_of_lt_of_le hδε (le_trans (min_le_right _ _) (min_le_right _ _)))



/-! ### The open sets of good inputs -/







/-! #### What the chain's data gives about the output's power sums

`ChainGood` is the four step equations, the two non-degeneracy conditions and injectivity of
the output. Two of the three power-sum conclusions of `exists_open_good7` are consequences
of that data, and are recorded below as proved lemmas:

* the **fifth** power sum *is* step 4, definitionally (`chainStep4'_psumY_eq`);
* the **third** power sum follows from steps 1 and 3, the conic condition of step 2 and the
  two denominators (`chainY_psumY_cube_eq`) — the content of `psumY_13_line` with its two
  `psumY … 1` hypotheses dropped.

The **first** power sum is a fifth equation and is *not* implied: `chainY_psumY_one_eq'`
identifies it as `S₁(P) + κ S₁(v)`, and `chainY_psumY_one_eq` gives the criterion under
which it does vanish. -/

/-- Step 4 *is* the vanishing of the fifth power sum of the output: `chainStep4'` unfolds to
`psumY (chainP I lam + kappa • chainV I lam x mu) 5`, which is
`psumY (chainY I lam x mu kappa) 5`. -/
theorem chainStep4'_psumY_eq (I : ChainYInputs n) (lam x mu kappa : ℝ) :
    chainStep4' I lam x mu kappa = psumY (chainY I lam x mu kappa) 5 := rfl

/-- The first power sum of the output, as a linear functional of the two vectors entering
the last step. This identity is what shows the `psumY … 1 = 0` conclusion of
`exists_open_good7` is an *extra* equation, not a consequence of `ChainGood`. -/
theorem chainY_psumY_one_eq' (I : ChainYInputs n) (lam x mu kappa : ℝ) :
    psumY (chainY I lam x mu kappa) 1
      = psumY (chainP I lam) 1 + kappa * psumY (chainV I lam x mu) 1 := by
  have h := psumY_one_eq (chainP I lam) (chainV I lam x mu) kappa
  simpa only [chainY] using h

/-- `psumY (P − s • v) 1 = S₁ P − s · S₁ v`, the `sub` counterpart of `psumY_one_eq`. -/
theorem psumY_sub_smul_eq (P v : Fin n → ℝ) (s : ℝ) :
    psumY (P - s • v) 1 = psumY P 1 - s * psumY v 1 := by
  have h := psumY_one_eq P v (-s)
  have key : P - s • v = P + (-s) • v := by
    rw [sub_eq_add_neg, neg_smul]
  rw [key, psumY_one_eq]
  ring

/-- **`S₁` is preserved by the whole chain** when it vanishes on all six inputs.

This is the missing hypothesis of `exists_open_good7`; see the `WARNING` there. It holds at
both centres, and it is what turns `S₁ y = 0` into an identity of the chain rather than a
fifth equation in the four unknowns `lam`, `x`, `mu`, `kappa`. -/
theorem chainY_psumY_one_eq {I : ChainYInputs n} {lam x mu kappa : ℝ}
    (ha : psumY I.a 1 = 0) (hb : psumY I.b 1 = 0) (hg : psumY I.g 1 = 0)
    (hw1 : psumY I.w1 1 = 0) (hw2 : psumY I.w2 1 = 0) (hw3 : psumY I.w3 1 = 0) :
    psumY (chainY I lam x mu kappa) 1 = 0 := by
  have hP : psumY (chainP I lam) 1 = 0 := by
    have key : chainP I lam = I.a + lam • I.b := rfl
    rw [key, psumY_one_eq, ha, hb]
    ring
  -- every `N_P`-projection of an input direction still has vanishing first power sum
  have hproj : ∀ w : Fin n → ℝ, psumY w 1 = 0 →
      psumY (chainProjN (chainP I lam) I.g w) 1 = 0 := by
    intro w hw
    have key : chainProjN (chainP I lam) I.g w
        = w - (yNBY (chainP I lam) w / yNBY (chainP I lam) I.g) • I.g := rfl
    rw [key, psumY_sub_smul_eq, hw, hg]
    ring
  have hW1 : psumY (chainW1 I lam) 1 = 0 := by
    have key : chainW1 I lam = chainProjN (chainP I lam) I.g I.w1 := rfl
    rw [key]
    exact hproj I.w1 hw1
  have hW2 : psumY (chainW2 I lam) 1 = 0 := by
    have key : chainW2 I lam = chainProjN (chainP I lam) I.g I.w2 := rfl
    rw [key]
    exact hproj I.w2 hw2
  have hW3 : psumY (chainW3 I lam) 1 = 0 := by
    have key : chainW3 I lam = chainProjN (chainP I lam) I.g I.w3 := rfl
    rw [key]
    exact hproj I.w3 hw3
  have hq0 : psumY (chainQ0 I lam x) 1 = 0 := by
    have key : chainQ0 I lam x = chainW1 I lam + x • chainW2 I lam := rfl
    rw [key, psumY_one_eq, hW1, hW2]
    ring
  have hd : psumY (chainD I lam mu) 1 = 0 := by
    have key : chainD I lam mu = mu • chainW1 I lam + chainW3 I lam := rfl
    rw [key, add_comm, psumY_one_eq, hW1, hW3]
    ring
  have hv : psumY (chainV I lam x mu) 1 = 0 := by
    have key : chainV I lam x mu = chainQ0 I lam x
        - (2 * yBdotY (chainP I lam) (chainQ0 I lam x) (chainD I lam mu)
          / yBdotY (chainP I lam) (chainD I lam mu) (chainD I lam mu)) • chainD I lam mu := rfl
    rw [key, psumY_sub_smul_eq, hq0, hd]
    ring
  have h := chainY_psumY_one_eq' I lam x mu kappa
  rw [h, hP, hv]
  ring

/-- `chainProjN` is idempotent on the hyperplane `N_P`: a point of `N_P` is its own
projection. This is what reconciles `chainStep2'`, which projects `chainW1`/`chainW2` a
*second* time, with `chainQ0`, which uses the projected directions directly. -/
theorem chainProjN_of_mem_N {P g w : Fin n → ℝ} (hw : yNBY P w = 0) :
    chainProjN P g w = w := by
  have key : chainProjN P g w = w - (yNBY P w / yNBY P g) • g := rfl
  rw [key]
  ext i
  simp [hw]

/-- **The third power sum of the output is a consequence of the chain's data.**

`h1` is step 1, `h3` is step 3, `h2` read as "the conic point is on the conic", and
`hNv`/`hQv` are the two facts about the direction `v` that `psumY_cube_eq` needs. So this is
`psumY_13_line` with its two `psumY … 1` hypotheses dropped. -/
theorem chainY_psumY_cube_eq {I : ChainYInputs n} {lam x mu kappa : ℝ}
    (h1 : chainStep1' I lam = 0) (h2 : chainStep2' I lam x = 0)
    (h3 : chainStep3' I lam x mu = 0) (hden1 : yNBY (chainP I lam) I.g ≠ 0)
    (hden2 : yBdotY (chainP I lam) (chainD I lam mu) (chainD I lam mu) ≠ 0) :
    psumY (chainY I lam x mu kappa) 3 = 0 := by
  have hP3 : psumY (chainP I lam) 3 = 0 := h1
  have hN1 : yNBY (chainP I lam) (chainW1 I lam) = 0 := chainProjN_mem_N hden1
  have hN2 : yNBY (chainP I lam) (chainW2 I lam) = 0 := chainProjN_mem_N hden1
  have hN3 : yNBY (chainP I lam) (chainW3 I lam) = 0 := chainProjN_mem_N hden1
  have hNq0 : yNBY (chainP I lam) (chainQ0 I lam x) = 0 := by
    have h := yNBY_add_right (chainP I lam) (chainW1 I lam) (x • chainW2 I lam)
    have h' := yNBY_smul_right (chainP I lam) (chainW2 I lam) x
    have key : chainQ0 I lam x = chainW1 I lam + x • chainW2 I lam := rfl
    rw [key, h, hN1, h', hN2]
    ring
  have hNd : yNBY (chainP I lam) (chainD I lam mu) = 0 := by
    have h := yNBY_add_right (chainP I lam) (mu • chainW1 I lam) (chainW3 I lam)
    have h' := yNBY_smul_right (chainP I lam) (chainW1 I lam) mu
    have key : chainD I lam mu = mu • chainW1 I lam + chainW3 I lam := rfl
    rw [key, h, h', hN1, hN3]
    ring
  have hQ0 : yConicY (chainP I lam) (chainQ0 I lam x) = 0 := by
    have key0 : chainQ0 I lam x = chainW1 I lam + x • chainW2 I lam := rfl
    have key1 : chainProjN (chainP I lam) I.g (chainW1 I lam) = chainW1 I lam :=
      chainProjN_of_mem_N hN1
    have key2 : chainProjN (chainP I lam) I.g (chainW2 I lam) = chainW2 I lam :=
      chainProjN_of_mem_N hN2
    have key3 : chainStep2' I lam x = yConicY (chainP I lam)
        (chainProjN (chainP I lam) I.g (chainW1 I lam)
          + x • chainProjN (chainP I lam) I.g (chainW2 I lam)) := rfl
    rw [key3, key1, key2] at h2
    rw [key0]
    exact h2
  have hNv : yNBY (chainP I lam) (chainV I lam x mu) = 0 := by
    have key : chainV I lam x mu = chainQ0 I lam x
        - (2 * yBdotY (chainP I lam) (chainQ0 I lam x) (chainD I lam mu)
          / yBdotY (chainP I lam) (chainD I lam mu) (chainD I lam mu)) • chainD I lam mu := rfl
    have h := yNBY_sub_right (chainP I lam) (chainQ0 I lam x)
      ((2 * yBdotY (chainP I lam) (chainQ0 I lam x) (chainD I lam mu)
        / yBdotY (chainP I lam) (chainD I lam mu) (chainD I lam mu)) • chainD I lam mu)
    have h' := yNBY_smul_right (chainP I lam) (chainD I lam mu)
      (2 * yBdotY (chainP I lam) (chainQ0 I lam x) (chainD I lam mu)
        / yBdotY (chainP I lam) (chainD I lam mu) (chainD I lam mu))
    rw [key, h, hNq0, h', hNd]
    ring
  have hQv : yConicY (chainP I lam) (chainV I lam x mu) = 0 := by
    have key : chainV I lam x mu = chainConicPt (chainP I lam) (chainQ0 I lam x)
        (chainD I lam mu) := rfl
    rw [key]
    exact chainConicPt_on_conic hden2 hQ0
  have hv3 : psumY (chainV I lam x mu) 3 = 0 := by
    have key : chainStep3' I lam x mu = psumY (chainV I lam x mu) 3 := rfl
    rw [key] at h3
    exact h3
  have hlin : psumY (chainP I lam + kappa • chainV I lam x mu) 3 = 0 := by
    rw [psumY_cube_eq, hP3, hNv, hQv, hv3]
    ring
  simpa only [chainY] using hlin

/-! #### The `S₁` input conditions

`S₁(y) = ∑ᵢ yᵢ` is a *fifth* equation in the four step unknowns, and
`chainY_psumY_one_eq` discharges it from six conditions on the six input directions. Both
centres satisfy all six **exactly** (`centre7_s1`, `centre8_s1`), so PLAN §2.4's standing
assumption "its inputs are six vectors `a, b, g, w₁, w₂, w₃ ∈ V`" is available for them.

The conditions are **closed**, not open, in the input variables: they are therefore imposed
on the lifted P-constructible input by `exists_PC_inputs_s1`, not on an open set. -/

/-- All six input directions of `centre7` have vanishing first power sum. -/
theorem centre7_s1 :
    psumY centre7a 1 = 0 ∧ psumY centre7b 1 = 0 ∧ psumY centre7g 1 = 0 ∧
      psumY centre7w1 1 = 0 ∧ psumY centre7w2 1 = 0 ∧ psumY centre7w3 1 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [psumY, psumFinY, centre7a, centre7b, centre7g, centre7w1, centre7w2, centre7w3,
      Fin.sum_univ_succ]

/-- All six input directions of `centre8` have vanishing first power sum. -/
theorem centre8_s1 :
    psumY centre8a 1 = 0 ∧ psumY centre8b 1 = 0 ∧ psumY centre8g 1 = 0 ∧
      psumY centre8w1 1 = 0 ∧ psumY centre8w2 1 = 0 ∧ psumY centre8w3 1 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [psumY, psumFinY, centre8a, centre8b, centre8g, centre8w1, centre8w2, centre8w3,
      Fin.sum_univ_succ]

/-! #### The `hpole1` condition at the two rational centres

`hpole1` holds at every radius: the step-2 denominator is a quadratic in `lam` with negative
discriminant and positive leading coefficient, hence strictly positive for every `lam ∈ ℝ`,
and in particular nonzero on the closed box of any radius whatsoever. This promotes
`centre7_denom1`/`centre8_denom1` from "at the centre" to "everywhere". -/

/-- The Vandermonde product `∏_{i < j} (vᵢ - vⱼ)²`, which is nonzero exactly when `v` is
injective and is continuous in `v`. -/
private def vandermonde {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  Finset.prod (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2))
    (fun p => (v p.1 - v p.2) ^ 2)

private lemma vandermonde_ne_zero_iff {n : ℕ} {v : Fin n → ℝ} :
    vandermonde v ≠ 0 ↔ Function.Injective v := by
  constructor
  · intro h i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hmem : (i, j) ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2) := by
        simp [hlt]
      have hz : (v i - v j) ^ 2 = 0 := by rw [hij, sub_self, zero_pow (by norm_num)]
      exact h (Finset.prod_eq_zero hmem hz)
    · have hmem : (j, i) ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2) := by
        simp [hlt]
      have hz : (v j - v i) ^ 2 = 0 := by rw [hij, sub_self, zero_pow (by norm_num)]
      exact h (Finset.prod_eq_zero hmem hz)
  · intro h
    rw [vandermonde, Finset.prod_ne_zero_iff]
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact pow_ne_zero 2 (sub_ne_zero.mpr fun heq => absurd (h heq) (ne_of_lt hp))

private lemma continuous_vandermonde {n : ℕ} :
    Continuous (vandermonde : (Fin n → ℝ) → ℝ) := by
  unfold vandermonde
  refine continuous_finsetProd _ fun p _ => ?_
  exact ((continuous_apply p.1).sub (continuous_apply p.2)).pow 2

/-- **The generic corrected openness lemma.** At a centre where the four step functions have
the sign changes `hs`, the two denominators are nonzero (`hden1`, `hden2`) and the chain
output is injective (`hinj`), an open neighbourhood of the centre consists of good
configurations, with each step function nonzero somewhere. The proof pins the roots to a
small box using `exists_chain_roots_local`, then evaluates the whole configuration map on a
ball around the centre, where continuity gives both injectivity (via `vandermonde`) and the
four nonvanishing statements. -/
private theorem exists_open_good_of_centre
    {n : ℕ} (I₀ : ChainYInputs n) (c₁ c₂ c₃ c₄ : ℝ)
    (hs : ∃ ε : ℝ, 0 < ε ∧
      (∀ δ, 0 < δ → δ < ε →
        chainStep1' I₀ (c₁ - δ) * chainStep1' I₀ (c₁ + δ) < 0) ∧
      (∀ δ, 0 < δ → δ < ε →
        chainStep2' I₀ c₁ (c₂ - δ) * chainStep2' I₀ c₁ (c₂ + δ) < 0) ∧
      (∀ δ, 0 < δ → δ < ε →
        chainStep3' I₀ c₁ c₂ (c₃ - δ) * chainStep3' I₀ c₁ c₂ (c₃ + δ) < 0) ∧
      (∀ δ, 0 < δ → δ < ε →
        chainStep4' I₀ c₁ c₂ c₃ (c₄ - δ) * chainStep4' I₀ c₁ c₂ c₃ (c₄ + δ) < 0))
    (hden1 : yNBY (chainP I₀ c₁) I₀.g ≠ 0)
    (hden2 : yBdotY (chainP I₀ c₁) (chainD I₀ c₁ c₃) (chainD I₀ c₁ c₃) ≠ 0)
    (hinj : Function.Injective (chainY I₀ c₁ c₂ c₃ c₄)) :
    ∃ U : Set (ChainYInputs n), IsOpen U ∧ I₀ ∈ U ∧
      ∀ I ∈ U, ∃ lam x mu kappa : ℝ, ChainGood I lam x mu kappa ∧
        (∃ t : ℝ, chainStep1' I t ≠ 0) ∧
        (∃ t : ℝ, chainStep2' I lam t ≠ 0) ∧
        (∃ t : ℝ, chainStep3Cleared (chainP I lam) (chainQ0 I lam x)
            (t • chainW1 I lam + chainW3 I lam) ≠ 0) ∧
        (∃ t : ℝ, chainStep4' I lam x mu t ≠ 0) := by
  obtain ⟨ε₀, hε₀, hs1, hs2, hs3, hs4⟩ := hs
  -- a radius on which the step-3 denominator is nonzero near `(c₁, c₃)`
  have hden2cont : ContinuousAt (fun y : ℝ × ℝ =>
      yBdotY (chainP I₀ y.1) (chainD I₀ y.1 y.2) (chainD I₀ y.1 y.2)) (c₁, c₃) := by
    simp only [yBdotY, ymoment3Y, chainD, chainP, ChainYInputs.g, ChainYInputs.a,
      ChainYInputs.b, ChainYInputs.w1, ChainYInputs.w3, chainW1, chainW3, chainWt,
      chainProjN, yNBY, ymoment2Y, Pi.add_apply, Pi.smul_apply]
    fun_prop (disch := assumption)
  obtain ⟨ρ₂, hρ₂pos, hρ₂⟩ := Metric.mem_nhds_iff.mp
    (hden2cont.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hden2))
  -- the fixed one-sided witness offset
  set δ : ℝ := min ε₀ ρ₂ / 2 with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]; exact div_pos (lt_min hε₀ hρ₂pos) (by norm_num)
  have hδε : δ < ε₀ := by
    rw [hδdef]; have h := min_le_left ε₀ ρ₂; linarith
  have hδρ : δ < ρ₂ := by
    rw [hδdef]; have h := min_le_right ε₀ ρ₂; linarith
  let P₀ : ChainYInputs n × (ℝ × ℝ × ℝ × ℝ) := (I₀, (c₁, (c₂, (c₃, c₄))))
  -- continuity of the five functions at the centre
  have hcont1 : ContinuousAt (fun p : ChainYInputs n × (ℝ × ℝ × ℝ × ℝ) =>
      chainStep1' p.1 (c₁ - δ)) P₀ := by
    simp only [chainStep1', chainStep1, psumY, psumFinY, ChainYInputs.a, ChainYInputs.b,
      Pi.add_apply, Pi.smul_apply]
    fun_prop
  have hcont2 : ContinuousAt (fun p : ChainYInputs n × (ℝ × ℝ × ℝ × ℝ) =>
      chainStep2' p.1 p.2.1 (c₂ - δ)) P₀ := by
    simp only [chainStep2', chainStep2, chainProjN, chainP, chainW1, chainW2, chainWt,
      ChainYInputs.g, ChainYInputs.a, ChainYInputs.b, ChainYInputs.w1, ChainYInputs.w2,
      yConicY, ymoment2Y, yNBY, Pi.add_apply, Pi.smul_apply]
    fun_prop (disch := assumption)
  have hcont3 : ContinuousAt (fun p : ChainYInputs n × (ℝ × ℝ × ℝ × ℝ) =>
      chainStep3Cleared (chainP p.1 p.2.1) (chainQ0 p.1 p.2.1 p.2.2.1)
        ((c₃ - δ) • chainW1 p.1 p.2.1 + chainW3 p.1 p.2.1)) P₀ := by
    simp only [chainStep3Cleared, chainQ0, chainW1, chainW2, chainW3, chainWt, chainProjN,
      chainP, ChainYInputs.g, ChainYInputs.a, ChainYInputs.b, ChainYInputs.w1,
      ChainYInputs.w2, ChainYInputs.w3, yNBY, ymoment2Y, yBdotY, ymoment3Y, Pi.add_apply,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    fun_prop (disch := assumption)
  have hcont4 : ContinuousAt (fun p : ChainYInputs n × (ℝ × ℝ × ℝ × ℝ) =>
      chainStep4' p.1 p.2.1 p.2.2.1 p.2.2.2.1 (c₄ - δ)) P₀ := by
    simp only [chainStep4', chainStep4, chainV, chainConicPt, chainD, chainQ0, chainW1,
      chainW2, chainW3, chainWt, chainProjN, chainP, ChainYInputs.g, ChainYInputs.a,
      ChainYInputs.b, ChainYInputs.w1, ChainYInputs.w2, ChainYInputs.w3, psumY, psumFinY,
      ymoment2Y, yBdotY, ymoment3Y, yNBY, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    fun_prop (disch := assumption)
  have hcontY : ContinuousAt (fun p : ChainYInputs n × (ℝ × ℝ × ℝ × ℝ) =>
      chainY p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) P₀ := by
    simp only [chainY, chainP, chainV, chainConicPt, chainD, chainQ0, chainW1, chainW2,
      chainW3, chainWt, chainProjN, ChainYInputs.g, ChainYInputs.a, ChainYInputs.b,
      ChainYInputs.w1, ChainYInputs.w2, ChainYInputs.w3, ymoment2Y, yBdotY, ymoment3Y,
      yNBY, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    fun_prop (disch := assumption)
  -- the values at the centre
  have h1₀ : chainStep1' P₀.1 (c₁ - δ) ≠ 0 :=
    left_ne_zero_of_mul (ne_of_lt (hs1 δ hδpos hδε))
  have h2₀ : chainStep2' P₀.1 P₀.2.1 (c₂ - δ) ≠ 0 :=
    left_ne_zero_of_mul (ne_of_lt (hs2 δ hδpos hδε))
  have h4₀ : chainStep4' P₀.1 P₀.2.1 P₀.2.2.1 P₀.2.2.2.1 (c₄ - δ) ≠ 0 :=
    left_ne_zero_of_mul (ne_of_lt (hs4 δ hδpos hδε))
  have h3raw₀ : chainStep3' P₀.1 P₀.2.1 P₀.2.2.1 (c₃ - δ) ≠ 0 :=
    left_ne_zero_of_mul (ne_of_lt (hs3 δ hδpos hδε))
  have hden2δ : yBdotY (chainP I₀ c₁) (chainD I₀ c₁ (c₃ - δ))
      (chainD I₀ c₁ (c₃ - δ)) ≠ 0 := by
    have hmem : (c₁, c₃ - δ) ∈ Metric.ball (c₁, c₃) ρ₂ := by
      rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      have h1 : |c₁ - c₁| = 0 := by rw [sub_self, abs_zero]
      have h2 : |(c₃ - δ) - c₃| = δ := by
        rw [show c₃ - δ - c₃ = -δ by ring, abs_neg, abs_of_pos hδpos]
      rw [h1, h2]
      exact max_lt hρ₂pos hδρ
    have hmem' := hρ₂ hmem
    simpa only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff] using hmem'
  have h3₀ : chainStep3Cleared (chainP I₀ c₁) (chainQ0 I₀ c₁ c₂)
      ((c₃ - δ) • chainW1 I₀ c₁ + chainW3 I₀ c₁) ≠ 0 := by
    have hden' : yBdotY (chainP I₀ c₁)
        ((c₃ - δ) • chainW1 I₀ c₁ + chainW3 I₀ c₁)
        ((c₃ - δ) • chainW1 I₀ c₁ + chainW3 I₀ c₁) ≠ 0 := by
      simpa only [chainD] using hden2δ
    rw [chainStep3Cleared_eq' hden']
    exact mul_ne_zero (pow_ne_zero 3 hden')
      (by simpa only [chainStep3'] using h3raw₀)
  have hV0 : vandermonde (chainY P₀.1 P₀.2.1 P₀.2.2.1 P₀.2.2.2.1 P₀.2.2.2.2) ≠ 0 :=
    vandermonde_ne_zero_iff.mpr hinj
  -- the corresponding neighbourhoods of the centre
  have hV1 : {p : ChainYInputs n × (ℝ × ℝ × ℝ × ℝ) |
      chainStep1' p.1 (c₁ - δ) ≠ 0} ∈ nhds P₀ :=
    hcont1.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds h1₀)
  have hV2 : {p : ChainYInputs n × (ℝ × ℝ × ℝ × ℝ) |
      chainStep2' p.1 p.2.1 (c₂ - δ) ≠ 0} ∈ nhds P₀ :=
    hcont2.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds h2₀)
  have hV3 : {p : ChainYInputs n × (ℝ × ℝ × ℝ × ℝ) |
      chainStep3Cleared (chainP p.1 p.2.1) (chainQ0 p.1 p.2.1 p.2.2.1)
        ((c₃ - δ) • chainW1 p.1 p.2.1 + chainW3 p.1 p.2.1) ≠ 0} ∈ nhds P₀ :=
    hcont3.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds (by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using h3₀))
  have hV4 : {p : ChainYInputs n × (ℝ × ℝ × ℝ × ℝ) |
      chainStep4' p.1 p.2.1 p.2.2.1 p.2.2.2.1 (c₄ - δ) ≠ 0} ∈ nhds P₀ :=
    hcont4.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds h4₀)
  have hVinj : {p : ChainYInputs n × (ℝ × ℝ × ℝ × ℝ) |
      vandermonde (chainY p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) ≠ 0} ∈ nhds P₀ :=
    (continuous_vandermonde.continuousAt.comp' hcontY).preimage_mem_nhds
      (isOpen_compl_singleton.mem_nhds hV0)
  have hVall : ({p : ChainYInputs n × (ℝ × ℝ × ℝ × ℝ) |
        chainStep1' p.1 (c₁ - δ) ≠ 0} ∩
      {p : ChainYInputs n × (ℝ × ℝ × ℝ × ℝ) |
        chainStep2' p.1 p.2.1 (c₂ - δ) ≠ 0} ∩
      {p : ChainYInputs n × (ℝ × ℝ × ℝ × ℝ) |
        chainStep3Cleared (chainP p.1 p.2.1) (chainQ0 p.1 p.2.1 p.2.2.1)
          ((c₃ - δ) • chainW1 p.1 p.2.1 + chainW3 p.1 p.2.1) ≠ 0} ∩
      {p : ChainYInputs n × (ℝ × ℝ × ℝ × ℝ) |
        chainStep4' p.1 p.2.1 p.2.2.1 p.2.2.2.1 (c₄ - δ) ≠ 0} ∩
      {p : ChainYInputs n × (ℝ × ℝ × ℝ × ℝ) |
        vandermonde (chainY p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) ≠ 0}) ∈ nhds P₀ :=
    Filter.inter_mem (Filter.inter_mem (Filter.inter_mem (Filter.inter_mem hV1 hV2) hV3)
      hV4) hVinj
  obtain ⟨ρ, hρpos, hρ⟩ := Metric.mem_nhds_iff.mp hVall
  -- shrink the radius for the local Lemma C
  set ε' : ℝ := min ε₀ (ρ / 2) with hε'def
  have hε'pos : 0 < ε' := by rw [hε'def]; exact lt_min hε₀ (by positivity)
  have hε'ε : ε' ≤ ε₀ := by rw [hε'def]; exact min_le_left _ _
  have hε'ρ : ε' < ρ := by
    rw [hε'def]; have h := min_le_right ε₀ (ρ / 2); linarith
  obtain ⟨U₀, hU₀open, hI₀U₀, hroots⟩ :=
    exists_chain_roots_local I₀ c₁ c₂ c₃ c₄ ε' ε' ε' ε'
      ⟨hε'pos, hε'pos, hε'pos, hε'pos⟩
      (fun δ hδ hδε => hs1 δ hδ (lt_of_lt_of_le hδε hε'ε))
      (fun δ hδ hδε => hs2 δ hδ (lt_of_lt_of_le hδε hε'ε))
      (fun δ hδ hδε => hs3 δ hδ (lt_of_lt_of_le hδε hε'ε))
      (fun δ hδ hδε => hs4 δ hδ (lt_of_lt_of_le hδε hε'ε))
      hden1 hden2
  refine ⟨U₀ ∩ Metric.ball I₀ ρ, hU₀open.inter Metric.isOpen_ball,
    ⟨hI₀U₀, Metric.mem_ball_self hρpos⟩, ?_⟩
  intro I hI
  obtain ⟨hIU₀, hIball⟩ := hI
  obtain ⟨lam, x, mu, kappa, hlam, hx, hmu, hkappa, e1, e2, e3, e4, hd1, hd2⟩ :=
    hroots I hIU₀
  have hp : dist (I, (lam, (x, (mu, kappa)))) (I₀, (c₁, (c₂, (c₃, c₄)))) < ρ := by
    rw [Prod.dist_eq]
    refine max_lt (Metric.mem_ball.mp hIball) ?_
    rw [Prod.dist_eq]
    refine max_lt ?_ ?_
    · rw [Real.dist_eq]; exact lt_of_lt_of_le hlam (le_of_lt hε'ρ)
    · rw [Prod.dist_eq]
      refine max_lt ?_ ?_
      · rw [Real.dist_eq]; exact lt_of_lt_of_le hx (le_of_lt hε'ρ)
      · rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
        exact max_lt (lt_of_lt_of_le hmu (le_of_lt hε'ρ))
          (lt_of_lt_of_le hkappa (le_of_lt hε'ρ))
  obtain ⟨⟨⟨⟨hV1', hV2'⟩, hV3'⟩, hV4'⟩, hVinj'⟩ := hρ (Metric.mem_ball.mpr hp)
  exact ⟨lam, x, mu, kappa,
    ⟨e1, e2, e3, e4, hd1, hd2, vandermonde_ne_zero_iff.mp hVinj'⟩,
    ⟨c₁ - δ, hV1'⟩, ⟨c₂ - δ, hV2'⟩, ⟨c₃ - δ, hV3'⟩, ⟨c₄ - δ, hV4'⟩⟩

/-- For `n = 7` there is an open set of inputs, containing the rational centre, on which the
chain reaches a good configuration and each step function is nonzero somewhere in its own
step variable. The `PConstructible` conjuncts and the input `S₁` condition are supplied
downstream (`exists_PC_inputs_s1`); see `exists_open_good_of_centre`. -/
theorem exists_open_good7 :
    ∃ U : Set (ChainYInputs 7), IsOpen U ∧ centre7 ∈ U ∧
      ∀ I ∈ U, ∃ lam x mu kappa : ℝ, ChainGood I lam x mu kappa ∧
        (∃ t : ℝ, chainStep1' I t ≠ 0) ∧
        (∃ t : ℝ, chainStep2' I lam t ≠ 0) ∧
        (∃ t : ℝ, chainStep3Cleared (chainP I lam) (chainQ0 I lam x)
            (t • chainW1 I lam + chainW3 I lam) ≠ 0) ∧
        (∃ t : ℝ, chainStep4' I lam x mu t ≠ 0) := by
  exact exists_open_good_of_centre centre7 centre7roots.1 centre7roots.2.1
    centre7roots.2.2.1 centre7roots.2.2.2 centre7_chain_signs centre7_denom1 centre7_denom2
    centre7_inj



/-- The `n = 8` twin of `exists_open_good7`, proved by the same generic lemma
`exists_open_good_of_centre` with the `n = 8` centre data. -/
theorem exists_open_good8 :
    ∃ U : Set (ChainYInputs 8), IsOpen U ∧ centre8 ∈ U ∧
      ∀ I ∈ U, ∃ lam x mu kappa : ℝ, ChainGood I lam x mu kappa ∧
        (∃ t : ℝ, chainStep1' I t ≠ 0) ∧
        (∃ t : ℝ, chainStep2' I lam t ≠ 0) ∧
        (∃ t : ℝ, chainStep3Cleared (chainP I lam) (chainQ0 I lam x)
            (t • chainW1 I lam + chainW3 I lam) ≠ 0) ∧
        (∃ t : ℝ, chainStep4' I lam x mu t ≠ 0) := by
  exact exists_open_good_of_centre centre8 centre8roots.1 centre8roots.2.1
    centre8roots.2.2.1 centre8roots.2.2.2 centre8_chain_signs centre8_denom1 centre8_denom2
    centre8_inj



/-! ### The lift to `b`-coordinates



The chain is a `b`-linear construction: every one of its operations is a `b`-vector

combination of the inputs with a scalar coefficient that is a *symmetric* functional of

y-vectors, hence P-constructible. So a P-constructible input `b`-tuple plus four

P-constructible step roots give a P-constructible output `b`-vector — the reason the

inverse Vandermonde map is never needed (PLAN §2.6, last sentence). -/



/-- The six starting points of the chain, as `b`-vectors. The type is the same nested
product as `ChainYInputs`; only the interpretation of the coordinates differs. -/
abbrev ChainBInputs (n : ℕ) := ChainYInputs n

/-- The y-space chain inputs attached to a `b`-vector input tuple. -/
def chainBtoY (αs : Fin n → ℝ) (I : ChainBInputs n) : ChainYInputs n :=
  (yvec αs I.1, yvec αs I.2.1, yvec αs I.2.2.1, yvec αs I.2.2.2.1,
    yvec αs I.2.2.2.2.1, yvec αs I.2.2.2.2.2)


/-! #### The `b`-coordinate chain -/



namespace ChainB



variable {m : ℕ}



/-- `P = a + λ b`. -/
def P (I : ChainBInputs m) (lam : ℝ) : Fin m → ℝ := I.a + lam • I.b



/-- The projection of `w` into `N_P` along `g`, in `b`-coordinates. -/
def projN (αs : Fin m → ℝ) (P g w : Fin m → ℝ) : Fin m → ℝ :=
  w - (yNB αs P w / yNB αs P g) • g



/-- `w̃ⱼ`, in `b`-coordinates. -/
def Wt (αs : Fin m → ℝ) (I : ChainBInputs m) (lam : ℝ) (j : Fin 3) : Fin m → ℝ :=
  match j with
  | 0 => projN αs (P I lam) I.g I.w1
  | 1 => projN αs (P I lam) I.g I.w2
  | 2 => projN αs (P I lam) I.g I.w3



/-- `q₀ = w̃₁ + x w̃₂`, in `b`-coordinates. -/
def Q0 (αs : Fin m → ℝ) (I : ChainBInputs m) (lam x : ℝ) : Fin m → ℝ :=
  Wt αs I lam 0 + x • Wt αs I lam 1



/-- `d(μ) = μ w̃₁ + w̃₃`, in `b`-coordinates. -/
def D (αs : Fin m → ℝ) (I : ChainBInputs m) (lam mu : ℝ) : Fin m → ℝ :=
  mu • Wt αs I lam 0 + Wt αs I lam 2



/-- The second intersection of the conic, in `b`-coordinates. -/
def conicPt (αs : Fin m → ℝ) (P q₀ d : Fin m → ℝ) : Fin m → ℝ :=
  q₀ - (2 * yBdot αs P q₀ d / yBdot αs P d d) • d



/-- `v = pt(μ)`, in `b`-coordinates. -/
def V (αs : Fin m → ℝ) (I : ChainBInputs m) (lam x mu : ℝ) : Fin m → ℝ :=
  conicPt αs (P I lam) (Q0 αs I lam x) (D αs I lam mu)



/-- The output `b`-vector `b* = P + κ v`. -/
def out (αs : Fin m → ℝ) (I : ChainBInputs m) (lam x mu kappa : ℝ) : Fin m → ℝ :=
  P I lam + kappa • V αs I lam x mu



/-- `yvec` of a difference is the difference of the `yvec`s. -/
theorem yvec_sub (αs : Fin n → ℝ) (b c : Fin n → ℝ) :
    yvec αs (b - c) = yvec αs b - yvec αs c := by
  funext i
  simp only [yvec, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]



/-- The `N_P`-projection of a `b`-vector maps to the y-space `chainProjN` of its
y-vector: the two constructions are the same, because the dividing coefficient
`yNB αs P w` is literally `yNBY (yvec αs P) (yvec αs w)` (`YSpace.yNB_eq_yNBY`). -/
theorem chainProjN_B {m : ℕ} (αs : Fin m → ℝ) (P g w : Fin m → ℝ)
    (_hden : yNB αs P g ≠ 0) :
    yvec αs (w - (yNB αs P w / yNB αs P g) • g)
      = chainProjN (yvec αs P) (yvec αs g) (yvec αs w) := by
  rw [yvec_sub, yvec_smul, chainProjN]
  simp only [← yNB_eq_yNBY]



theorem yvec_P (αs : Fin m → ℝ) (I : ChainBInputs m) (lam : ℝ) :
    yvec αs (P I lam) = chainP (n := m) (chainBtoY αs I) lam := by
  unfold P chainP chainBtoY ChainYInputs.a ChainYInputs.b
  rw [yvec_add, yvec_smul]



theorem yvec_Wt (αs : Fin m → ℝ) (I : ChainBInputs m) (lam : ℝ) (j : Fin 3)
    (hden : yNB αs (P I lam) I.g ≠ 0) :
    yvec αs (Wt αs I lam j) = chainWt (n := m) (chainBtoY αs I) lam j := by
  have key1 : yvec αs (projN αs (P I lam) I.g I.w1)
      = chainWt (n := m) (chainBtoY αs I) lam 0 := by
    have h := chainProjN_B αs (P I lam) I.g I.w1 hden
    rw [yvec_P] at h
    simpa [projN, chainWt, chainBtoY, ChainYInputs.g, ChainYInputs.w1] using h
  have key2 : yvec αs (projN αs (P I lam) I.g I.w2)
      = chainWt (n := m) (chainBtoY αs I) lam 1 := by
    have h := chainProjN_B αs (P I lam) I.g I.w2 hden
    rw [yvec_P] at h
    simpa [projN, chainWt, chainBtoY, ChainYInputs.g, ChainYInputs.w2] using h
  have key3 : yvec αs (projN αs (P I lam) I.g I.w3)
      = chainWt (n := m) (chainBtoY αs I) lam 2 := by
    have h := chainProjN_B αs (P I lam) I.g I.w3 hden
    rw [yvec_P] at h
    simpa [projN, chainWt, chainBtoY, ChainYInputs.g, ChainYInputs.w3] using h
  fin_cases j
  · exact key1
  · exact key2
  · exact key3



theorem yvec_Q0 (αs : Fin m → ℝ) (I : ChainBInputs m) (lam x : ℝ)
    (hden : yNB αs (P I lam) I.g ≠ 0) :
    yvec αs (Q0 αs I lam x) = chainQ0 (n := m) (chainBtoY αs I) lam x := by
  unfold Q0 chainQ0 chainW1 chainW2
  simp only [yvec_add, yvec_smul, yvec_Wt αs I lam 0 hden, yvec_Wt αs I lam 1 hden]



theorem yvec_D (αs : Fin m → ℝ) (I : ChainBInputs m) (lam mu : ℝ)
    (hden : yNB αs (P I lam) I.g ≠ 0) :
    yvec αs (D αs I lam mu) = chainD (n := m) (chainBtoY αs I) lam mu := by
  unfold D chainD
  simp only [yvec_add, yvec_smul, yvec_Wt αs I lam 0 hden, yvec_Wt αs I lam 2 hden]
  simp only [chainW1, chainW3, chainWt]


theorem yvec_conicPt (αs : Fin m → ℝ) (P q₀ d : Fin m → ℝ) (_hden : yBdot αs P d d ≠ 0) :
    yvec αs (conicPt αs P q₀ d)
      = chainConicPt (n := m) (yvec αs P) (yvec αs q₀) (yvec αs d) := by
  rw [conicPt, yvec_sub, yvec_smul, chainConicPt]
  simp only [← yBdot_eq_yBdotY]




theorem yvec_V (αs : Fin m → ℝ) (I : ChainBInputs m) (lam x mu : ℝ)
    (h1 : yNB αs (P I lam) I.g ≠ 0)
    (h2 : yBdot αs (P I lam) (D αs I lam mu) (D αs I lam mu) ≠ 0) :
    yvec αs (V αs I lam x mu) = chainV (n := m) (chainBtoY αs I) lam x mu := by
  have h2' : yBdotY (yvec αs (P I lam)) (yvec αs (D αs I lam mu))
      (yvec αs (D αs I lam mu)) ≠ 0 := by
    rw [← yBdot_eq_yBdotY]
    exact h2
  unfold V chainV
  rw [yvec_conicPt αs _ _ _ h2', yvec_P, yvec_Q0 αs I lam x h1, yvec_D αs I lam mu h1]



end ChainB



/-- **The two versions agree.** Every `b`-coordinate the chain produces has the y-vector

the y-space chain assigns it. -/
theorem chainBLift_yvec (αs : Fin n → ℝ) (I : ChainBInputs n)
    (lam x mu kappa : ℝ)
    (h1 : yNB αs (ChainB.P I lam) I.g ≠ 0)
    (h2 : yBdot αs (ChainB.P I lam) (ChainB.D αs I lam mu) (ChainB.D αs I lam mu) ≠ 0) :
    yvec αs (ChainB.out αs I lam x mu kappa) = chainY (chainBtoY αs I) lam x mu kappa := by
  unfold ChainB.out chainY
  rw [yvec_add, yvec_smul, ChainB.yvec_V αs I lam x mu h1 h2, ChainB.yvec_P]



/-! ### The step polynomials, and P-constructibility of the step roots



Each of the four steps is a polynomial in its own variable whose coefficients are

*symmetric* functionals of the y-vectors of the inputs, and therefore P-constructible.

That is the whole content of PLAN §2.6. The degrees are `3, 2, 6, 5`;

`root_Pconstructible_le_six_coeffs` then makes every step root P-constructible. -/



/-! #### The four step polynomials

Each step polynomial's coefficients are *symmetric* functionals of the y-vectors of the
inputs, hence weighted power sums `∑ᵢ αs i ^ m` of the roots, and
`psumRoots_Pconstructible_of_roots` makes them P-constructible once the root hypotheses
`(hmon) (hn) (hnat) (hsep) (hcoef) (hαs) (hnd)` are available. Everything downstream
(`exists_step3_poly`, `stepRoots_Pconstructible`, `chainBLift_Pconstructible`,
`exists_oddTschirnhaus`) is proved in terms of these four. -/



/-- **Step 1** as a degree-`≤ 3` polynomial with P-constructible coefficients. -/
theorem exists_step1_poly_of_roots {q : ℝ[X]} {αs : Fin n → ℝ} (a b : Fin n → ℝ)
    (hmon : q.Monic) (hn : 0 < n) (hnat : q.natDegree = n) (hsep : q.Separable)
    (hcoef : ∀ k, PConstructible (q.coeff k)) (hαs : ∀ i : Fin n, q.eval (αs i) = 0)
    (hnd : Function.Injective αs)
    (ha : ∀ k, PConstructible (a k)) (hb : ∀ k, PConstructible (b k)) :
    ∃ g : ℝ[X], g.natDegree ≤ 3 ∧ (∀ k, PConstructible (g.coeff k)) ∧
      ∀ lam : ℝ, g.eval lam = chainStep1 (yvec αs a) (yvec αs b) lam := by
  obtain ⟨g, hdeg, hcoeff, heval⟩ :=
    psumY_line_poly (αs := αs) (u := a) (v := b) hmon hn hnat hsep hcoef hαs hnd ha hb 3
  refine ⟨g, hdeg, hcoeff, fun lam => ?_⟩
  rw [heval, chainStep1, yvec_add, yvec_smul]



/-- **Step 4** as a degree-`≤ 5` polynomial with P-constructible coefficients. -/
theorem exists_step4_poly_of_roots {q : ℝ[X]} {αs : Fin n → ℝ} (P v : Fin n → ℝ)
    (hmon : q.Monic) (hn : 0 < n) (hnat : q.natDegree = n) (hsep : q.Separable)
    (hcoef : ∀ k, PConstructible (q.coeff k)) (hαs : ∀ i : Fin n, q.eval (αs i) = 0)
    (hnd : Function.Injective αs)
    (hP : ∀ k, PConstructible (P k)) (hv : ∀ k, PConstructible (v k)) :
    ∃ f : ℝ[X], f.natDegree ≤ 5 ∧ (∀ k, PConstructible (f.coeff k)) ∧
      ∀ kappa : ℝ, f.eval kappa = chainStep4 (yvec αs P) (yvec αs v) kappa := by
  obtain ⟨f, hdeg, hcoeff, heval⟩ :=
    psumY_line_poly (αs := αs) (u := P) (v := v) hmon hn hnat hsep hcoef hαs hnd hP hv 5
  refine ⟨f, hdeg, hcoeff, fun kappa => ?_⟩
  rw [heval, chainStep4, yvec_add, yvec_smul]



/-- The same, in `b`-coordinates. -/
theorem yConicB_add_smul_right {n : ℕ} (αs : Fin n → ℝ) (P u w : Fin n → ℝ) (s : ℝ) :
    yConicB αs P (u + s • w)
      = yConicB αs P u + 2 * s * yBdot αs P u w + s ^ 2 * yConicB αs P w := by
  rw [yConicB_eq_yConicY, yvec_add, yvec_smul, yConicY_add_smul_right, ← yBdot_eq_yBdotY,
    ← yConicB_eq_yConicY, ← yConicB_eq_yConicY]

/-- **Step 2** as a degree-`≤ 2` polynomial with P-constructible coefficients. The two

coefficients are `yConicB αs P w̃₁` and `yConicB αs P w̃₂`, the second pairing of the
`N_P`-projections; those are P-constructible because the projections are
`w - (⟨P,w⟩/⟨P,g⟩)·g` and both pairings are. -/
theorem exists_step2_poly_of_roots {q : ℝ[X]} {αs : Fin n → ℝ} (P g w₁ w₂ : Fin n → ℝ)
    (hmon : q.Monic) (hn : 0 < n) (hnat : q.natDegree = n) (hsep : q.Separable)
    (hcoef : ∀ k, PConstructible (q.coeff k)) (hαs : ∀ i : Fin n, q.eval (αs i) = 0)
    (hnd : Function.Injective αs)
    (hP : ∀ k, PConstructible (P k)) (hg : ∀ k, PConstructible (g k))
    (hw1 : ∀ k, PConstructible (w₁ k)) (hw2 : ∀ k, PConstructible (w₂ k)) :
    ∃ f : ℝ[X], f.natDegree ≤ 2 ∧ (∀ k, PConstructible (f.coeff k)) ∧
      ∀ x : ℝ, f.eval x
        = chainStep2 (yvec αs P) (yvec αs g) (yvec αs w₁) (yvec αs w₂) x := by
  have hprojPC (w : Fin n → ℝ) (hw : ∀ k, PConstructible (w k)) :
      ∀ k, PConstructible (ChainB.projN αs P g w k) := by
    intro k
    rw [ChainB.projN, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    exact PConstructible.sub (hw k)
      (PConstructible.mul
        (PConstructible.div
          (yNB_Pconstructible hmon hn hnat hsep hcoef hαs hnd hP hw)
          (yNB_Pconstructible hmon hn hnat hsep hcoef hαs hnd hP hg))
        (hg k))
  have hproj (w : Fin n → ℝ) :
      chainProjN (yvec αs P) (yvec αs g) (yvec αs w)
        = yvec αs (ChainB.projN αs P g w) := by
    unfold chainProjN ChainB.projN
    rw [← yvec_smul, ← ChainB.yvec_sub]
    simp only [← yNB_eq_yNBY]
  set a : ℝ := yConicB αs P (ChainB.projN αs P g w₁) with ha_def
  set b : ℝ := 2 * yBdot αs P (ChainB.projN αs P g w₁) (ChainB.projN αs P g w₂) with hb_def
  set c : ℝ := yConicB αs P (ChainB.projN αs P g w₂) with hc_def
  have haPC : PConstructible a := by
    rw [ha_def]
    exact yConicB_Pconstructible hmon hn hnat hsep hcoef hαs hnd hP (hprojPC w₁ hw1)
  have hbPC : PConstructible b := by
    rw [hb_def]
    exact PConstructible.mul (nat_Pconstructible 2)
      (yBdot_Pconstructible hmon hn hnat hsep hcoef hαs hnd hP (hprojPC w₁ hw1)
        (hprojPC w₂ hw2))
  have hcPC : PConstructible c := by
    rw [hc_def]
    exact yConicB_Pconstructible hmon hn hnat hsep hcoef hαs hnd hP (hprojPC w₂ hw2)
  have hXcoeff : ∀ k : ℕ, PConstructible (Polynomial.X.coeff k) := by
    intro k
    rw [Polynomial.coeff_X]
    split_ifs
    · exact PConstructible.base_one
    · exact zero_Pconstructible
  have hlincoeff : ∀ k : ℕ,
      PConstructible ((Polynomial.C b + Polynomial.C c * Polynomial.X).coeff k) := by
    intro k
    rw [Polynomial.coeff_add]
    exact PConstructible.add (coeff_C_Pconstructible hbPC k)
      (coeff_mul_Pconstructible (fun i => coeff_C_Pconstructible hcPC i) hXcoeff k)
  have hXsqcoeff : ∀ k : ℕ, PConstructible ((Polynomial.X ^ 2).coeff k) := by
    intro k
    simpa [pow_two] using (coeff_mul_Pconstructible hXcoeff hXcoeff k)
  refine ⟨Polynomial.C a + Polynomial.C b * Polynomial.X
    + Polynomial.C c * Polynomial.X ^ 2, ?_, ?_, ?_⟩
  · have h1 : (Polynomial.C a + Polynomial.C b * Polynomial.X).natDegree ≤ 1 :=
      Polynomial.natDegree_add_le_of_degree_le (by simp)
        (by simpa using Polynomial.natDegree_C_mul_X_pow_le b 1)
    refine le_trans
      (Polynomial.natDegree_add_le_of_degree_le (by omega)
        (Polynomial.natDegree_C_mul_X_pow_le c 2)) (by omega)
  · intro k
    rw [Polynomial.coeff_add, Polynomial.coeff_add]
    exact PConstructible.add
      (PConstructible.add (coeff_C_Pconstructible haPC k)
        (C_mul_coeff_Pconstructible hbPC hXcoeff k))
      (C_mul_coeff_Pconstructible hcPC hXsqcoeff k)
  · intro x
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X]
    rw [chainStep2, hproj w₁, hproj w₂, yConicY_add_smul_right, ← yConicB_eq_yConicY,
      ← yBdot_eq_yBdotY, ← yConicB_eq_yConicY, ← ha_def, ← hc_def, hb_def]
    ring

/-! ### Step 3: the cleared cubic is a polynomial of degree `≤ 6`

**Why the cleared step-3 equation is a polynomial at all.** Along the affine line
`d = w₃ + mu • w₁` the cleared form is `Σᵢ (Yq₀ᵢ·B − 2·C·dᵢ)³` with `B = ⟨P,d,d⟩` and
`C = ⟨P,q₀,d⟩`. The pairing `⟨P,·,·⟩ = Σᵢ YPᵢ·YUᵢ·YVᵢ` is *trilinear* in its three
y-vectors, so `B` is a **quadratic** in `mu` and `C` is
**linear**: the whole thing is a polynomial of degree `2·3 = 6`
in `mu` — the largest degree the chain ever reaches, and the reason
`root_Pconstructible_le_six_coeffs` is the engine. The witness is

```
p    = Σᵢ (C (Yq₀ᵢ) • Bp − C 2 • (Cp • affᵢ)) ^ 3
affᵢ = C (Yw₃ᵢ) + C (Yw₁ᵢ) • X        (degree ≤ 1)
Bp   = Σᵢ C (YPᵢ) • affᵢ ^ 2           (degree ≤ 2)
Cp   = Σᵢ C (YPᵢ • Yq₀ᵢ) • affᵢ        (degree ≤ 1)
```

**Why the coefficients are P-constructible.** `psumY_line_poly` does *not* apply — the
cleared form is a cubic of a quadratic, not a power sum of an affine line — but the
*engine* behind it does. A polynomial of degree `≤ 6` is determined by its values at the
seven rational nodes `0,…,6`, and the `Lagrange` basis at those nodes has P-constructible
coefficients, so the four helpers `prod_coeff_Pconstructible`,
`X_sub_C_coeff_Pconstructible`, `basisDivisor_coeff_Pconstructible` and
`basis_coeff_Pconstructible` from `YSpace` are used directly. The *node values* are
P-constructible because the cleared form is itself a power sum: by
`chainStep3Cleared_eq_psumY` below it is `psumY (yvec αs (B • q₀ − (2 • C) • b)) 3` with
`B = yBdot αs P b b` and `C = yBdot αs P q₀ b`, both P-constructible by
`yBdot_Pconstructible`, so `psum_yvec_Pconstructible` applies to the P-constructible
`b`-vector `B • q₀ − (2 • C) • b` at every rational `b`. -/

/-- **The cleared form is itself a power sum.** `chainStep3Cleared P q₀ b` is the cubic
power sum of the y-vector of the denominator-cleared conic point
`⟨P,b,b⟩ • q₀ − 2·⟨P,q₀,b⟩ • b`, i.e. of `yvec αs (B • q₀ − (2 • C) • b)` — which is what
lets `psum_yvec_Pconstructible` be applied to it. -/
private theorem chainStep3Cleared_eq_psumY (αs : Fin n → ℝ) (P q₀ b : Fin n → ℝ) (B C : ℝ)
    (hB : B = yBdotY (yvec αs P) (yvec αs b) (yvec αs b))
    (hC : C = yBdotY (yvec αs P) (yvec αs q₀) (yvec αs b)) :
    chainStep3Cleared (yvec αs P) (yvec αs q₀) (yvec αs b)
      = psumY (yvec αs (B • q₀ - (2 • C) • b)) 3 := by
  simp only [chainStep3Cleared, psumY, psumFinY, ChainB.yvec_sub, yvec_smul,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [hB, hC]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- The affine polynomial of the step-3 direction: the `i`-th coordinate of
`d = w₃ + mu • w₁`, as a polynomial in `mu`. -/
private def step3Aff (αs : Fin n → ℝ) (w₁ w₃ : Fin n → ℝ) (i : Fin n) : ℝ[X] :=
  Polynomial.C (yvec αs w₃ i) + Polynomial.C (yvec αs w₁ i) * Polynomial.X

/-- `step3Aff` has degree `≤ 1`, so its second power has degree `≤ 2`. -/
private theorem step3Aff_natDegree (αs : Fin n → ℝ) (w₁ w₃ : Fin n → ℝ) (i : Fin n) :
    (step3Aff αs w₁ w₃ i).natDegree ≤ 1 := by
  unfold step3Aff
  exact Polynomial.natDegree_add_le_of_degree_le (by simp)
    (by simpa using Polynomial.natDegree_C_mul_X_pow_le (yvec αs w₁ i) 1)

/-- `step3Aff αs w₁ w₃ i` evaluated at `s` is the `i`-th entry of `w₃ + s • w₁` in
y-coordinates. -/
private theorem step3Aff_eval (αs : Fin n → ℝ) (w₁ w₃ : Fin n → ℝ) (i : Fin n) (s : ℝ) :
    (step3Aff αs w₁ w₃ i).eval s = yvec αs w₃ i + s * yvec αs w₁ i := by
  unfold step3Aff
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  ring

/-- Step 3, denominator cleared, as a degree-`≤ 6` polynomial with P-constructible
coefficients.

The witness is `p = Σᵢ (C (Yq₀ᵢ) • Bp − C 2 • (Cp • affᵢ))³` with `Bp`, `Cp` the two
denominator pairings written as polynomials in `mu`; the section note above gives the
degree count and explains why the coefficients come from the `Lagrange` engine copied in
above. -/
theorem exists_step3_poly {q : ℝ[X]} {αs : Fin n → ℝ} (P q₀ w₁ w₃ : Fin n → ℝ)
    (hmon : q.Monic) (hn : 0 < n) (hnat : q.natDegree = n) (hsep : q.Separable)
    (hcoef : ∀ k, PConstructible (q.coeff k)) (hαs : ∀ i : Fin n, q.eval (αs i) = 0)
    (hnd : Function.Injective αs)
    (hP : ∀ k, PConstructible (P k)) (hq₀ : ∀ k, PConstructible (q₀ k))
    (hw₁ : ∀ k, PConstructible (w₁ k)) (hw₃ : ∀ k, PConstructible (w₃ k)) :
    ∃ f : ℝ[X], f.natDegree ≤ 6 ∧ (∀ k, PConstructible (f.coeff k)) ∧
      ∀ mu : ℝ, f.eval mu
        = chainStep3Cleared (yvec αs P) (yvec αs q₀) (mu • yvec αs w₁ + yvec αs w₃) := by
  classical
  -- HALF (a). The two pairings `B = ⟨P,d,d⟩` and `C = ⟨P,q₀,d⟩`, as polynomials in `mu`.
  set Bp : ℝ[X] := ∑ i : Fin n, Polynomial.C (yvec αs P i) * (step3Aff αs w₁ w₃ i) ^ 2
    with hBp
  set Cp : ℝ[X] :=
    ∑ i : Fin n, Polynomial.C (yvec αs P i * yvec αs q₀ i) * step3Aff αs w₁ w₃ i
    with hCp
  have hBpdeg : Bp.natDegree ≤ 2 := by
    rw [hBp]
    refine
      Polynomial.natDegree_sum_le_of_forall_le (Finset.univ : Finset (Fin n)) _ fun i _ => ?_
    refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    simpa using Polynomial.natDegree_pow_le_of_le 2 (step3Aff_natDegree αs w₁ w₃ i)
  have hCpdeg : Cp.natDegree ≤ 1 := by
    rw [hCp]
    refine Polynomial.natDegree_sum_le_of_forall_le (Finset.univ : Finset (Fin n)) _
      fun i _ => ?_
    exact le_trans (Polynomial.natDegree_C_mul_le _ _) (step3Aff_natDegree αs w₁ w₃ i)
  have hBpval (s : ℝ) : Bp.eval s
      = yBdotY (yvec αs P) (yvec αs w₃ + s • yvec αs w₁)
          (yvec αs w₃ + s • yvec αs w₁) := by
    rw [hBp, Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, yBdotY, ymoment3Y]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [step3Aff_eval, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hCpval (s : ℝ) : Cp.eval s
      = yBdotY (yvec αs P) (yvec αs q₀) (yvec αs w₃ + s • yvec αs w₁) := by
    rw [hCp, Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, yBdotY, ymoment3Y]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [step3Aff_eval, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  -- HALF (b). The cleared form itself: a cubic of a quadratic, hence degree `≤ 6`.
  set p : ℝ[X] := ∑ i : Fin n,
      (Polynomial.C (yvec αs q₀ i) * Bp
        - Polynomial.C 2 * (Cp * step3Aff αs w₁ w₃ i)) ^ 3 with hp
  have htdeg (i : Fin n) :
      (Polynomial.C (yvec αs q₀ i) * Bp
        - Polynomial.C 2 * (Cp * step3Aff αs w₁ w₃ i)).natDegree ≤ 2 := by
    refine le_trans (Polynomial.natDegree_sub_le_of_le
      (Polynomial.natDegree_C_mul_le _ _)
      (Polynomial.natDegree_C_mul_le _ _)) ?_
    exact max_le hBpdeg
      (le_trans (Polynomial.natDegree_mul_le_of_le hCpdeg (step3Aff_natDegree αs w₁ w₃ i))
        (by omega))
  have hpdeg : p.natDegree ≤ 6 := by
    rw [hp]
    refine le_trans (Polynomial.natDegree_sum_le_of_forall_le
      (Finset.univ : Finset (Fin n)) (n := 6) _ fun i _ => ?_) (by omega)
    exact le_trans (Polynomial.natDegree_pow_le_of_le 3 (htdeg i)) (by omega)
  have hval (s : ℝ) : p.eval s
      = chainStep3Cleared (yvec αs P) (yvec αs q₀) (yvec αs w₃ + s • yvec αs w₁) := by
    rw [hp, Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_pow, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_C, chainStep3Cleared, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, hBpval, hCpval]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [step3Aff_eval]
    ring
  -- HALF (c). Interpolation at the seven rational nodes `0, …, 6`, exactly as in
  -- `YSpace.psumY_line_poly`: a degree-`≤ 6` polynomial is a rational linear combination
  -- of the `Lagrange` basis polynomials at those nodes.
  set vv : Fin (6 + 1) → ℝ := fun r => (r : ℕ)
  have hinj : Set.InjOn vv ((Finset.univ : Finset (Fin (6 + 1))) : Set (Fin (6 + 1))) := by
    rintro i _ j _ hij
    apply Fin.ext
    exact Nat.cast_injective hij
  have hcard : 6 < (Finset.univ : Finset (Fin (6 + 1))).card := by simp
  have hpdeg' : p.degree ≤ 6 :=
    (Polynomial.natDegree_le_iff_degree_le (p := p) (n := 6)).mp hpdeg
  have hdeglt : p.degree < (Finset.univ : Finset (Fin (6 + 1))).card :=
    lt_of_le_of_lt hpdeg' (Nat.cast_lt.mpr hcard)
  have hgp : p = Lagrange.interpolate (Finset.univ : Finset (Fin (6 + 1))) vv
      fun r => p.eval (vv r) :=
    Lagrange.eq_interpolate_of_eval_eq (fun r => p.eval (vv r)) hinj hdeglt fun _ _ => rfl
  set g : ℝ[X] := Lagrange.interpolate (Finset.univ : Finset (Fin (6 + 1))) vv
    fun r => p.eval (vv r) with hg
  have hg' : g = p := hg.trans hgp.symm
  refine ⟨g, ?_, ?_, ?_⟩
  · rw [hg']
    exact hpdeg
  · intro j
    have hvi : ∀ i : Fin (6 + 1), PConstructible (vv i) := fun i => nat_Pconstructible i
    have hw : ∀ i : Fin (6 + 1), PConstructible (p.eval (vv i)) := by
      intro i
      rw [hval, ← yvec_smul, ← yvec_add]
      have hbrPC : ∀ k, PConstructible ((w₃ + vv i • w₁) k) := by
        intro k
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        exact PConstructible.add (hw₃ k) (PConstructible.mul (hvi i) (hw₁ k))
      have hBPC : PConstructible (yBdotY (yvec αs P) (yvec αs (w₃ + vv i • w₁))
          (yvec αs (w₃ + vv i • w₁))) :=
        yBdot_Pconstructible hmon hn hnat hsep hcoef hαs hnd hP hbrPC hbrPC
      have hCPC : PConstructible (yBdotY (yvec αs P) (yvec αs q₀)
          (yvec αs (w₃ + vv i • w₁))) :=
        yBdot_Pconstructible hmon hn hnat hsep hcoef hαs hnd hP hq₀ hbrPC
      rw [chainStep3Cleared_eq_psumY αs P q₀ (w₃ + vv i • w₁) _ _ rfl rfl]
      refine psum_yvec_Pconstructible (αs := αs)
        (b := (yBdotY (yvec αs P) (yvec αs (w₃ + vv i • w₁))
            (yvec αs (w₃ + vv i • w₁))) • q₀
          - (2 • yBdotY (yvec αs P) (yvec αs q₀) (yvec αs (w₃ + vv i • w₁)))
            • (w₃ + vv i • w₁))
        hmon hn hnat hsep hcoef hαs hnd ?_ 3
      intro k
      convert PConstructible.sub (PConstructible.mul hBPC (hq₀ k))
        (PConstructible.mul (PConstructible.mul (nat_Pconstructible 2) hCPC) (hbrPC k)) using 1;
        simp; ring
    rw [hg, Lagrange.interpolate_apply, Polynomial.finsetSum_coeff]
    refine Finset.sum_induction _ PConstructible (fun _ _ ha hb => PConstructible.add ha hb)
      zero_Pconstructible fun i _ => ?_
    exact C_mul_coeff_Pconstructible (hw i) (basis_coeff_Pconstructible hvi i) j
  · intro s
    rw [hg', hval]
    exact congrArg (fun d => chainStep3Cleared (yvec αs P) (yvec αs q₀) d) (add_comm _ _)



/-- Step 4 as a degree-`≤ 5` polynomial with P-constructible coefficients. -/
theorem exists_step4_poly {q : ℝ[X]} {αs : Fin n → ℝ} (P v : Fin n → ℝ)
    (hmon : q.Monic) (hn : 0 < n) (hnat : q.natDegree = n) (hsep : q.Separable)
    (hcoef : ∀ k, PConstructible (q.coeff k)) (hαs : ∀ i : Fin n, q.eval (αs i) = 0)
    (hnd : Function.Injective αs)
    (hP : ∀ k, PConstructible (P k)) (hv : ∀ k, PConstructible (v k)) :
    ∃ f : ℝ[X], f.natDegree ≤ 5 ∧ (∀ k, PConstructible (f.coeff k)) ∧
      ∀ kappa : ℝ, f.eval kappa = chainStep4 (yvec αs P) (yvec αs v) kappa := by
  exact exists_step4_poly_of_roots P v hmon hn hnat hsep hcoef hαs hnd hP hv



/-- Every step root of a good chain is P-constructible.

**RESTATEMENT — the two defects listed in the previous WARNING on this `sorry` are
fixed here, and the proof is real.**

1. *Missing root hypotheses.*  The seven `(hmon) (hn) (hnat) (hsep) (hcoef) (hαs) (hnd)`
   are now hypotheses.  They are needed because the coefficients of a step polynomial are
   symmetric functionals of the `b`-vectors of the inputs, and `yNB_Pconstructible`,
   `yBdot_Pconstructible`, `yConicB_Pconstructible` — which build every coefficient of
   step 2, through `ChainB.projN` — return a P-constructible number only for a `b`-vector
   whose entries are powers of a polynomial `q` with separable roots and P-constructible
   coefficients.  See the section note above.

2. *Non-degeneracy.*  `root_Pconstructible_le_six_coeffs` needs its polynomial to be
   `≠ 0`, and `ChainGood` does not give that.  The four new conjuncts `(hne1) … (hne4)`
   do: each says that the corresponding step *function* is not identically `0`.  That is
   exactly the missing hypothesis, and it is a condition on the data `(I, lam, x, mu)`,
   not on the existential witness, so `exists_open_good7/8` can supply it.

   **A non-zero leading coefficient is NOT enough**, which is the substantive finding
   behind this restatement.  `chainStep1 A B lam = psumY A 3 + 3·lam·yNBY A B
   + 3·lam^2·yConicY A B + lam^3·psumY B 3`, and the leading coefficient
   `psumY B 3 = ∑ᵢ Bᵢ³` vanishes already for `B = ![1, -1] ≠ 0`; worse, with
   `A = B = ![1, -1]` (so `n = 2`) **all four** coefficients vanish, i.e.
   `chainStep1 A B ≡ 0` although `B ≠ 0`.  The same objection defeats
   `ChainB.V αs I lam x mu ≠ 0` for step 4 and `ChainB.Wt αs I lam j ≠ 0` for steps 2
   and 3: nonzero direction, identically zero step function.  So the condition really is
   "not identically zero", and it cannot be replaced by the simpler data conditions.

   *Recommendation to the caller:* **`ChainGood` should be extended with these four
   conjuncts.**  At each rational centre a strict sign change across each step function
   makes each step nonzero *somewhere*, and "step `k` is nonzero somewhere" is **open**
   in `(I, lam, …)`, so the open set of good inputs inherits all four.  `ChainGood` is not
   edited here, since it has other callers.

   For step 3 the hypothesis is on `chainStep3Cleared`, not on `chainStep3'`, because
   `chainStep3Cleared P q₀ (t • w₁ + w₃) = yBdotY P (t • w₁ + w₃) (t • w₁ + w₃) ^ 3 *
   chainStep3' …` and that cubic denominator may vanish away from the good set;
   `chainStep3Cleared` is the polynomial the degree bound `≤ 6` applies to.

   `hchain` is used only for the four step equations and the two denominators; its
   `Function.Injective (chainY …)` conjunct is not needed. -/
theorem stepRoots_Pconstructible {q : ℝ[X]} {αs : Fin n → ℝ} {I : ChainBInputs n}
    (hmon : q.Monic) (hn : 0 < n) (hnat : q.natDegree = n) (hsep : q.Separable)
    (hcoef : ∀ k, PConstructible (q.coeff k)) (hαs : ∀ i : Fin n, q.eval (αs i) = 0)
    (hnd : Function.Injective αs)
    (hI : ∀ k, PConstructible (I.a k) ∧ PConstructible (I.b k) ∧ PConstructible (I.g k) ∧
      PConstructible (I.w1 k) ∧ PConstructible (I.w2 k) ∧ PConstructible (I.w3 k))
    (lam x mu kappa : ℝ) (hchain : ChainGood (chainBtoY αs I) lam x mu kappa)
    (hne1 : ∃ t : ℝ, chainStep1' (chainBtoY αs I) t ≠ 0)
    (hne2 : ∃ t : ℝ, chainStep2' (chainBtoY αs I) lam t ≠ 0)
    (hne3 : ∃ t : ℝ, chainStep3Cleared (chainP (chainBtoY αs I) lam)
      (chainQ0 (chainBtoY αs I) lam x)
      (t • chainW1 (chainBtoY αs I) lam + chainW3 (chainBtoY αs I) lam) ≠ 0)
    (hne4 : ∃ t : ℝ, chainStep4' (chainBtoY αs I) lam x mu t ≠ 0) :
    PConstructible lam ∧ PConstructible x ∧ PConstructible mu ∧ PConstructible kappa := by
  have ha : ∀ k, PConstructible (I.a k) := fun k => (hI k).1
  have hb : ∀ k, PConstructible (I.b k) := fun k => (hI k).2.1
  have hg : ∀ k, PConstructible (I.g k) := fun k => (hI k).2.2.1
  have hw1 : ∀ k, PConstructible (I.w1 k) := fun k => (hI k).2.2.2.1
  have hw2 : ∀ k, PConstructible (I.w2 k) := fun k => (hI k).2.2.2.2.1
  have hw3 : ∀ k, PConstructible (I.w3 k) := fun k => (hI k).2.2.2.2.2
  -- the `chainProjN` denominator, in `b`-coordinates: `ChainGood`'s first nonzero
  have hden1Y : yNBY (yvec αs (ChainB.P I lam)) (yvec αs I.g) ≠ 0 := by
    rw [ChainB.yvec_P]
    simpa only [chainBtoY, ChainYInputs.g] using hchain.2.2.2.2.1
  have hden1 : yNB αs (ChainB.P I lam) I.g ≠ 0 := hden1Y
  -- the `g` slot of the y-space chain, spelled both ways
  have hgdef : (chainBtoY αs I).g = yvec αs I.g := by
    simp only [chainBtoY, ChainYInputs.g]
  -- step 1: a cubic, from `psumY_line_poly`
  have hstep1 (t : ℝ) : chainStep1' (chainBtoY αs I) t
      = chainStep1 (yvec αs I.a) (yvec αs I.b) t := rfl
  obtain ⟨g1, hdeg1, hcoeff1, heval1⟩ :=
    exists_step1_poly_of_roots I.a I.b hmon hn hnat hsep hcoef hαs hnd ha hb
  have hg1ne : g1 ≠ 0 := by
    rintro rfl
    obtain ⟨t, ht⟩ := hne1
    rw [hstep1 t] at ht
    exact ht (by simpa using (heval1 t).symm)
  have hstep1lam : chainStep1 (yvec αs I.a) (yvec αs I.b) lam = 0 := by
    rw [← hstep1 lam]
    simpa only [chainStep1'] using hchain.1
  have hlam : PConstructible lam :=
    root_Pconstructible_le_six_coeffs hg1ne (by omega) hcoeff1
      (by rw [heval1 lam, hstep1lam])
  -- the `b`-vector `P = a + lam b`, and the three `N_P`-projections
  have hP : ∀ k, PConstructible (ChainB.P I lam k) := by
    intro k
    rw [ChainB.P, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact PConstructible.add (ha k) (PConstructible.mul hlam (hb k))
  have hproj (w : Fin n → ℝ) (hw : ∀ k, PConstructible (w k)) :
      ∀ k, PConstructible (ChainB.projN αs (ChainB.P I lam) I.g w k) := by
    intro k
    rw [ChainB.projN, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    exact PConstructible.sub (hw k)
      (PConstructible.mul
        (PConstructible.div
          (yNB_Pconstructible hmon hn hnat hsep hcoef hαs hnd hP hw)
          (yNB_Pconstructible hmon hn hnat hsep hcoef hαs hnd hP hg))
        (hg k))
  have hW1 : ∀ k, PConstructible (ChainB.Wt αs I lam 0 k) := by
    simpa only [ChainB.Wt] using (hproj I.w1 hw1)
  have hW2 : ∀ k, PConstructible (ChainB.Wt αs I lam 1 k) := by
    simpa only [ChainB.Wt] using (hproj I.w2 hw2)
  -- step 2: a quadratic in `x`, from the line expansion of the conic form
  have hstep2 (t : ℝ) : chainStep2' (chainBtoY αs I) lam t
      = chainStep2 (yvec αs (ChainB.P I lam)) (yvec αs I.g)
        (yvec αs (ChainB.Wt αs I lam 0)) (yvec αs (ChainB.Wt αs I lam 1)) t := by
    simp only [chainStep2', chainW1, chainW2]
    rw [← ChainB.yvec_P αs I lam, ← ChainB.yvec_Wt αs I lam 0 hden1,
      ← ChainB.yvec_Wt αs I lam 1 hden1, hgdef]
  obtain ⟨g2, hdeg2, hcoeff2, heval2⟩ := exists_step2_poly_of_roots (P := ChainB.P I lam)
    I.g (ChainB.Wt αs I lam 0) (ChainB.Wt αs I lam 1)
    hmon hn hnat hsep hcoef hαs hnd hP hg hW1 hW2
  have hg2ne : g2 ≠ 0 := by
    rintro rfl
    obtain ⟨t, ht⟩ := hne2
    rw [hstep2 t] at ht
    exact ht (by simpa using (heval2 t).symm)
  have hstep2x : chainStep2 (yvec αs (ChainB.P I lam)) (yvec αs I.g)
    (yvec αs (ChainB.Wt αs I lam 0)) (yvec αs (ChainB.Wt αs I lam 1)) x = 0 := by
    rw [← hstep2 x]
    simpa only [chainStep2'] using hchain.2.1
  have hx : PConstructible x :=
    root_Pconstructible_le_six_coeffs hg2ne (by omega) hcoeff2
      (by rw [heval2 x, hstep2x])
  -- `q₀` and the third projection, needed by steps 3 and 4
  have hW3 : ∀ k, PConstructible (ChainB.Wt αs I lam 2 k) := by
    simpa only [ChainB.Wt] using (hproj I.w3 hw3)
  have hQ0 : ∀ k, PConstructible (ChainB.Q0 αs I lam x k) := by
    intro k
    rw [ChainB.Q0, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact PConstructible.add (hW1 k) (PConstructible.mul hx (hW2 k))
  -- step 3: the denominator-cleared sextic
  have hlin (t : ℝ) : t • yvec αs (ChainB.Wt αs I lam 0)
      + yvec αs (ChainB.Wt αs I lam 2) = chainD (chainBtoY αs I) lam t := by
    have h := ChainB.yvec_D αs I lam t hden1
    rw [ChainB.D, yvec_add, yvec_smul] at h
    exact h
  have hcl (t : ℝ) : chainStep3Cleared (yvec αs (ChainB.P I lam))
      (yvec αs (ChainB.Q0 αs I lam x))
      (t • yvec αs (ChainB.Wt αs I lam 0) + yvec αs (ChainB.Wt αs I lam 2))
      = chainStep3Cleared (chainP (chainBtoY αs I) lam) (chainQ0 (chainBtoY αs I) lam x)
        (t • chainW1 (chainBtoY αs I) lam + chainW3 (chainBtoY αs I) lam) := by
    rw [ChainB.yvec_P, ChainB.yvec_Q0 αs I lam x hden1, chainW1, chainW3,
      ChainB.yvec_Wt αs I lam 0 hden1, ChainB.yvec_Wt αs I lam 2 hden1]
  obtain ⟨g3, hdeg3, hcoeff3, heval3⟩ := exists_step3_poly (P := ChainB.P I lam)
    (ChainB.Q0 αs I lam x) (ChainB.Wt αs I lam 0) (ChainB.Wt αs I lam 2)
    hmon hn hnat hsep hcoef hαs hnd hP hQ0 hW1 hW3
  have hg3ne : g3 ≠ 0 := by
    rintro rfl
    obtain ⟨t, ht⟩ := hne3
    rw [← hcl t] at ht
    exact ht (by simpa using (heval3 t).symm)
  have hden2' : yBdotY (chainP (chainBtoY αs I) lam)
      (mu • chainW1 (chainBtoY αs I) lam + chainW3 (chainBtoY αs I) lam)
      (mu • chainW1 (chainBtoY αs I) lam + chainW3 (chainBtoY αs I) lam) ≠ 0 := by
    simpa only [chainD, chainW1, chainW3, chainWt] using hchain.2.2.2.2.2.1
  have h3zero : chainStep3 (chainP (chainBtoY αs I) lam) (chainQ0 (chainBtoY αs I) lam x)
      (chainW1 (chainBtoY αs I) lam) (chainW3 (chainBtoY αs I) lam) mu = 0 := by
    simpa only [chainStep3'] using hchain.2.2.1
  have hclmu : chainStep3Cleared (chainP (chainBtoY αs I) lam)
      (chainQ0 (chainBtoY αs I) lam x)
      (mu • chainW1 (chainBtoY αs I) lam + chainW3 (chainBtoY αs I) lam) = 0 := by
    rw [chainStep3Cleared_eq' hden2', h3zero, mul_zero]
  have hmu : PConstructible mu :=
    root_Pconstructible_le_six_coeffs hg3ne hdeg3 hcoeff3
      (by rw [heval3 mu, hcl mu, hclmu])
  -- step 4: the quintic
  have hD : ∀ k, PConstructible (ChainB.D αs I lam mu k) := by
    intro k
    rw [ChainB.D, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact PConstructible.add (PConstructible.mul hmu (hW1 k)) (hW3 k)
  have hBdotDD : PConstructible (yBdot αs (ChainB.P I lam) (ChainB.D αs I lam mu)
      (ChainB.D αs I lam mu)) :=
    yBdot_Pconstructible hmon hn hnat hsep hcoef hαs hnd hP hD hD
  have hBdotQD : PConstructible (yBdot αs (ChainB.P I lam) (ChainB.Q0 αs I lam x)
      (ChainB.D αs I lam mu)) :=
    yBdot_Pconstructible hmon hn hnat hsep hcoef hαs hnd hP hQ0 hD
  have hV : ∀ k, PConstructible (ChainB.V αs I lam x mu k) := by
    intro k
    rw [ChainB.V, ChainB.conicPt, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    exact PConstructible.sub (hQ0 k)
      (PConstructible.mul
        (PConstructible.div (PConstructible.mul (nat_Pconstructible 2) hBdotQD) hBdotDD)
        (hD k))
  have hden2b : yBdot αs (ChainB.P I lam) (ChainB.D αs I lam mu)
      (ChainB.D αs I lam mu) ≠ 0 := by
    rw [yBdot_eq_yBdotY, ChainB.yvec_P, ChainB.yvec_D αs I lam mu hden1]
    simpa only [chainD, chainW1, chainW3, chainWt] using hden2'
  have hstep4 (t : ℝ) : chainStep4 (yvec αs (ChainB.P I lam))
      (yvec αs (ChainB.V αs I lam x mu)) t = chainStep4' (chainBtoY αs I) lam x mu t := by
    simp only [chainStep4', chainStep4]
    rw [ChainB.yvec_P, ChainB.yvec_V αs I lam x mu hden1 hden2b]
  obtain ⟨g4, hdeg4, hcoeff4, heval4⟩ := exists_step4_poly (P := ChainB.P I lam)
    (ChainB.V αs I lam x mu) hmon hn hnat hsep hcoef hαs hnd hP hV
  have hg4ne : g4 ≠ 0 := by
    rintro rfl
    obtain ⟨t, ht⟩ := hne4
    rw [← hstep4 t] at ht
    exact ht (by simpa using (heval4 t).symm)
  have hstep4kappa : chainStep4 (yvec αs (ChainB.P I lam))
      (yvec αs (ChainB.V αs I lam x mu)) kappa = 0 := by
    rw [hstep4 kappa]
    simpa only [chainStep4'] using hchain.2.2.2.1
  have hkappa : PConstructible kappa :=
    root_Pconstructible_le_six_coeffs hg4ne (by omega) hcoeff4
      (by rw [heval4 kappa, hstep4kappa])
  exact ⟨hlam, hx, hmu, hkappa⟩



/-- **The output `b`-vector is P-constructible.** This is the intended statement (the root

hypotheses added; `hchain` is *not* needed, only the P-constructibility of the inputs and of

the four step roots). Every entry of the chain is a `b`-linear combination of the inputs with

a symmetric-functional coefficient, so the arithmetic closes with `PConstructible.add`,
`.mul`, `.div` and the three pairing lemmas. -/
theorem chainBLift_Pconstructible_of_roots {q : ℝ[X]} {αs : Fin n → ℝ}
    {I : ChainBInputs n}
    (hmon : q.Monic) (hn : 0 < n) (hnat : q.natDegree = n) (hsep : q.Separable)
    (hcoef : ∀ k, PConstructible (q.coeff k)) (hαs : ∀ i : Fin n, q.eval (αs i) = 0)
    (hnd : Function.Injective αs)
    (hI : ∀ k, PConstructible (I.a k) ∧ PConstructible (I.b k) ∧ PConstructible (I.g k) ∧
      PConstructible (I.w1 k) ∧ PConstructible (I.w2 k) ∧ PConstructible (I.w3 k))
    (lam x mu kappa : ℝ)
    (hroots : PConstructible lam ∧ PConstructible x ∧ PConstructible mu ∧
      PConstructible kappa) :
    ∀ k, PConstructible (ChainB.out αs I lam x mu kappa k) := by
  have ha : ∀ k, PConstructible (I.a k) := fun k => (hI k).1
  have hb : ∀ k, PConstructible (I.b k) := fun k => (hI k).2.1
  have hg : ∀ k, PConstructible (I.g k) := fun k => (hI k).2.2.1
  have hw1 : ∀ k, PConstructible (I.w1 k) := fun k => (hI k).2.2.2.1
  have hw2 : ∀ k, PConstructible (I.w2 k) := fun k => (hI k).2.2.2.2.1
  have hw3 : ∀ k, PConstructible (I.w3 k) := fun k => (hI k).2.2.2.2.2
  have hP : ∀ k, PConstructible (ChainB.P I lam k) := by
    intro k
    rw [ChainB.P, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact PConstructible.add (ha k) (PConstructible.mul hroots.1 (hb k))
  have hproj (w : Fin n → ℝ) (hw : ∀ k, PConstructible (w k)) :
      ∀ k, PConstructible (ChainB.projN αs (ChainB.P I lam) I.g w k) := by
    intro k
    rw [ChainB.projN, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    exact PConstructible.sub (hw k)
      (PConstructible.mul
        (PConstructible.div
          (yNB_Pconstructible hmon hn hnat hsep hcoef hαs hnd hP hw)
          (yNB_Pconstructible hmon hn hnat hsep hcoef hαs hnd hP hg))
        (hg k))
  have hW1 : ∀ k, PConstructible (ChainB.Wt αs I lam 0 k) := by
    simpa only [ChainB.Wt] using (hproj I.w1 hw1)
  have hW2 : ∀ k, PConstructible (ChainB.Wt αs I lam 1 k) := by
    simpa only [ChainB.Wt] using (hproj I.w2 hw2)
  have hW3 : ∀ k, PConstructible (ChainB.Wt αs I lam 2 k) := by
    simpa only [ChainB.Wt] using (hproj I.w3 hw3)
  have hQ0 : ∀ k, PConstructible (ChainB.Q0 αs I lam x k) := by
    intro k
    rw [ChainB.Q0, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact PConstructible.add (hW1 k) (PConstructible.mul hroots.2.1 (hW2 k))
  have hD : ∀ k, PConstructible (ChainB.D αs I lam mu k) := by
    intro k
    rw [ChainB.D, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact PConstructible.add (PConstructible.mul hroots.2.2.1 (hW1 k)) (hW3 k)
  have hBdotDD : PConstructible (yBdot αs (ChainB.P I lam) (ChainB.D αs I lam mu)
      (ChainB.D αs I lam mu)) :=
    yBdot_Pconstructible hmon hn hnat hsep hcoef hαs hnd hP hD hD
  have hBdotQD : PConstructible (yBdot αs (ChainB.P I lam) (ChainB.Q0 αs I lam x)
      (ChainB.D αs I lam mu)) :=
    yBdot_Pconstructible hmon hn hnat hsep hcoef hαs hnd hP hQ0 hD
  have hV : ∀ k, PConstructible (ChainB.V αs I lam x mu k) := by
    intro k
    rw [ChainB.V, ChainB.conicPt, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    exact PConstructible.sub (hQ0 k)
      (PConstructible.mul
        (PConstructible.div (PConstructible.mul (nat_Pconstructible 2) hBdotQD) hBdotDD)
        (hD k))
  intro k
  rw [ChainB.out, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact PConstructible.add (hP k) (PConstructible.mul hroots.2.2.2 (hV k))

/-! #### The `b`-space density argument -/

/-- `b ↦ chainBtoY αs b` is onto: `yvec αs` is a bijection of the two vector spaces, so every

y-space input is the image of a `b`-input. This is the one place surjectivity is used: it is

what makes the open set `(chainBtoY αs) ⁻¹' U` of `b`-inputs nonempty. -/
private theorem chainBtoY_surjective {m : ℕ} {αs : Fin m → ℝ} (hnd : Function.Injective αs)
    (Y : ChainYInputs m) : ∃ I : ChainBInputs m, chainBtoY αs I = Y := by
  obtain ⟨A, B, C, D, E, F⟩ := Y
  obtain ⟨b₁, h₁⟩ : ∃ b : Fin m → ℝ, yvec αs b = A := yvecL_surjective hnd A
  obtain ⟨b₂, h₂⟩ : ∃ b : Fin m → ℝ, yvec αs b = B := yvecL_surjective hnd B
  obtain ⟨b₃, h₃⟩ : ∃ b : Fin m → ℝ, yvec αs b = C := yvecL_surjective hnd C
  obtain ⟨b₄, h₄⟩ : ∃ b : Fin m → ℝ, yvec αs b = D := yvecL_surjective hnd D
  obtain ⟨b₅, h₅⟩ : ∃ b : Fin m → ℝ, yvec αs b = E := yvecL_surjective hnd E
  obtain ⟨b₆, h₆⟩ : ∃ b : Fin m → ℝ, yvec αs b = F := yvecL_surjective hnd F
  refine ⟨(b₁, (b₂, (b₃, (b₄, (b₅, b₆))))), ?_⟩
  unfold chainBtoY
  simp only [Prod.mk.injEq]
  simp [h₁, h₂, h₃, h₄, h₅, h₆]

/-- `b ↦ yvec αs b` is continuous: each entry is a finite sum of products of continuous functions,
and a map into a `Pi` type is continuous when all of its entries are. -/
private theorem continuous_yvec {m : ℕ} (αs : Fin m → ℝ) :
    Continuous fun b : Fin m → ℝ => yvec αs b := by
  refine continuous_pi fun i => ?_
  simp only [yvec]
  exact continuous_finsetSum _ fun k _ => (continuous_apply k).mul continuous_const

/-- `I ↦ chainBtoY αs I` is continuous: it is the six-fold product of the continuous map
`b ↦ yvec αs b` with the coordinate projections. -/
private theorem continuous_chainBtoY {m : ℕ} (αs : Fin m → ℝ) :
    Continuous (chainBtoY (n := m) αs) := by
  have hyv : Continuous fun b : Fin m → ℝ => yvec αs b := continuous_yvec αs
  unfold chainBtoY
  exact (hyv.comp continuous_fst).prodMk
    ((hyv.comp continuous_snd.fst).prodMk
      ((hyv.comp continuous_snd.snd.fst).prodMk
        ((hyv.comp continuous_snd.snd.snd.fst).prodMk
          ((hyv.comp continuous_snd.snd.snd.snd.fst).prodMk
            (hyv.comp continuous_snd.snd.snd.snd.snd)))))

/-- **Density, for an arbitrary continuous map into y-space.** The six-step argument of
the P-constructible `b`-input density proof, with `chainBtoY αs` replaced by an arbitrary
continuous `G`.
Fixing five slots and varying the sixth is a continuous map (a `G`-preimage of a slice), so
each slice of the open set is open and nonempty, and density of rational vectors fills it
with a P-constructible slot. -/
private theorem exists_PC_tuple_mem {m : ℕ} {G : ChainYInputs m → ChainYInputs m}
    {U : Set (ChainYInputs m)} (hG : Continuous G) (hU : IsOpen U)
    (hne : ∃ I : ChainYInputs m, G I ∈ U) :
    ∃ I : ChainYInputs m,
      (∀ k, PConstructible (I.a k)) ∧ (∀ k, PConstructible (I.b k)) ∧
      (∀ k, PConstructible (I.g k)) ∧ (∀ k, PConstructible (I.w1 k)) ∧
      (∀ k, PConstructible (I.w2 k)) ∧ (∀ k, PConstructible (I.w3 k)) ∧ G I ∈ U := by
  obtain ⟨I₀, hI₀⟩ := hne
  obtain ⟨B₁, B₂, B₃, B₄, B₅, B₆⟩ := I₀
  have hmem : G (B₁, (B₂, (B₃, (B₄, (B₅, B₆))))) ∈ U := hI₀
  have g₁ : Continuous fun v : Fin m → ℝ => G (v, (B₂, (B₃, (B₄, (B₅, B₆))))) :=
    hG.comp (continuous_id.prodMk (continuous_const.prodMk (continuous_const.prodMk
      (continuous_const.prodMk (continuous_const.prodMk continuous_const)))))
  obtain ⟨b₁, hb₁, hd₁⟩ :=
    exists_Pconstructible_mem_isOpen (hU.preimage g₁) ⟨B₁, Set.mem_preimage.mpr hmem⟩
  have h₁ : G (b₁, (B₂, (B₃, (B₄, (B₅, B₆))))) ∈ U := Set.mem_preimage.mp hd₁
  have g₂ : Continuous fun v : Fin m → ℝ => G (b₁, (v, (B₃, (B₄, (B₅, B₆))))) :=
    hG.comp (continuous_const.prodMk (continuous_id.prodMk (continuous_const.prodMk
      (continuous_const.prodMk (continuous_const.prodMk continuous_const)))))
  obtain ⟨b₂, hb₂, hd₂⟩ :=
    exists_Pconstructible_mem_isOpen (hU.preimage g₂) ⟨B₂, Set.mem_preimage.mpr h₁⟩
  have h₂ : G (b₁, (b₂, (B₃, (B₄, (B₅, B₆))))) ∈ U := Set.mem_preimage.mp hd₂
  have g₃ : Continuous fun v : Fin m → ℝ => G (b₁, (b₂, (v, (B₄, (B₅, B₆))))) :=
    hG.comp (continuous_const.prodMk (continuous_const.prodMk (continuous_id.prodMk
      (continuous_const.prodMk (continuous_const.prodMk continuous_const)))))
  obtain ⟨b₃, hb₃, hd₃⟩ :=
    exists_Pconstructible_mem_isOpen (hU.preimage g₃) ⟨B₃, Set.mem_preimage.mpr h₂⟩
  have h₃ : G (b₁, (b₂, (b₃, (B₄, (B₅, B₆))))) ∈ U := Set.mem_preimage.mp hd₃
  have g₄ : Continuous fun v : Fin m → ℝ => G (b₁, (b₂, (b₃, (v, (B₅, B₆))))) :=
    hG.comp (continuous_const.prodMk (continuous_const.prodMk (continuous_const.prodMk
      (continuous_id.prodMk (continuous_const.prodMk continuous_const)))))
  obtain ⟨b₄, hb₄, hd₄⟩ :=
    exists_Pconstructible_mem_isOpen (hU.preimage g₄) ⟨B₄, Set.mem_preimage.mpr h₃⟩
  have h₄ : G (b₁, (b₂, (b₃, (b₄, (B₅, B₆))))) ∈ U := Set.mem_preimage.mp hd₄
  have g₅ : Continuous fun v : Fin m → ℝ => G (b₁, (b₂, (b₃, (b₄, (v, B₆))))) :=
    hG.comp (continuous_const.prodMk (continuous_const.prodMk (continuous_const.prodMk
      (continuous_const.prodMk (continuous_id.prodMk continuous_const)))))
  obtain ⟨b₅, hb₅, hd₅⟩ :=
    exists_Pconstructible_mem_isOpen (hU.preimage g₅) ⟨B₅, Set.mem_preimage.mpr h₄⟩
  have h₅ : G (b₁, (b₂, (b₃, (b₄, (b₅, B₆))))) ∈ U := Set.mem_preimage.mp hd₅
  have g₆ : Continuous fun v : Fin m → ℝ => G (b₁, (b₂, (b₃, (b₄, (b₅, v))))) :=
    hG.comp (continuous_const.prodMk (continuous_const.prodMk (continuous_const.prodMk
      (continuous_const.prodMk (continuous_const.prodMk continuous_id)))))
  obtain ⟨b₆, hb₆, hd₆⟩ :=
    exists_Pconstructible_mem_isOpen (hU.preimage g₆) ⟨B₆, Set.mem_preimage.mpr h₅⟩
  exact ⟨(b₁, (b₂, (b₃, (b₄, (b₅, b₆))))), fun k => hb₁ k, fun k => hb₂ k, fun k => hb₃ k,
    fun k => hb₄ k, fun k => hb₅ k, fun k => hb₆ k, Set.mem_preimage.mp hd₆⟩

/-! ### The trace correction onto `V = {S₁ = 0}` -/

/-- Subtract `S₁(y(b))/m` from the `0`-th coordinate of `b`. This is the per-slot correction of
`YSpace.exists_b_Pconstructible_near`, packaged on its own; by construction the corrected
`y`-vector lies in `V = {S₁ = 0}`. -/
def correctSlot {m : ℕ} (αs : Fin m → ℝ) (hm : 0 < m) (b : Fin m → ℝ) : Fin m → ℝ :=
  bcorrect b ⟨0, hm⟩ (psumY (yvec αs b) 1 / m)

/-- Apply `correctSlot` to all six slots of a `b`-input. -/
def correctAll {m : ℕ} (αs : Fin m → ℝ) (hm : 0 < m) (I : ChainBInputs m) : ChainBInputs m :=
  (correctSlot αs hm I.1, correctSlot αs hm I.2.1, correctSlot αs hm I.2.2.1,
    correctSlot αs hm I.2.2.2.1, correctSlot αs hm I.2.2.2.2.1, correctSlot αs hm I.2.2.2.2.2)

/-- `chainBtoY αs` after the trace correction on every slot. Its image is exactly the set of
y-space inputs all six of whose slots have vanishing first power sum. -/
def correctPhi {m : ℕ} (αs : Fin m → ℝ) (hm : 0 < m) : ChainBInputs m → ChainYInputs m :=
  fun I => chainBtoY αs (correctAll αs hm I)

private theorem continuous_correctSlot {m : ℕ} {αs : Fin m → ℝ} (hm : 0 < m) :
    Continuous (correctSlot αs hm) := by
  have hyv : ∀ i : Fin m, Continuous fun b : Fin m → ℝ => yvec αs b i := by
    intro i
    simp only [yvec]
    exact continuous_finsetSum _ fun k _ => (continuous_apply k).mul continuous_const
  have hpc : Continuous fun b : Fin m → ℝ => psumY (yvec αs b) 1 := by
    simp only [psumY, psumFinY]
    refine continuous_finsetSum _ fun i _ => ?_
    simpa using (hyv i).pow 1
  have hc : Continuous fun b : Fin m → ℝ => psumY (yvec αs b) 1 / m := hpc.div_const _
  unfold correctSlot
  refine continuous_pi fun k => ?_
  by_cases hk : k = (⟨0, hm⟩ : Fin m)
  · have heq : (fun b : Fin m → ℝ => bcorrect b ⟨0, hm⟩ (psumY (yvec αs b) 1 / m) k)
        = fun b : Fin m → ℝ => b k - psumY (yvec αs b) 1 / m := by
      funext b
      simp only [bcorrect, hk, if_true]
    rw [heq]
    exact (continuous_apply k).sub hc
  · have heq : (fun b : Fin m → ℝ => bcorrect b ⟨0, hm⟩ (psumY (yvec αs b) 1 / m) k)
        = fun b : Fin m → ℝ => b k := by
      funext b
      simp only [bcorrect, hk, if_false, sub_zero]
    rw [heq]
    exact continuous_apply k

private theorem continuous_correctAll {m : ℕ} {αs : Fin m → ℝ} (hm : 0 < m) :
    Continuous (correctAll αs hm) := by
  have hcs : Continuous (correctSlot αs hm) := continuous_correctSlot hm
  unfold correctAll
  exact (hcs.comp continuous_fst).prodMk
    ((hcs.comp continuous_snd.fst).prodMk
      ((hcs.comp continuous_snd.snd.fst).prodMk
        ((hcs.comp continuous_snd.snd.snd.fst).prodMk
          ((hcs.comp continuous_snd.snd.snd.snd.fst).prodMk
            (hcs.comp continuous_snd.snd.snd.snd.snd)))))

private theorem continuous_correctPhi {m : ℕ} {αs : Fin m → ℝ} (hm : 0 < m) :
    Continuous (correctPhi αs hm) :=
  (continuous_chainBtoY αs).comp (continuous_correctAll hm)

private theorem psumY_yvec_correctSlot {m : ℕ} {αs : Fin m → ℝ} (hm : 0 < m)
    (b : Fin m → ℝ) : psumY (yvec αs (correctSlot αs hm b)) 1 = 0 := by
  have h1 : yvec αs (correctSlot αs hm b)
      = fun i => yvec αs b i - psumY (yvec αs b) 1 / m := by
    funext i
    unfold correctSlot
    rw [yvec_correct]
    simp
  rw [h1]
  simp only [psumY, psumFinY, pow_one, Finset.sum_sub_distrib]
  have h2 : (∑ i : Fin m, (∑ x, yvec αs b x) / (m : ℝ)) = ∑ x, yvec αs b x := by
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
    field_simp
  rw [h2]
  ring

private theorem correctSlot_eq_self {m : ℕ} {αs : Fin m → ℝ} {hm : 0 < m} {b : Fin m → ℝ}
    (h : psumY (yvec αs b) 1 = 0) : correctSlot αs hm b = b := by
  funext k
  unfold correctSlot bcorrect
  rw [h]
  simp

private theorem correctSlot_Pconstructible {m : ℕ} {q : ℝ[X]} {αs : Fin m → ℝ}
    {b : Fin m → ℝ} (hm : 0 < m) (hmon : q.Monic) (hnat : q.natDegree = m)
    (hsep : q.Separable) (hcoef : ∀ k, PConstructible (q.coeff k))
    (hαs : ∀ i : Fin m, q.eval (αs i) = 0) (hnd : Function.Injective αs)
    (hb : ∀ k, PConstructible (b k)) : ∀ k, PConstructible (correctSlot αs hm b k) := by
  intro k
  have hpc : PConstructible (psumY (yvec αs b) 1) :=
    psum_yvec_Pconstructible hmon hm hnat hsep hcoef hαs hnd hb 1
  by_cases hk : k = (⟨0, hm⟩ : Fin m)
  · unfold correctSlot bcorrect
    rw [if_pos hk]
    exact PConstructible.sub (hb k) (PConstructible.div hpc (nat_Pconstructible m))
  · unfold correctSlot bcorrect
    rw [if_neg hk]
    simp only [sub_zero]
    exact hb k

/-- **PLAN-addendum §2.3 / §3 item E.** Every nonempty open set of y-space inputs meeting
`V⁶ = {all six slots have S₁ = 0}` contains the `chainBtoY`-image of a P-constructible
`b`-input whose six y-slots lie in `V`. The trace correction `correctAll` retracts onto the
preimage of `V⁶`, so running the six-step density argument for the composite
`correctPhi = chainBtoY ∘ correctAll` and correcting the result yields both P-constructible
entries and the six linear conditions. -/
theorem exists_PC_inputs_s1 {m : ℕ} {q : ℝ[X]} {αs : Fin m → ℝ} {U : Set (ChainYInputs m)}
    (hm : 0 < m) (hU : IsOpen U)
    (hne : (U ∩ {Y : ChainYInputs m | psumY Y.a 1 = 0 ∧ psumY Y.b 1 = 0 ∧ psumY Y.g 1 = 0 ∧
        psumY Y.w1 1 = 0 ∧ psumY Y.w2 1 = 0 ∧ psumY Y.w3 1 = 0}).Nonempty)
    (hmon : q.Monic) (hnat : q.natDegree = m) (hsep : q.Separable)
    (hcoef : ∀ k, PConstructible (q.coeff k)) (hαs : ∀ i : Fin m, q.eval (αs i) = 0)
    (hnd : Function.Injective αs) :
    ∃ I : ChainBInputs m, (∀ k, PConstructible (I.a k)) ∧ (∀ k, PConstructible (I.b k)) ∧
      (∀ k, PConstructible (I.g k)) ∧ (∀ k, PConstructible (I.w1 k)) ∧
      (∀ k, PConstructible (I.w2 k)) ∧ (∀ k, PConstructible (I.w3 k)) ∧
      chainBtoY αs I ∈ U ∧ psumY (yvec αs I.a) 1 = 0 ∧ psumY (yvec αs I.b) 1 = 0 ∧
      psumY (yvec αs I.g) 1 = 0 ∧ psumY (yvec αs I.w1) 1 = 0 ∧
      psumY (yvec αs I.w2) 1 = 0 ∧ psumY (yvec αs I.w3) 1 = 0 := by
  have hneG : ∃ I : ChainYInputs m, correctPhi αs hm I ∈ U := by
    obtain ⟨Y, hYU, hYV⟩ := hne
    obtain ⟨hYa, hYb, hYg, hYw1, hYw2, hYw3⟩ := hYV
    obtain ⟨I, hI⟩ := chainBtoY_surjective hnd Y
    refine ⟨I, ?_⟩
    have e1 : yvec αs I.1 = Y.a := by
      simpa [chainBtoY, ChainYInputs.a] using congrArg (fun Z : ChainYInputs m => Z.1) hI
    have e2 : yvec αs I.2.1 = Y.b := by
      simpa [chainBtoY, ChainYInputs.b] using congrArg (fun Z : ChainYInputs m => Z.2.1) hI
    have e3 : yvec αs I.2.2.1 = Y.g := by
      simpa [chainBtoY, ChainYInputs.g] using congrArg (fun Z : ChainYInputs m => Z.2.2.1) hI
    have e4 : yvec αs I.2.2.2.1 = Y.w1 := by
      simpa [chainBtoY, ChainYInputs.w1] using
        congrArg (fun Z : ChainYInputs m => Z.2.2.2.1) hI
    have e5 : yvec αs I.2.2.2.2.1 = Y.w2 := by
      simpa [chainBtoY, ChainYInputs.w2] using
        congrArg (fun Z : ChainYInputs m => Z.2.2.2.2.1) hI
    have e6 : yvec αs I.2.2.2.2.2 = Y.w3 := by
      simpa [chainBtoY, ChainYInputs.w3] using
        congrArg (fun Z : ChainYInputs m => Z.2.2.2.2.2) hI
    have h1 : psumY (yvec αs I.1) 1 = 0 := by rw [e1]; exact hYa
    have h2 : psumY (yvec αs I.2.1) 1 = 0 := by rw [e2]; exact hYb
    have h3 : psumY (yvec αs I.2.2.1) 1 = 0 := by rw [e3]; exact hYg
    have h4 : psumY (yvec αs I.2.2.2.1) 1 = 0 := by rw [e4]; exact hYw1
    have h5 : psumY (yvec αs I.2.2.2.2.1) 1 = 0 := by rw [e5]; exact hYw2
    have h6 : psumY (yvec αs I.2.2.2.2.2) 1 = 0 := by rw [e6]; exact hYw3
    have hfix : correctAll αs hm I = I := by
      unfold correctAll
      rw [correctSlot_eq_self (hm := hm) h1, correctSlot_eq_self (hm := hm) h2,
        correctSlot_eq_self (hm := hm) h3, correctSlot_eq_self (hm := hm) h4,
        correctSlot_eq_self (hm := hm) h5, correctSlot_eq_self (hm := hm) h6]
    unfold correctPhi
    rw [hfix, hI]
    exact hYU
  obtain ⟨I, hIa, hIb, hIg, hIw1, hIw2, hIw3, hIU⟩ :=
    exists_PC_tuple_mem (continuous_correctPhi hm) hU hneG
  refine ⟨correctAll αs hm I, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k; exact correctSlot_Pconstructible hm hmon hnat hsep hcoef hαs hnd hIa k
  · intro k; exact correctSlot_Pconstructible hm hmon hnat hsep hcoef hαs hnd hIb k
  · intro k; exact correctSlot_Pconstructible hm hmon hnat hsep hcoef hαs hnd hIg k
  · intro k; exact correctSlot_Pconstructible hm hmon hnat hsep hcoef hαs hnd hIw1 k
  · intro k; exact correctSlot_Pconstructible hm hmon hnat hsep hcoef hαs hnd hIw2 k
  · intro k; exact correctSlot_Pconstructible hm hmon hnat hsep hcoef hαs hnd hIw3 k
  · exact hIU
  · exact psumY_yvec_correctSlot hm I.1
  · exact psumY_yvec_correctSlot hm I.2.1
  · exact psumY_yvec_correctSlot hm I.2.2.1
  · exact psumY_yvec_correctSlot hm I.2.2.2.1
  · exact psumY_yvec_correctSlot hm I.2.2.2.2.1
  · exact psumY_yvec_correctSlot hm I.2.2.2.2.2

/-- **The assembly, given an open set of good y-space inputs carrying the four nonzero-step
witnesses.** `exists_PC_inputs_s1` puts a `b`-input `I` with P-constructible entries inside the
good open set `U` and with all six y-slots in `V = {S₁ = 0}`; the four nonzero-step witnesses
then make the step roots `lam x mu kappa` P-constructible via `stepRoots_Pconstructible`, and
`chainBLift_Pconstructible_of_roots` lifts them to the output `b`-vector. `chainBLift_yvec`
identifies that output's y-vector with the chain output, so `ChainGood` together with the input
`S₁ = 0` transfers `Function.Injective` and `S₁ = S₃ = S₅ = 0` to it.

`hgood` is exactly the conclusion of `exists_open_good7`/`exists_open_good8`. -/
private theorem exists_b_good_of_PC_roots {q : ℝ[X]} {αs : Fin n → ℝ} {U : Set (ChainYInputs n)}
    (hU : IsOpen U)
    (hneU : (U ∩ {Y : ChainYInputs n | psumY Y.a 1 = 0 ∧ psumY Y.b 1 = 0 ∧
      psumY Y.g 1 = 0 ∧ psumY Y.w1 1 = 0 ∧ psumY Y.w2 1 = 0 ∧ psumY Y.w3 1 = 0}).Nonempty)
    (hgood : ∀ Y ∈ U, ∃ lam x mu kappa : ℝ, ChainGood Y lam x mu kappa ∧
      (∃ t : ℝ, chainStep1' Y t ≠ 0) ∧
      (∃ t : ℝ, chainStep2' Y lam t ≠ 0) ∧
      (∃ t : ℝ, chainStep3Cleared (chainP Y lam) (chainQ0 Y lam x)
          (t • chainW1 Y lam + chainW3 Y lam) ≠ 0) ∧
      (∃ t : ℝ, chainStep4' Y lam x mu t ≠ 0))
    (hmon : q.Monic) (hpos : 0 < n) (hnat : q.natDegree = n) (hsep : q.Separable)
    (hcoeff : ∀ k, PConstructible (q.coeff k)) (hαs : ∀ i : Fin n, q.eval (αs i) = 0)
    (hnd : Function.Injective αs) :
    ∃ b : Fin n → ℝ, (∀ k, PConstructible (b k)) ∧ Function.Injective (yvec αs b) ∧
      psumY (yvec αs b) 1 = 0 ∧ psumY (yvec αs b) 3 = 0 ∧ psumY (yvec αs b) 5 = 0 := by
  obtain ⟨I, hIa, hIb, hIg, hIw1, hIw2, hIw3, hIU, hVa, hVb, hVg, hVw1, hVw2, hVw3⟩ :=
    exists_PC_inputs_s1 hpos hU hneU hmon hnat hsep hcoeff hαs hnd
  obtain ⟨lam, x, mu, kappa, hchain, hne1, hne2, hne3, hne4⟩ := hgood (chainBtoY αs I) hIU
  have hI6 : ∀ k, PConstructible (I.a k) ∧ PConstructible (I.b k) ∧ PConstructible (I.g k) ∧
      PConstructible (I.w1 k) ∧ PConstructible (I.w2 k) ∧ PConstructible (I.w3 k) :=
    fun k => ⟨hIa k, hIb k, hIg k, hIw1 k, hIw2 k, hIw3 k⟩
  have hroots : PConstructible lam ∧ PConstructible x ∧ PConstructible mu ∧
      PConstructible kappa :=
    stepRoots_Pconstructible hmon hpos hnat hsep hcoeff hαs hnd hI6 lam x mu kappa hchain
      hne1 hne2 hne3 hne4
  have hpcout : ∀ k, PConstructible (ChainB.out αs I lam x mu kappa k) :=
    chainBLift_Pconstructible_of_roots hmon hpos hnat hsep hcoeff hαs hnd hI6 lam x mu kappa
      hroots
  have hden1 : yNB αs (ChainB.P I lam) I.g ≠ 0 := by
    rw [yNB_eq_yNBY, ChainB.yvec_P αs I lam]
    exact hchain.2.2.2.2.1
  have hden2 : yBdot αs (ChainB.P I lam) (ChainB.D αs I lam mu) (ChainB.D αs I lam mu) ≠ 0 := by
    rw [yBdot_eq_yBdotY, ChainB.yvec_P αs I lam, ChainB.yvec_D αs I lam mu hden1]
    exact hchain.2.2.2.2.2.1
  have key : yvec αs (ChainB.out αs I lam x mu kappa) = chainY (chainBtoY αs I) lam x mu kappa :=
    chainBLift_yvec αs I lam x mu kappa hden1 hden2
  refine ⟨ChainB.out αs I lam x mu kappa, hpcout, ?_, ?_, ?_, ?_⟩
  · rw [key]
    exact hchain.2.2.2.2.2.2
  · rw [key]
    exact chainY_psumY_one_eq (I := chainBtoY αs I) hVa hVb hVg hVw1 hVw2 hVw3
  · rw [key]
    exact chainY_psumY_cube_eq hchain.1 hchain.2.1 hchain.2.2.1 hchain.2.2.2.2.1
      hchain.2.2.2.2.2.1
  · rw [key, ← chainStep4'_psumY_eq]
    exact hchain.2.2.2.1

/-! ### The odd Tschirnhaus lemma -/



/-- **The odd Tschirnhaus lemma.** For `n ∈ {7, 8}` and `q` monic of degree `n` with
P-constructible coefficients and pairwise distinct real roots, there is a P-constructible
`b`-vector whose y-vector has vanishing `S₁, S₃, S₅` and pairwise distinct entries.

**Route.** `exists_open_good7` / `exists_open_good8` give an open set `U` of good y-space
inputs containing the rational centre `centre7`/`centre8`, in which every member has a good
chain together with the four nonzero-step witnesses. The centre lies in `V = {all six slots
have S₁ = 0}` by `centre7_s1`/`centre8_s1`, so `U ∩ V` is nonempty; `exists_PC_inputs_s1`
then produces a `b`-input with P-constructible entries, with all six y-slots in `V`, and with
`chainBtoY αs I ∈ U`. `exists_b_good_of_PC_roots` closes the remaining steps: the nonzero-step
witnesses make the four step roots P-constructible, `chainBLift_Pconstructible_of_roots` lifts
them to a P-constructible output `b`-vector, `chainBLift_yvec` identifies its y-vector with the
chain output, and `ChainGood` plus `S₁ = 0` gives `Function.Injective` and `S₁ = S₃ = S₅ = 0`. -/
theorem exists_oddTschirnhaus (hn : n = 7 ∨ n = 8) {q : ℝ[X]} (hmon : q.Monic)
    (hnat : q.natDegree = n) (hsep : q.Separable)
    (hcoeff : ∀ k, PConstructible (q.coeff k)) {αs : Fin n → ℝ}
    (hαs : ∀ i : Fin n, q.eval (αs i) = 0) (hnd : Function.Injective αs) :
    ∃ b : Fin n → ℝ, (∀ k, PConstructible (b k)) ∧
      Function.Injective (yvec αs b) ∧ psumY (yvec αs b) 1 = 0 ∧
      psumY (yvec αs b) 3 = 0 ∧ psumY (yvec αs b) 5 = 0 := by
  rcases hn with h7 | h8
  · subst h7
    obtain ⟨U, hU, hc, hgood⟩ := exists_open_good7
    exact exists_b_good_of_PC_roots hU ⟨centre7, hc, centre7_s1⟩ hgood hmon (by norm_num)
      hnat hsep hcoeff hαs hnd
  · subst h8
    obtain ⟨U, hU, hc, hgood⟩ := exists_open_good8
    exact exists_b_good_of_PC_roots hU ⟨centre8, hc, centre8_s1⟩ hgood hmon (by norm_num)
      hnat hsep hcoeff hαs hnd

end



end Pconstructible
