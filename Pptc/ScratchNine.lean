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

-- Targeted import rather than `import Mathlib`; `Pptc.Basic` already carries the polynomial
-- and tactic machinery this engine needs.
import Pptc.Basic

open Polynomial

namespace Pconstructible

noncomputable section

/-! ### The degree-9 crossing engine

The sextic engine of `root_Pconstructible_le_six_coeffs` crosses a cubic Bézier
`Γ t = (a t, b t)` with the sideways parabola `x = -y² - a₃y`, whose implicit equation `F`
has degree `2`; `F (Γ t)` therefore has degree `2 · 3 = 6`. Swapping the parabola for a
genuine cubic graph `Δ s = (c s, s)`, with implicit equation `F (A, B) = A - c B`, raises the
Bézout number to `3 · 3 = 9`: both curves are cubic parametrizations, so they cross in at most
nine points. The crossing isolates `y₀ = b β`, and `β` is then recovered as a root of the cubic
`b t - y₀` via `cubicVal_root_Pconstructible`, which is why `b` must be genuinely cubic.

There is one nondegeneracy that the sextic case gets for free from the *monic* normal form
`sexticVal` and which the general cubic relation does not: the crossing polynomial
`p t = a t - c (b t)` may be identically zero. When it is, `Γ` lies inside `Δ` and `hroot`
is satisfied by *every* real `β`, so no conclusion is available — for instance `a = b = t³`
and `c = s` make `a β = c (b β)` for all `β`. Requiring `c` to be genuinely cubic (`c₃ ≠ 0`)
along with `b₃ ≠ 0` makes `p` have leading coefficient `-c₃ b₃³ ≠ 0`, hence degree `9`, which
is exactly the degree-9 situation the engine is meant to cover. -/

-- Theorem: the cubic with coefficients `(0, 1, 0, 0)` is the identity function.
theorem cubicVal_identity (x : ℝ) : cubicVal 0 1 0 0 x = x := by
  simp [cubicVal]

-- Theorem: if `a`, `b`, `c` are cubics with P-constructible coefficients, `b` and `c` are
-- genuinely cubic, and `β` satisfies `a β = c (b β)`, then `β` is P-constructible. The
-- parametric curve `Γ t = (a t, b t)` is crossed with the cubic graph `Δ s = (c s, s)`, and
-- the ordinate `y₀ = b β` of the crossing recovers `β` through the cubic `b t - y₀`.
--
-- `c₃ ≠ 0` is not decorative: without it the crossing polynomial can vanish identically and
-- the statement is false (see the section comment).
theorem cubicGraph_cubic_cross_root_Pconstructible
    {a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₀ c₁ c₂ c₃ β : ℝ}
    (ha : ∀ k, PConstructible (match k with
      | 0 => a₀ | 1 => a₁ | 2 => a₂ | _ => a₃))
    (hb : ∀ k, PConstructible (match k with
      | 0 => b₀ | 1 => b₁ | 2 => b₂ | _ => b₃))
    (hc : ∀ k, PConstructible (match k with
      | 0 => c₀ | 1 => c₁ | 2 => c₂ | _ => c₃))
    (hb₃ : b₃ ≠ 0) (hc₃ : c₃ ≠ 0)
    (hroot : cubicVal a₀ a₁ a₂ a₃ β =
      cubicVal c₀ c₁ c₂ c₃ (cubicVal b₀ b₁ b₂ b₃ β)) :
    PConstructible β := by
  have hone : PConstructible (1 : ℝ) := PConstructible.base_one
  have hzero : PConstructible (0 : ℝ) := zero_Pconstructible
  have ha₀ : PConstructible a₀ := ha 0
  have ha₁ : PConstructible a₁ := ha 1
  have ha₂ : PConstructible a₂ := ha 2
  have ha₃ : PConstructible a₃ := ha 3
  have hb₀ : PConstructible b₀ := hb 0
  have hb₁ : PConstructible b₁ := hb 1
  have hb₂ : PConstructible b₂ := hb 2
  have hb₃P : PConstructible b₃ := hb 3
  have hc₀ : PConstructible c₀ := hc 0
  have hc₁ : PConstructible c₁ := hc 1
  have hc₂ : PConstructible c₂ := hc 2
  have hc₃P : PConstructible c₃ := hc 3
  -- `Γ` traces the cubic pair `(a t, b t)`; `Δ` traces the cubic graph `(c s, s)`, whose
  -- parameter is its own ordinate, and `F (A, B) = A - c B` is its implicit equation.
  set Γ : ℝ → ℝ × ℝ := cubicPairParam a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ with hΓdef
  set Δ : ℝ → ℝ × ℝ := cubicPairParam c₀ c₁ c₂ c₃ 0 1 0 0 with hΔdef
  set y₀ : ℝ := cubicVal b₀ b₁ b₂ b₃ β with hy₀def
  have hΔ : ∀ s : ℝ, Δ s = (cubicVal c₀ c₁ c₂ c₃ s, s) := by
    intro s
    simp only [hΔdef, cubicPairParam, cubicVal_identity]
  -- `β` being a root is exactly the statement that `Γ β` lands on `Δ` at the parameter
  -- `y₀ = b β`.
  have hΓβ : Γ β = Δ y₀ := by
    rw [hΓdef, hΔ y₀, hy₀def]
    simp only [cubicPairParam, Prod.mk.injEq]
    exact ⟨hroot, trivial⟩
  -- The crossing polynomial `p t = a t - c (b t)` has degree at most `9`; because `c₃ ≠ 0`
  -- and `b₃ ≠ 0` its degree-9 coefficient is `-c₃ b₃³ ≠ 0`, so it has finitely many roots.
  set p : ℝ → ℝ := fun t =>
    cubicVal a₀ a₁ a₂ a₃ t - cubicVal c₀ c₁ c₂ c₃ (cubicVal b₀ b₁ b₂ b₃ t) with hpdef
  set Ap : Polynomial ℝ := C a₃ * X ^ 3 + C a₂ * X ^ 2 + C a₁ * X + C a₀ with hApdef
  set Bp : Polynomial ℝ := C b₃ * X ^ 3 + C b₂ * X ^ 2 + C b₁ * X + C b₀ with hBpdef
  set Cp : Polynomial ℝ := C c₃ * X ^ 3 + C c₂ * X ^ 2 + C c₁ * X + C c₀ with hCpdef
  set P : Polynomial ℝ := Ap - Cp.comp Bp with hPdef
  have hPeval : ∀ t : ℝ, P.eval t = p t := by
    intro t
    simp only [hPdef, hApdef, hBpdef, hCpdef, hpdef, cubicVal, eval_add, eval_sub, eval_mul,
      eval_pow, eval_C, eval_X, eval_comp]
  have hPne : P ≠ 0 := by
    intro hP0
    have hBdeg : Bp.natDegree = 3 := by rw [hBpdef]; compute_degree!
    have hCdeg : Cp.natDegree = 3 := by rw [hCpdef]; compute_degree!
    have hcomp : (Cp.comp Bp).natDegree = 9 := by
      rw [Polynomial.natDegree_comp, hCdeg, hBdeg]
    have hAdeg : Ap.natDegree ≤ 3 := by rw [hApdef]; compute_degree
    have h1 : Ap = Cp.comp Bp := by
      rw [hPdef] at hP0
      exact sub_eq_zero.mp hP0
    rw [h1, hcomp] at hAdeg
    omega
  have hfin : {t : ℝ | p t = 0}.Finite :=
    (Polynomial.finite_setOfPred_isRoot hPne).subset
      (fun t ht => by change P.eval t = 0; rw [hPeval]; exact ht)
  -- Rational parameter windows around `β` and `y₀`, giving the two arcs to cross.
  obtain ⟨u, -, hu2⟩ := exists_rat_btwn (show β - 1 < β by linarith)
  obtain ⟨v, hv1, -⟩ := exists_rat_btwn (show β < β + 1 by linarith)
  obtain ⟨w, -, hw2⟩ := exists_rat_btwn (show y₀ - 1 < y₀ by linarith)
  obtain ⟨z, hz1, -⟩ := exists_rat_btwn (show y₀ < y₀ + 1 by linarith)
  have hS := cubicPairArc_PConstructibleCurve ha₀ ha₁ ha₂ ha₃ hb₀ hb₁ hb₂ hb₃P
    (rat_Pconstructible u) (rat_Pconstructible v) (by linarith : ((u : ℝ)) < (v : ℝ))
  have hT := cubicPairArc_PConstructibleCurve hc₀ hc₁ hc₂ hc₃P hzero hone hzero hzero
    (rat_Pconstructible w) (rat_Pconstructible z) (by linarith : ((w : ℝ)) < (z : ℝ))
  rw [← hΓdef] at hS
  rw [← hΔdef] at hT
  have hTzero : ∀ q ∈ Δ '' Set.Icc (w : ℝ) (z : ℝ),
      q.1 - cubicVal c₀ c₁ c₂ c₃ q.2 = 0 := by
    rintro q ⟨s, -, rfl⟩
    rw [hΔ s]
    simp
  have hcross := crossing_Pconstructible hS hT
    (Γ := Γ) (F := fun A B => A - cubicVal c₀ c₁ c₂ c₃ B) (p := p) (β := β)
    (Set.image_subset_range Γ _) hTzero
    (fun t => by simp only [hpdef, hΓdef, cubicPairParam])
    hfin ⟨β, ⟨hu2.le, hv1.le⟩, rfl⟩ ⟨y₀, ⟨hw2.le, hz1.le⟩, hΓβ.symm⟩
  -- The ordinate of the crossing is `b β`, and `β` is a root of the cubic `b t - b β`.
  have hy₀_eq : (Γ β).2 = y₀ := by
    rw [hΓdef, hy₀def]
    rfl
  have hy₀P : PConstructible y₀ := hy₀_eq ▸ hcross.2
  refine cubicVal_root_Pconstructible (PConstructible.sub hb₀ hy₀P) hb₁ hb₂ hb₃P
    (Or.inl hb₃) ?_
  rw [cubicVal, hy₀def, cubicVal]
  ring

end

end Pconstructible
