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

import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Normed.Field.Basic

/-!
### Compact-uniform open conditions

Turning a pointwise condition that holds uniformly over a compact parameter set into an
*open* condition on an external parameter.  Concretely, if `φ : X → Y → ℝ` is continuous
and satisfies a strict pointwise condition at `x₀` for every `y` in a compact `K`, then the
same condition holds for every `x` in a neighbourhood of `x₀`, uniformly over `K`.

The engine is `IsCompact.mem_prod_nhdsSet_of_forall`: the set where the condition holds is
open in `X × Y`, hence a neighbourhood of `{x₀} × K`, and a neighbourhood of `{x₀} × K` in
the product filter `𝓝 x₀ ×ˢ 𝓝ˢ K` unwinds to a common `U ∈ 𝓝 x₀` and `V ⊇ K`.

These are the topological glue lemmas used to open up "the configuration is nondegenerate"
conditions in the totally-real development, where the compact parameter is a real coordinate
or a pair/triple of them.
-/

namespace Pconstructible

open Filter Set
open scoped Topology

/-- If `φ : X → Y → ℝ` is continuous and `φ x₀ y < 0` for all `y` in a compact set `K`,
then `φ x y < 0` for all `y ∈ K` and all `x` in a neighbourhood of `x₀`.

-- Theorem: `∀ y ∈ K, φ x₀ y < 0` propagates to a neighbourhood of `x₀`, uniformly on `K`. -/
theorem exists_nhds_forall_lt {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {K : Set Y} (hK : IsCompact K) {φ : X → Y → ℝ}
    (hφ : Continuous (Function.uncurry φ)) {x₀ : X} (h0 : ∀ y ∈ K, φ x₀ y < 0) :
    ∃ U ∈ 𝓝 x₀, ∀ x ∈ U, ∀ y ∈ K, φ x y < 0 := by
  let s : Set (X × Y) := (Function.uncurry φ) ⁻¹' Set.Iio 0
  have hsopen : IsOpen s := (isOpen_Iio (a := (0 : ℝ))).preimage hφ
  have hmem : ∀ y ∈ K, s ∈ 𝓝 x₀ ×ˢ 𝓝 y := by
    intro y hy
    rw [← nhds_prod_eq]
    exact hsopen.mem_nhds (show (x₀, y) ∈ s from h0 y hy)
  have hprod : s ∈ 𝓝 x₀ ×ˢ 𝓝ˢ K := hK.mem_prod_nhdsSet_of_forall hmem
  rw [Filter.mem_prod_iff] at hprod
  obtain ⟨U, hU, V, hV, hUV⟩ := hprod
  have hKV : K ⊆ V := fun z hz => mem_of_mem_nhds ((mem_nhdsSet_iff_forall.mp hV) z hz)
  refine ⟨U, hU, fun x hx y hy => ?_⟩
  have hxy : (x, y) ∈ s := hUV ⟨hx, hKV hy⟩
  simpa [s, Function.uncurry] using hxy

/-- `exists_nhds_forall_lt` with only *pointwise* continuity at the points `(x₀, y)`, `y ∈ K`,
instead of global continuity of `Function.uncurry φ`. This is the form the chain-local lemma
needs, because the chain's step functions are continuous only where their denominators are
nonzero. -/
theorem exists_nhds_forall_lt_of_continuousAt {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {K : Set Y} (hK : IsCompact K) {φ : X → Y → ℝ} {x₀ : X}
    (hφ : ∀ y ∈ K, ContinuousAt (Function.uncurry φ) (x₀, y))
    (h0 : ∀ y ∈ K, φ x₀ y < 0) :
    ∃ U ∈ 𝓝 x₀, ∀ x ∈ U, ∀ y ∈ K, φ x y < 0 := by
  let s : Set (X × Y) := (Function.uncurry φ) ⁻¹' Set.Iio 0
  have hmem : ∀ y ∈ K, s ∈ 𝓝 x₀ ×ˢ 𝓝 y := by
    intro y hy
    rw [← nhds_prod_eq]
    exact (hφ y hy).preimage_mem_nhds
      (isOpen_Iio.mem_nhds (show Function.uncurry φ (x₀, y) ∈ Set.Iio 0 from h0 y hy))
  have hprod : s ∈ 𝓝 x₀ ×ˢ 𝓝ˢ K := hK.mem_prod_nhdsSet_of_forall hmem
  rw [Filter.mem_prod_iff] at hprod
  obtain ⟨U, hU, V, hV, hUV⟩ := hprod
  have hKV : K ⊆ V := fun z hz => mem_of_mem_nhds ((mem_nhdsSet_iff_forall.mp hV) z hz)
  refine ⟨U, hU, fun x hx y hy => ?_⟩
  have hxy : (x, y) ∈ s := hUV ⟨hx, hKV hy⟩
  simpa [s, Function.uncurry] using hxy

/-- Same as `exists_nhds_forall_lt` for a nonvanishing condition.

-- Theorem: `∀ y ∈ K, φ x₀ y ≠ 0` propagates to a neighbourhood of `x₀`, uniformly on `K`. -/
theorem exists_nhds_forall_ne {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {K : Set Y} (hK : IsCompact K) {φ : X → Y → ℝ}
    (hφ : Continuous (Function.uncurry φ)) {x₀ : X} (h0 : ∀ y ∈ K, φ x₀ y ≠ 0) :
    ∃ U ∈ 𝓝 x₀, ∀ x ∈ U, ∀ y ∈ K, φ x y ≠ 0 := by
  let s : Set (X × Y) := (Function.uncurry φ) ⁻¹' ({0}ᶜ : Set ℝ)
  have hsopen : IsOpen s := isOpen_compl_singleton.preimage hφ
  have hmem : ∀ y ∈ K, s ∈ 𝓝 x₀ ×ˢ 𝓝 y := by
    intro y hy
    rw [← nhds_prod_eq]
    exact hsopen.mem_nhds (show (x₀, y) ∈ s from h0 y hy)
  have hprod : s ∈ 𝓝 x₀ ×ˢ 𝓝ˢ K := hK.mem_prod_nhdsSet_of_forall hmem
  rw [Filter.mem_prod_iff] at hprod
  obtain ⟨U, hU, V, hV, hUV⟩ := hprod
  have hKV : K ⊆ V := fun z hz => mem_of_mem_nhds ((mem_nhdsSet_iff_forall.mp hV) z hz)
  refine ⟨U, hU, fun x hx y hy => ?_⟩
  have hxy : (x, y) ∈ s := hUV ⟨hx, hKV hy⟩
  simpa [s, Function.uncurry] using hxy

/-- The same for a finite conjunction: if each `φᵢ x₀` is strictly negative on `K`, all do
so on a common neighbourhood of `x₀`.

-- Theorem: finitely many strict-negativity conditions hold on a common `U ∈ 𝓝 x₀`. -/
theorem exists_nhds_forall_lt_finite {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} {s : Finset ι} {K : Set Y} (hK : IsCompact K) {φ : ι → X → Y → ℝ}
    (hφ : ∀ i ∈ s, Continuous (Function.uncurry (φ i))) {x₀ : X}
    (h0 : ∀ i ∈ s, ∀ y ∈ K, φ i x₀ y < 0) :
    ∃ U ∈ 𝓝 x₀, ∀ x ∈ U, ∀ i ∈ s, ∀ y ∈ K, φ i x y < 0 := by
  classical
  have key : ∀ t : Finset ι, (∀ i ∈ t, Continuous (Function.uncurry (φ i))) →
      (∀ i ∈ t, ∀ y ∈ K, φ i x₀ y < 0) →
      ∃ U ∈ 𝓝 x₀, ∀ x ∈ U, ∀ i ∈ t, ∀ y ∈ K, φ i x y < 0 := by
    intro t
    induction t using Finset.induction with
    | empty =>
        intro _ _
        exact ⟨Set.univ, Filter.univ_mem, fun x _ i hi => by simp at hi⟩
    | insert a t hat ih =>
        intro hφ' h0'
        obtain ⟨Ua, hUa, hUa'⟩ :=
          exists_nhds_forall_lt hK (hφ' a (Finset.mem_insert_self a t))
            (h0' a (Finset.mem_insert_self a t))
        obtain ⟨Ut, hUt, hUt'⟩ :=
          ih (fun i hi => hφ' i (Finset.mem_insert_of_mem hi))
            (fun i hi => h0' i (Finset.mem_insert_of_mem hi))
        refine ⟨Ua ∩ Ut, Filter.inter_mem hUa hUt, fun x hx i hi y hy => ?_⟩
        rw [Finset.mem_insert] at hi
        rcases hi with rfl | hi
        · exact hUa' x hx.1 y hy
        · exact hUt' x hx.2 i hi y hy
  exact key s hφ h0

/-- The finite-conjunction nonvanishing version, mirroring `exists_nhds_forall_lt_finite`.

-- Theorem: finitely many nonvanishing conditions hold on a common `U ∈ 𝓝 x₀`. -/
theorem exists_nhds_forall_ne_finite {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} {s : Finset ι} {K : Set Y} (hK : IsCompact K) {φ : ι → X → Y → ℝ}
    (hφ : ∀ i ∈ s, Continuous (Function.uncurry (φ i))) {x₀ : X}
    (h0 : ∀ i ∈ s, ∀ y ∈ K, φ i x₀ y ≠ 0) :
    ∃ U ∈ 𝓝 x₀, ∀ x ∈ U, ∀ i ∈ s, ∀ y ∈ K, φ i x y ≠ 0 := by
  classical
  have key : ∀ t : Finset ι, (∀ i ∈ t, Continuous (Function.uncurry (φ i))) →
      (∀ i ∈ t, ∀ y ∈ K, φ i x₀ y ≠ 0) →
      ∃ U ∈ 𝓝 x₀, ∀ x ∈ U, ∀ i ∈ t, ∀ y ∈ K, φ i x y ≠ 0 := by
    intro t
    induction t using Finset.induction with
    | empty =>
        intro _ _
        exact ⟨Set.univ, Filter.univ_mem, fun x _ i hi => by simp at hi⟩
    | insert a t hat ih =>
        intro hφ' h0'
        obtain ⟨Ua, hUa, hUa'⟩ :=
          exists_nhds_forall_ne hK (hφ' a (Finset.mem_insert_self a t))
            (h0' a (Finset.mem_insert_self a t))
        obtain ⟨Ut, hUt, hUt'⟩ :=
          ih (fun i hi => hφ' i (Finset.mem_insert_of_mem hi))
            (fun i hi => h0' i (Finset.mem_insert_of_mem hi))
        refine ⟨Ua ∩ Ut, Filter.inter_mem hUa hUt, fun x hx i hi y hy => ?_⟩
        rw [Finset.mem_insert] at hi
        rcases hi with rfl | hi
        · exact hUa' x hx.1 y hy
        · exact hUt' x hx.2 i hi y hy
  exact key s hφ h0

/-- The `0 < φᵢ x₀ y ^ 2` (equivalently `φᵢ x₀ y ≠ 0`) finite-conjunction version: a common
neighbourhood of `x₀` on which all the squares stay positive.

-- Theorem: finitely many `0 < φᵢ x₀ y ^ 2` conditions hold on a common `U ∈ 𝓝 x₀`. -/
theorem exists_nhds_forall_mixed {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} {s : Finset ι} {K : Set Y} (hK : IsCompact K) {φ : ι → X → Y → ℝ}
    (hφ : ∀ i ∈ s, Continuous (Function.uncurry (φ i))) {x₀ : X}
    (h0 : ∀ i ∈ s, ∀ y ∈ K, 0 < φ i x₀ y ^ 2) :
    ∃ U ∈ 𝓝 x₀, ∀ x ∈ U, ∀ i ∈ s, ∀ y ∈ K, 0 < φ i x y ^ 2 := by
  obtain ⟨U, hU, h⟩ :=
    exists_nhds_forall_ne_finite (K := K) (s := s) hK (φ := φ) hφ
      (fun i hi y hy => by
        intro hz
        have hpos := h0 i hi y hy
        rw [hz] at hpos
        norm_num at hpos)
  refine ⟨U, hU, fun x hx i hi y hy => ?_⟩
  rw [pow_two]
  exact mul_self_pos.mpr (h x hx i hi y hy)

end Pconstructible
