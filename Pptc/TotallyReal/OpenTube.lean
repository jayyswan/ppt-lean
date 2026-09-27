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

/-- `exists_nhds_forall_lt` with only *pointwise* continuity at the points `(x₀, y)`, `y ∈ K`,
instead of global continuity of `Function.uncurry φ`. This is the form the chain-local lemma
needs, because the chain's step functions are continuous only where their denominators are
nonzero. -/
theorem exists_nhds_forall_lt_of_continuousAt {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {K : Set Y} (hK : IsCompact K) {φ : X → Y → ℝ} {x₀ : X}
    (hφ : ∀ y ∈ K, ContinuousAt (Function.uncurry φ) (x₀, y))
    (h0 : ∀ y ∈ K, φ x₀ y < 0) :
    ∃ U ∈ 𝓝 x₀, ∀ x ∈ U, ∀ y ∈ K, φ x y < 0 := by
  rw [← eventually_iff_exists_mem]
  exact hK.eventually_forall_of_forall_eventually fun y hy =>
    (hφ y hy).preimage_mem_nhds (isOpen_Iio.mem_nhds (h0 y hy))

/-- Same as `exists_nhds_forall_lt` for a nonvanishing condition.

-- Theorem: `∀ y ∈ K, φ x₀ y ≠ 0` propagates to a neighbourhood of `x₀`, uniformly on `K`. -/
theorem exists_nhds_forall_ne {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {K : Set Y} (hK : IsCompact K) {φ : X → Y → ℝ}
    (hφ : Continuous (Function.uncurry φ)) {x₀ : X} (h0 : ∀ y ∈ K, φ x₀ y ≠ 0) :
    ∃ U ∈ 𝓝 x₀, ∀ x ∈ U, ∀ y ∈ K, φ x y ≠ 0 := by
  rw [← eventually_iff_exists_mem]
  exact hK.eventually_forall_of_forall_eventually fun y hy =>
    hφ.continuousAt.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds (h0 y hy))

end Pconstructible
