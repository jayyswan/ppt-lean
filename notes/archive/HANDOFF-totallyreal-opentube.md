# HANDOFF: TotallyReal/OpenTube.lean

Target file: `pptc/Pptc/TotallyReal/OpenTube.lean` (new). Namespace `Pconstructible`.
Deliverable: generic topological lemmas turning pointwise strict inequalities /
nonvanishing uniform over a compact parameter set into an open condition on the parameter.

Lemmas requested:
- `exists_nhds_forall_lt`  : Continuous (uncurry φ) → (∀ y∈K, φ x₀ y < 0) → ∃ U∈𝓝 x₀, ∀ x∈U, ∀ y∈K, φ x y < 0
- `exists_nhds_forall_ne`  : same with ≠ 0
- `exists_nhds_forall_lt_finite` : finite conjunction over i ∈ s (Finset)
- `exists_nhds_forall_mixed` : finite conjunction, 0 < φ i x y ^ 2

Plan: prove via `IsCompact.mem_prod_nhdsSet_of_forall` with `l := 𝓝 x₀`,
`s := {p | φ p.1 p.2 < 0}` open; unfold `Filter.prod` membership to get U, V with
`U ×ˢ V ⊆ s`, and `K ⊆ V` from `V ∈ 𝓝ˢ K`. Finite version via product trick with
`K' := K ×ˢ s` (s finite ⟹ compact) or Finset induction on intersections of nhds.

## Progress
- [start] dir TotallyReal exists; creating OpenTube.lean.
- [imports] `Mathlib.Topology.Compactness.Compact` alone gives no instances for ℝ. Added
  `Mathlib.Topology.Order.IntermediateValue` (order facts) and `Mathlib.Analysis.Normed.Field.Basic`
  (this is where `Real.normedField`/`TopologicalSpace ℝ` comes from in 4.33; `Mathlib.Topology.Instances.Real`
  does NOT exist — only `.../Real/Lemmas.lean`).
- [proof] lt & ne proved via `IsCompact.mem_prod_nhdsSet_of_forall` + `Filter.mem_prod_iff` + `mem_nhdsSet_iff_forall`.
- [fix] membership of `s` needed `simpa [s, Function.uncurry]`; `Continuous.pow` unavailable,
  so mixed is derived from new `exists_nhds_forall_ne_finite` + `mul_self_pos`.
- [done] `lean_diagnostic_messages`: success, 0 items. Proved: exists_nhds_forall_lt,
  exists_nhds_forall_ne, exists_nhds_forall_lt_finite, exists_nhds_forall_ne_finite,
  exists_nhds_forall_mixed. Final signatures as specified in the task.
- [next] run lake_check + axiom_check.
- [FINAL] `lake_check Pptc/TotallyReal/OpenTube.lean`: OK - no errors or warnings.
  `axiom_check` on all five: [propext, Classical.choice, Quot.sound] — no `sorryAx`.
  Only file created/edited: `pptc/Pptc/TotallyReal/OpenTube.lean`. No scratch files.
