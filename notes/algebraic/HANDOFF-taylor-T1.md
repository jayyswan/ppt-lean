# HANDOFF taylor-T1 — `Pptc/Taylor/Lift.lean`

**Status: DONE.** Zero `sorry`s, no new axioms, `lake build Pptc.Taylor.Lift` succeeds.
Only file created: `Pptc/Taylor/Lift.lean` (no other file touched).

## Declarations (full names, signatures as verified by `lean_file_outline`)

All inside `namespace Pconstructible`, `noncomputable section`, `open Polynomial`.

```lean
structure Pconstructible.TrinomialLift (Coord : ℝ → Prop) (β : ℝ) where
  D : ℕ
  hD : 0 < D
  a b x₀ : ℝ
  c : ℚ
  q : ℚ[X]
  T : ℝ[X]
  y₀ : ℝ
  ha : Coord a
  hb : Coord b
  hx₀ : Coord x₀
  hT : ∀ i, Coord (T.coeff i)
  hroot : x₀ ^ D + a * x₀ + b = 0
  hq : q ≠ 0
  hqy : aeval y₀ q = 0
  hq_sep : q.Separable
  hxT : x₀ = T.eval y₀
  hinj : ∀ z₁ z₂ : ℂ,
    (q.map (algebraMap ℚ ℂ)).eval z₁ = 0 →
    (q.map (algebraMap ℚ ℂ)).eval z₂ = 0 →
    (T.map (algebraMap ℝ ℂ)).eval z₁ = (T.map (algebraMap ℝ ℂ)).eval z₂ → z₁ = z₂
  hβ : β = y₀ ^ 2 + c
```

```lean
theorem Pconstructible.PConstructible.of_unique_common_root
    {q : ℚ[X]} {T : ℝ[X]} (hq : q ≠ 0) (hsep : q.Separable)
    (hT : ∀ i, PConstructible (T.coeff i))
    {x₀ y₀ : ℝ} (hx₀ : PConstructible x₀) (hxT : T.eval y₀ = x₀)
    (hqy : aeval y₀ q = 0)
    (huniq : ∀ z : ℂ, (q.map (algebraMap ℚ ℂ)).eval z = 0 →
      (T.map (algebraMap ℝ ℂ)).eval z = (x₀ : ℂ) → z = (y₀ : ℂ)) :
    PConstructible y₀

theorem Pconstructible.TrinomialLift.Pconstructible {Coord : ℝ → Prop}
    (hCoord : ∀ x, Coord x → PConstructible x) {β : ℝ}
    (h : TrinomialLift Coord β) : PConstructible β
```

Private helper (not exported, used only by the recovery theorem):

```lean
theorem natDegree_le_one_of_separable_of_unique_root
    {K : Type*} [Field K] {φ : K →+* ℂ} (hφ : Function.Injective φ)
    {p : K[X]} (hp : p ≠ 0) (hsep : p.Separable) {a : ℂ}
    (hroot : ∀ z : ℂ, (p.map φ).eval z = 0 → z = a) : p.natDegree ≤ 1
```

## Proof (as implemented)

`of_unique_common_root`: over `K := PReal`,
1. `qK := q.map (algebraMap ℚ PReal)` is nonzero, separable, and `aeval y₀ qK = 0`
   (`Polynomial.aeval_map_algebraMap PReal y₀ q`).
2. `TK` from `Subfield.exists_map_eq_of_forall_coeff_mem PReal`, `xK := ⟨x₀, hx₀⟩`,
   `RK := TK - C xK`; then `RK.map (algebraMap PReal ℝ) = T - C x₀` and `aeval y₀ RK = 0`.
3. `h_int : IsIntegral PReal y₀ := IsAlgebraic.isIntegral ⟨qK, hqK, hqyK⟩`;
   `p := minpoly PReal y₀`, so `p ∣ qK`, `p ∣ RK`, `p.Separable` (`hsepK.of_dvd`),
   `p ≠ 0`, `p.Monic`.
4. Map both divisibilities to `ℂ` (`Polynomial.map_dvd`, `map_map`,
   `IsScalarTower.algebraMap_eq ℚ PReal ℂ` / `… PReal ℝ ℂ`); any root `z` of
   `p.map (algebraMap PReal ℂ)` is then a root of `q.map (algebraMap ℚ ℂ)` and of
   `(T - C x₀).map (algebraMap ℝ ℂ)`, hence satisfies `T z = x₀`, hence `z = y₀` by
   `huniq`.
5. `natDegree p ≤ 1` from the helper lemma (`p` separable + single complex root ⇒
   `natDegree ≤ 1`), using `Polynomial.nodup_roots`, `Multiset.eq_replicate_card`,
   `Multiset.nodup_iff_count_le_one`, `IsAlgClosed.splits`,
   `Splits.natDegree_eq_card_roots`, `natDegree_map_eq_of_injective`.
6. `0 < p.natDegree` (`minpoly.natDegree_pos h_int`), so `p.natDegree = 1`, monic gives
   `p.coeff 1 = 1`; `eq_X_add_C_of_natDegree_le_one hdeg` and `minpoly.aeval` give
   `y₀ + (p.coeff 0 : ℝ) = 0`, hence `y₀ = -(p.coeff 0) ∈ PReal`.

`TrinomialLift.Pconstructible`: derives `huniq` from `hinj` (the `(y₀ : ℂ)` root comes
from `q.map (algebraMap ℚ ℂ) = (q.map (algebraMap ℚ ℝ)).map (algebraMap ℝ ℂ)` +
`eval_map_apply` + `eval_map_algebraMap`), applies the recovery theorem with
`fun i => hCoord _ (hT i)` and `hCoord _ hx₀`, then rewrites `hβ` and closes with
`PConstructible.add (mul hy₀ hy₀) (rat_Pconstructible c)`.

## Verification

- `lean_diagnostic_messages` on the final file: **no diagnostics at all** (no errors, no
  linter warnings).
- `lean_verify`:
  - `Pconstructible.TrinomialLift.Pconstructible` → axioms
    `[propext, Classical.choice, Quot.sound]`, `non_standard_axioms: []`
  - `Pconstructible.PConstructible.of_unique_common_root` → same, no `sorryAx`.
- `lake build Pptc.Taylor.Lift`:
  ```
  ✔ [2970/2970] Built Pptc.Taylor.Lift (16s)
  Build completed successfully (2970 jobs).
  ```

## Gotchas / Mathlib v4.33 naming notes

1. `Polynomial.Separable.nodup_roots` does **not** exist. The v4.33 name is
   `Polynomial.nodup_roots : p.Separable → p.roots.Nodup`.
2. `Multiset.nodup_replicate` and `Multiset.replicate_nodup` do **not** exist. Use
   `Multiset.nodup_iff_count_le_one` (`s.Nodup ↔ ∀ a, count a s ≤ 1`) together with
   `Multiset.count_replicate_self`. `Multiset.eq_replicate_card` exists as
   `s = replicate s.card a ↔ ∀ b ∈ s, b = a`.
3. `minpoly.monic` and `minpoly.ne_zero` take an `IsIntegral K x` argument in this version.
   Get it via `IsAlgebraic.isIntegral ⟨q, hq, hqy⟩` (or `isAlgebraic_iff_isIntegral`).
   `minpoly.natDegree_pos h_int : 0 < (minpoly K x).natDegree` (needs `[Nontrivial B]`)
   saves a `natDegree = 0` case split.
4. `Polynomial.eval_map_apply` / `eval_map_algebraMap` are matched **syntactically** by
   `rw`: the coercion `(y₀ : ℂ)` elaborates to `Complex.ofReal y₀`, which `rw` will not
   match against the pattern `algebraMap ℝ ℂ y₀` even though they are definitionally
   equal. Workaround used in `TrinomialLift.Pconstructible`: prove a local `have h :
   … (algebraMap ℝ ℂ y₀) … := by rw [...]` and finish with `exact h` (elaboration of
   `exact` uses defeq, `rw` does not). Same trick for `algebraMap PReal ℂ y₀`.
5. `rw`/`simp` do not unfold local `let` definitions by themselves; add them to the
   simp set (`simp [RK, hTK, xK]`) or use `dsimp only [qK]` first.
6. `Polynomial.map_ne_zero` requires `[IsSimpleRing R]` (automatic for a field) and
   `[Nontrivial S]`.
7. `Polynomial.Separable.of_dvd` has signature `f.Separable → g ∣ f → g.Separable`, so
   `hsepK.of_dvd hpdq` is the right reading order.
8. `IsScalarTower.algebraMap_eq ℚ PReal ℂ`, `… ℚ ℝ ℂ` and `… PReal ℝ ℂ` all fire as
   plain `rw`s after `rw [Polynomial.map_map]` (goal shape
   `… = q.map ((algebraMap PReal ℂ).comp (algebraMap ℚ PReal))`). `Algebra PReal ℂ` and
   `Algebra ℚ PReal` instances exist out of the box.
9. The structure is `Type`-valued (Lean forbids data fields in `structure … : Prop`), so
   T2 must wrap point existence in `Nonempty (TrinomialLift Coord β)` when phrasing
   `TaylorTrinomial : Prop`.
10. The structure stores `hxT : x₀ = T.eval y₀` while the recovery lemma wants
    `T.eval y₀ = x₀`; the call site uses `hxT.symm`.
11. `set_option linter.dupNamespace false` is needed because the mandated names are
    `Pconstructible.PConstructible.of_unique_common_root` and
    `Pconstructible.TrinomialLift.Pconstructible` (same as `Field.lean` does for
    `PReal.Pconstructible` etc.).

## Deviations from the task text

- The plan's §7.1 sketch used an explicit `gcd` of `q` and `T - C x₀` in `PReal[X]`.
  Implemented instead with `minpoly PReal y₀`: it divides both polynomials, and the
  degree argument runs directly on a monic polynomial, avoiding the `RK = 0` case split
  (`T` constant) and the "gcd of a zero polynomial" edge case. Mathematically identical
  (the gcd divides the minimal polynomial and vice versa up to scalar).
- The task's step 5 ("`y₀` is a root of `p.map …`") turned out to be unnecessary: the
  degree lemma only needs "every complex root is `y₀`", and the final step uses
  `minpoly.aeval`.
- The Möbius inverse wrapper was not added: `mobius_Pconstructible` already exists in
  `Pptc/Taylor/Field.lean`, and the required-contents list for T1 did not ask for it.
- Two targeted Mathlib imports added: `Mathlib.FieldTheory.IsAlgClosed.Basic` (for
  `IsAlgClosed.splits`) and `Mathlib.FieldTheory.Separable` (for `Polynomial.nodup_roots`,
  `separable_map`).
