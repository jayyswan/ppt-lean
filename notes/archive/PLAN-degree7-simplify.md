# PLAN: simplify `Pptc/DegreeSeven.lean`

Target file: `pptc/Pptc/DegreeSeven.lean` (≈ 6150 lines, compiles cleanly at the start of this
plan). Goal: remove dead code, merge duplicated lemmas, and replace the diagonalisation-based
`s ≥ 2` argument with a much shorter one. Expected end size ≈ 4000–4300 lines.

The public result `root_Pconstructible_of_nonreal_root` must keep its exact statement.

---

## 0. Ground rules (read first)

- Follow `CLAUDE.md` in the repo root. In particular: lean-lsp tools first, **no whole-project
  `lake build`**, targeted imports only, `-- Theorem:` comment on every theorem, 100-char lines,
  no `sorry`, CRLF handled by the guard plugin.
- MCP file paths are relative to the package root: `Pptc/DegreeSeven.lean`.
- **Line numbers in this plan are approximate** (they refer to the file at the start). Locate
  declarations by name; line numbers drift after every edit.
- Full-file `lean_diagnostic_messages` takes **2–5 minutes** on this file. Pass `timeout_s`
  (e.g. 110) and poll again while `partial: true`. Only lines after the first edit re-elaborate,
  so edits near the end of the file check faster.
- `lean_multi_attempt` **drops newlines in multi-line snippets** (they get glued onto one line),
  so it is only reliable for single-line tactics. For multi-line changes, edit the file and read
  diagnostics for the affected range.
- Work in phases, in order A → B → C → D. After each phase: zero errors in the whole file, no new
  warnings in edited ranges, then commit locally (git root is `pptc/`, branch `main`).
  **Never push.** If the working tree has uncommitted changes when you start, commit them first
  as a baseline.
- Keep a progress log at the repo root: `HANDOFF-degree7-simplify.md`, one line per completed
  step, so an aborted run is recoverable.
- `Pptc/ScratchQuad.lean` is the only module importing `Pptc.DegreeSeven`. Before deleting or
  renaming a declaration, `rg -w <name> Pptc/ScratchQuad.lean`. (At plan time it uses none of
  the declarations below.) `Pptc/StopTotallyReal.lean` has its own unrelated `companion7` and
  `ofReal_multiset_sum`; ignore it.
- Final check: `lean_verify` on `Pconstructible.root_Pconstructible_of_nonreal_root`. Only
  `propext`, `Classical.choice`, `Quot.sound` are allowed.

### Reachability script

`PLAN-degree7-simplify-reach.py` (next to this plan) lists every declaration in the file that is
not transitively referenced from the given root(s). Run it from anywhere:

```
py -3 C:/dev/Powerpoint/lean/PLAN-degree7-simplify-reach.py root_Pconstructible_of_nonreal_root
```

It is token-based and strips comments, so it errs toward "reachable". A declaration it reports
as unreachable really is unused by the main theorem, but always confirm by compiling after
deleting.

---

## Phase A — delete dead code (≈ −800 lines, mechanical)

Delete these declarations. They are unreachable from `root_Pconstructible_of_nonreal_root` and
unused by `ScratchQuad`. Delete in **bottom-up order** (last in file first), so line numbers
above stay valid. Also delete section headers and `/-! ... -/` docs that only describe deleted
declarations, and keep `namespace` / `section` / `end` pairs balanced.

| ~line | declaration | notes |
|---|---|---|
| 5195 | `mem_R_of_root` | |
| 5121 | `omegaC_conj` | |
| 4268 | `root_Pconstructible_of_two_conjugate_pairs` | the main theorem inlines this normalisation |
| 4185–4212 | `septicOnePairCubic`, `_homogeneous`, `_neg`, `_zero` | plus section "The reduced cubic of the one-pair case" |
| 4087 | `root_Pconstructible_of_other_root` | plus section "One P-constructible root yields all of them" |
| 3942–3993 | `septic_one_pair_powerSums_zero`, `septic_one_pair_p3_eq`, `septic_one_pair_Q_zero` | plus section "The one-conjugate-pair reduction" |
| 3789 | `divByMonic_coeff_Pconstructible` | check that `modByMonic_*` doesn't use it (the script says no) |
| 3348 | `sq_smul_add` | |
| 3175 | `p1vec_smul_add_vecOf` | |
| 3150 | `vecOf_Pconstructible` | |
| 3047 | `coeff6_Pconstructible` | |
| 1848–2038 | all of ScratchC **C1** and **C3**: `complete_square2`, `complete_square2_congruence`, `complete_square2_congruence_Pconstructible`, `exists_diag_congruence_two`, `form22`, `bilin22`, `planeVec`, `form22_planeVec`, `bilin22_planeVec`, `bilin22_self`, `hCubic`, `hCubic_one`, `restrict_plane_homogeneous`, `exists_isotropic_vec_of_cubic_root`, `exists_isotropic_vec_of_exists_root` | the whole "inlined from Pptc.ScratchC" block, if nothing else is left in it |
| 1788 | `two_pos_of_posDef` | |
| 1654–1715 | `traceForm_neg_of_poly`, `hermiteForm_comm` | |
| 1607 | `hermiteForm_Pconstructible` | |
| 313–525 | `e7_ext`, `eb`, `eb_eq_e7`, `eb_val`, `transpose_companion7_mulVec_e7_succ`, `transpose_companion7_mulVec_e7_last`, `transpose_companion7_pow_mulVec_e7_zero`, `transpose_companion7_pow_seven_mulVec_e7_zero`, `sum_range_seven_e7`, `sum_range_seven_pow_e7`, `aeval_transpose_companion7_commute`, `aeval_transpose_companion7_mulVec_e7_zero`, `aeval_transpose_companion7_eq_zero`, `companion7_charpoly`, `aeval_companion7_self` | **keep** `e7`, `e7_apply_self`, `e7_apply_ne` (used by `bvec`) |

Do **not** delete now (Phase C removes them): `neg_entries_Pconstructible`,
`smul_entries_Pconstructible`, `pivotEquiv_*`.

**Decision left to the user:** `lightCone_cubic_no_projective_zero` (~3994) and its section "The
stated general lemma is false" are unreachable, but they record that an earlier proof plan was
false. **Keep them** unless the user says otherwise.

**User's decision**
hi it's me the user, yeah go ahead and remove that one too

After Phase A: run the reach script again. Only the items listed as deferred above (plus
`lightCone_cubic_no_projective_zero`) should remain unreachable. Compile, commit.

---

## Phase B — merge duplicates (≈ −250 lines)

Each sub-step is independent. Compile and commit after each.

### B1. One trace-value lemma instead of four copies

Now: `exists_neg_trace` / `exists_pos_trace` (~1041, ~1070) and `exists_neg_pair` /
`exists_pos_pair` (~1103, ~1183) repeat the same block for `c = Complex.I` and `c = 1`: build
`hfsq`, `hfothersq`, call `algebraMap_trace_eq_of_value` twice, and simplify `c + conj c`. The pair
lemmas do it twice each.

1. Add, right after `trace_aeval_eq_zero_of_vanishes`:
   ```lean
   -- Theorem: if a real polynomial `f` takes the value `c` at a non-real root `z` and vanishes at
   -- every other root, then `trace N_f = 2 Re c` and `trace N_f² = 2 Re c²`.
   theorem trace_eq_of_value (q : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 7)
       (hsep : q.Separable) {z : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0)
       (hzim : z.im ≠ 0) {f : ℝ[X]} {c : ℂ}
       (hfz : (f.map (algebraMap ℝ ℂ)).eval z = c)
       (hfother : ∀ x : ℂ, (q.map (algebraMap ℝ ℂ)).eval x = 0 → x ≠ z →
         x ≠ starRingEnd ℂ z → (f.map (algebraMap ℝ ℂ)).eval x = 0) :
       Matrix.trace (aeval (companion7 q) f) = 2 * c.re ∧
         Matrix.trace ((aeval (companion7 q) f) ^ 2) = 2 * (c ^ 2).re
   ```
   Match `hfz` / `hfother` to what `exists_poly_value_at_root` actually returns (check with
   `lean_hover_info`). Proof: the existing `hfsq` / `hfothersq` / `ht` / `htsq` block, then
   `Complex.add_conj` (`z + conj z = ↑(2 * z.re)`) and `(algebraMap ℝ ℂ).injective`.
2. Generic existence lemmas:
   - `exists_value_trace (c : ℂ)`: `∃ f, f.natDegree ≤ 6 ∧ trace = 2 * c.re ∧ trace sq = 2 * (c^2).re`.
   - `exists_value_pair (c : ℂ)`: the pair version plus
     `trace (aeval M f * aeval M g) = 0`. The cross-trace block (currently duplicated in both
     pair lemmas) appears here once.
3. Re-prove `exists_neg_trace`, `exists_pos_trace`, `exists_neg_pair`, `exists_pos_pair` as
   short corollaries (`c := Complex.I` / `c := 1`, then `norm_num` / `simp` with `Complex.I_re`,
   `Complex.I_sq`). Keep their names and statements so the call sites don't change.

Expected: about −150 lines.

### B2. Duplicate helpers in the S1 sections

- `eq_zero_of_eval_zero_on_roots` (private, ~4922) and `eq_zero_of_vanishes_on_roots` (~5231)
  have identical proofs. Move `eq_zero_of_vanishes_on_roots` up to where the private one is (its
  first user, `isotropic_plane_trivial`, comes before ~5231). Delete the private one and update
  the call in `isotropic_plane_trivial`, which passes an extra `_hmon` argument to drop.
- `ofReal_sum_sq` (private, ~4863) is `ofReal_multiset_sum` (~5145) with `F := fun r => H.eval r ^ 2`.
  Move `ofReal_multiset_sum` up, delete `ofReal_sum_sq`, and fix its one use in
  `sum_sq_add_pair_re`. Watch out: `((H.eval r) ^ 2 : ℂ)` elaborates as `(↑(H.eval r)) ^ 2`, not
  `↑((H.eval r) ^ 2)`, so a `push_cast` / `Complex.ofReal_pow` step may be needed.

### B3. Mathlib replacements

- `matrix_sum_apply` (~231) → `Matrix.sum_apply` (argument order `(i j s g)`). Update its user
  `aeval_entries_Pconstructible` and delete it.
- `coeff_finset_sum` (~3464) → `Polynomial.finset_sum_coeff` (same argument order). Update its
  users and delete it.
- `traceH_Pconstructible` (~1591) is an alias of `trace_pow_companion7_Pconstructible q hq _`.
  Inline it at its users (`Hmat_Pconstructible`, plus `hermiteForm_Pconstructible` if that still
  exists) and delete it.

### B4. Real companion matrix → generic companion matrix

`companion7` (~103, over `ℝ`) has literally the same body as `companion7'` (~542, any
`CommRing`). The real-only eigenvector development duplicates the generic one line for line.

1. Move this block up to just before `companion7_charpoly_aeval_isRoot` (~190):
   `companion7'`, `companion7'_apply`, `companionVecC`, `companion7'_mulVec_apply_of_lt`,
   `companion7'_mulVec_apply_last`, `companion7'_mulVec_companionVecC` (from ScratchG) and
   `pow_mulVec_eigenvector_gen`, `aeval_mulVec_eigenvector_gen` (from ScratchN, ~1304). They
   depend only on Mathlib. Keep `companion7_map_eq` where it is.
2. Add `theorem companion7_eq_companion7' (q : ℝ[X]) : companion7 q = companion7' q := rfl`.
   If `rfl` fails, use `by ext i j; rfl`.
3. Re-prove `companion7_charpoly_aeval_isRoot` with `companion7'_mulVec_companionVecC` (`K := ℝ`)
   and `aeval_mulVec_eigenvector_gen`, rewriting with `companion7_eq_companion7'` first.
4. Delete `companionVec`, `companion7_mulVec_apply_of_lt`, `companion7_mulVec_apply_last`,
   `companion7_mulVec_companionVec`, `pow_mulVec_eigenvector`, `aeval_mulVec_eigenvector`.
5. Optional: rename `*_gen` to drop the suffix, if nothing else uses the name.

Expected: about −70 lines.

---

## Phase C — a shorter `s ≥ 2` argument (≈ −1000 lines, +150)

### What happens now

`exists_tschirnhaus_traces` (~3548) needs a P-constructible **totally isotropic plane** `(cv, cw)`
of the Gram form on `{p1 = 0}` with `cv ≠ 0` and `cw` not a multiple of `cv`. Currently:

- `neg_dir_of_pair` / `pos_dir_of_pair` give real planes on which `Q := qform (Gram q)` is
  negative / positive definite;
- `exists_diag_congruence` (the whole ScratchC2 section, ~2039–2670) diagonalises `Gram q` by a
  P-constructible congruence;
- `two_neg_diag_of_pair` / `two_pos_diag_of_pair` move the signature onto the diagonal;
- `exists_diagonal_isotropic_vectors` (~2676) reads off the isotropic vectors.

### The new argument (paper-checked, not yet in Lean)

Write `Q = qform A` and `B = bilin A` for a symmetric `A` with P-constructible entries
(`A = Gram q` in the application).

1. **Cone point.** From one non-real root: `exists_neg_trace`, `exists_pos_trace`, rational
   approximation (`exists_rat_vec_pos` + `continuous_qform`), then `exists_isotropic_Pconstructible`
   give a P-constructible `P₀ ≠ 0` with `Q P₀ = 0`. This is exactly Steps 1–2 of the current
   `root_Pconstructible_of_one_conjugate_pair` (~5943–5978).
2. **Negative and positive directions orthogonal to `P₀`.** `neg_dir_of_pair` gives `v₁, v₂` with
   `Q (a•v₁ + b•v₂) < 0` for `(a, b) ≠ 0`. **These vectors are NOT P-constructible.**
   - *Real direction.* Let `e₀ := v₁` if `B P₀ v₁ = 0 ∧ B P₀ v₂ = 0`, otherwise
     `e₀ := (B P₀ v₂) • v₁ - (B P₀ v₁) • v₂`. Then `B P₀ e₀ = 0`, and `e₀` is a nontrivial
     combination, so `Q e₀ < 0`.
   - *Projection.* Choose a P-constructible `c ≠ 0` and a P-constructible vector `u` such that the
     map `π y := c • y - (B P₀ y) • u` satisfies `B P₀ (π y) = 0` for all `y`:
     - if `B P₀ (Pi.single i 1) ≠ 0` for some `i`, take `u := Pi.single i 1` and `c := B P₀ u`;
     - otherwise `B P₀ ≡ 0` (expand `y` in the standard basis, or use `bilin_eq_sum`), so take
       `c := 1`, `u := 0`.
   - *Rationalise.* `π e₀ = c • e₀`, so `Q (π e₀) = c² · Q e₀ < 0`. The function
     `y ↦ -Q (π y)` is continuous (`continuous_qform`, `continuous_bilin`, `fun_prop`), so
     `exists_rat_vec_pos` gives a rational `r` with `Q (π r) < 0`. Set `e := π r`. It is
     P-constructible, `B P₀ e = 0`, and `Q e < 0`.
   - The same with `pos_dir_of_pair` gives `f` with `B P₀ f = 0` and `0 < Q f`. Get this by
     applying the negative lemma to `A := -Gram q`, using `qform (-A) x = -qform A x` and
     `bilin (-A) x y = -bilin A x y`. In the earlier golf pass,
     `simpa only [qform, Matrix.neg_mulVec, dotProduct_neg, neg_neg_iff_pos]` handled this for
     `qform`.
3. **Second isotropic vector.** `exists_pos_quadratic_root` gives a P-constructible `t > 0` with
   `Q (e + t•f) = 0` (the same computation as in `exists_isotropic_Pconstructible`). Let
   `x := e + t • f`. Then `B P₀ x = 0`.
4. **Independence.** Suppose `x = k • P₀`. Then `e = k • P₀ - t • f`, and
   `Q e = k²·Q P₀ - 2kt·B P₀ f + t²·Q f = t²·Q f > 0`, which contradicts `Q e < 0`. So `x` is
   not a multiple of `P₀`, and in particular `x ≠ 0`.
5. `(P₀, x)` is a totally isotropic, independent plane. Feed `cv := Lcomb q P₀` and
   `cw := Lcomb q x` into the **existing tail** of `exists_tschirnhaus_traces` (from `hcvP`
   onward): `binary_cubic_zero`, `ψ := s • cv + t • cw`, and so on. The facts the tail needs
   change source:
   - `qform (Hmat q) cv = 0`: `qform_Hmat_Lcomb` and `Q P₀ = 0`;
   - `qform (Hmat q) cw = 0`: `qform_Hmat_Lcomb` and `Q x = 0`;
   - `bilin (Hmat q) cv cw = 0`: `bilin_Hmat_Lcomb` and `B P₀ x = 0`;
   - `cv ≠ 0` and `¬ ∃ k, cw = k • cv`: `Lcomb_injective`, `Lcomb_sub`, `Lcomb_smul`;
   - P-constructibility: `Lcomb_Pconstructible` applied directly (no `mulVec`).

### Ordering constraint

`exists_tschirnhaus_traces` (~3548) currently sits **before** everything the new argument needs:
`exists_pos_quadratic_root` (~4152), `exists_isotropic_Pconstructible` (~4455),
`exists_rat_vec_pos` (~4491), `continuous_qform` / `continuous_bilin` (~5863). So:

- Create a new section `/-! ### The s ≥ 2 case: a totally isotropic plane through the cone point -/`
  right after `stereo_Pconstructible` (~5911) and before `root_Pconstructible_of_one_conjugate_pair`.
- **Move** these into it, in this order, keeping their proofs except where noted:
  `smul_add_smul_eq_zero_of_not_parallel`, then the new lemmas below, then
  `exists_tschirnhaus_traces` (rewritten), `natDegree_ne_zero_of_trace_zero`,
  `root_Pconstructible_of_two_conjugate_pairs_monic`. Their other dependencies
  (`resolvent_powerLaw`, `charpoly_aeval_coeff_6_5_4_eq_zero`, `root_Pconstructible_of_powerLaw`,
  `root_Pconstructible_of_nonSeparable`, `binary_cubic_zero`) are all earlier in the file.
- The section doc of "The main trace-killing Tschirnhaus polynomial" and "The `s ≥ 2` case"
  mention "inertia and diagonalisation". Rewrite them to describe the new argument.

### New lemmas (suggested statements; adjust to the real signatures of the helpers)

Check each helper's real signature with `lean_hover_info` first, especially `bilin_Pconstructible`
(is it generic in the matrix?), `qform_smul_add`, `continuous_bilin` and `exists_rat_vec_pos`.

```lean
-- Theorem: the cone of the trace form contains a P-constructible nonzero point as soon as `q`
-- has a non-real root.
theorem exists_cone_point_Pconstructible (q : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 7)
    (hsep : q.Separable) (hq : ∀ k, PConstructible (q.coeff k)) {z : ℂ}
    (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0) (hzim : z.im ≠ 0) :
    ∃ P₀ : Fin 6 → ℝ, (∀ i, PConstructible (P₀ i)) ∧ qform (Gram q) P₀ = 0 ∧ P₀ ≠ 0

-- Theorem: a P-constructible linear map `y ↦ c • y - B P₀ y • u` with `c ≠ 0` lands in the
-- hyperplane `B P₀ · = 0`.
theorem exists_orth_projection {A : Matrix (Fin 6) (Fin 6) ℝ}
    (hA : ∀ i j, PConstructible (A i j)) {P₀ : Fin 6 → ℝ} (hP₀ : ∀ i, PConstructible (P₀ i)) :
    ∃ (c : ℝ) (u : Fin 6 → ℝ), c ≠ 0 ∧ PConstructible c ∧ (∀ i, PConstructible (u i)) ∧
      ∀ y, bilin A P₀ (c • y - bilin A P₀ y • u) = 0

-- Theorem: if `Q` is negative definite on a real plane, there is a P-constructible `e` with
-- `B P₀ e = 0` and `Q e < 0`.
theorem exists_orth_neg_Pconstructible {A : Matrix (Fin 6) (Fin 6) ℝ} (hAsym : Aᵀ = A)
    (hA : ∀ i j, PConstructible (A i j)) {P₀ : Fin 6 → ℝ} (hP₀ : ∀ i, PConstructible (P₀ i))
    {v₁ v₂ : Fin 6 → ℝ}
    (hdef : ∀ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) → qform A (a • v₁ + b • v₂) < 0) :
    ∃ e : Fin 6 → ℝ, (∀ i, PConstructible (e i)) ∧ bilin A P₀ e = 0 ∧ qform A e < 0

-- Theorem: from `P₀` on the cone and P-constructible `e`, `f` orthogonal to it with
-- `Q e < 0 < Q f`, there is a P-constructible isotropic `x ⟂ P₀` that is not a multiple of `P₀`.
theorem exists_isotropic_orth_Pconstructible (q : ℝ[X]) (hq : ∀ k, PConstructible (q.coeff k))
    {P₀ e f : Fin 6 → ℝ} (hQ₀ : qform (Gram q) P₀ = 0)
    (he : ∀ i, PConstructible (e i)) (hf : ∀ i, PConstructible (f i))
    (hBe : bilin (Gram q) P₀ e = 0) (hBf : bilin (Gram q) P₀ f = 0)
    (heQ : qform (Gram q) e < 0) (hfQ : 0 < qform (Gram q) f) :
    ∃ x : Fin 6 → ℝ, (∀ i, PConstructible (x i)) ∧ qform (Gram q) x = 0 ∧
      bilin (Gram q) P₀ x = 0 ∧ ¬ ∃ k : ℝ, x = k • P₀
```

For `exists_isotropic_orth_Pconstructible`, generalise `exists_isotropic_Pconstructible` so it
also returns `∃ t, 0 < t ∧ P₀ = e + t • f` (or factor out the shared computation) instead of
copying its proof.

Then:
- `root_Pconstructible_of_one_conjugate_pair`: replace Steps 1–2 (~5943–5978) with a call to
  `exists_cone_point_Pconstructible`. Check afterwards that `fneg` / `gpos` / `hQneg` / `hQpos`
  aren't used later in that proof.
- `exists_tschirnhaus_traces`: keep the statement. The new proof is
  `exists_cone_point_Pconstructible` → `neg_dir_of_pair` / `pos_dir_of_pair` →
  `exists_orth_neg_Pconstructible` (for `Gram q` and `-Gram q`) →
  `exists_isotropic_orth_Pconstructible` → the existing tail.

Implement the new lemmas one at a time (one `@lean-prover` deliverable each), compiling after each
one, and only then rewrite `exists_tschirnhaus_traces`.

---

## Phase D — second dead-code sweep

Run the reach script. After Phase C these should be unreachable; delete everything reported,
bottom-up:

- ScratchC2 diagonalisation: `pivotEquiv*`, `block_elim`, `block_elim_symm`, `reindex_*`,
  `lift_block`, `diag_congr_of_pivot`, `hyper*`, `Finset.sum_eq_add_of_support`,
  `exists_diag_congruence_fintype_aux`, `exists_diag_congruence`, `one_entries_Pconstructible`,
  `add_/neg_/smul_/mul_entries_Pconstructible`;
- `exists_diagonal_isotropic_vectors`;
- `two_neg_of_negDef`, `two_neg_diag_of_pair`, `two_pos_diag_of_pair`, `qform_diag`,
  `qform_congr`, `bilin_diag`, `bilin_congr`;
- `mulVec_Pconstructible`, `mulVec_eq_zero_of_det_ne_zero`.

**Keep anything the script still reports as reachable.** In particular `Finset.sum_Pconstructible`
(in ScratchC2) is used by `Lcomb_Pconstructible`, `bilin_Pconstructible` and others. If the rest of
its section disappears, move it next to its first user.

Then:
- Try removing imports that may now be unused, one at a time: `Mathlib.Data.Matrix.Block`,
  `Mathlib.LinearAlgebra.Matrix.Reindex`, `Mathlib.Logic.Equiv.Fintype`,
  `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`. Keep any whose removal causes an error.
- Update the file header docstring (lines ~34–53) so the `s ≥ 2` bullet describes the new route.
- Final: full-file diagnostics (zero errors), `lean_verify` on
  `Pconstructible.root_Pconstructible_of_nonreal_root`,
  `lake env lean Pptc/ScratchQuad.lean` (it imports this file), commit locally, and report line
  counts before and after each phase. Do not push.

---

## Out of scope / don't

- Don't change the statement of `root_Pconstructible_of_nonreal_root`,
  `root_Pconstructible_of_one_conjugate_pair` or `root_Pconstructible_of_nonSeparable`.
- Don't refactor `exists_sign_change`, `exists_sextic_along_line`, `exists_lagrange_value` or the
  esymm/Newton section. They are long but not duplicated.
- Don't touch `Pptc/Scratch*.lean` except to check `ScratchQuad` still compiles.
- If any Phase C lemma resists after a reasonable effort, stop and report which one and why.
  Phases A, B and D are valuable on their own.
