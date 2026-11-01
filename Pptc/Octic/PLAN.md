# Octics with a nonreal root: plan for `Pptc/Octic/`

**Goal.** Close the case that `TotallyReal/Main.lean` leaves as future work: a separable octic
with P-constructible coefficients and at least one nonreal root. Combined with the existing
`root_Pconstructible_totallyReal_eight` (splitting case) and
`root_Pconstructible_of_nonSeparable_eight`, this gives

```lean
theorem root_Pconstructible_deg8_coeffs {q : ℝ[X]} (hq : q ≠ 0) (h8 : q.natDegree ≤ 8)
    (hcoef : ∀ k, PConstructible (q.coeff k)) {α : ℝ} (hα : q.eval α = 0) :
    PConstructible α
```

i.e. every real root of every octic with P-constructible coefficients is P-constructible.

**Route.** This is the septic Bring–Jerrard proof (`DegreeSeven.lean`, §A–F) moved up one
degree:

1. Find `φ`, with `deg φ ≤ 7`, P-constructible coefficients and `φ ≠ 0`, such that
   `Tr φ = Tr φ² = Tr φ³ = 0` on `ℝ[X]/(q)`.
2. By Newton's identities the characteristic polynomial `R` of `φ(C_q)` has no `X⁷, X⁶, X⁵`
   terms, so `y = φ(β)` satisfies `y⁸ = c₄y⁴ + … + c₀` with P-constructible `cᵢ`.
3. `y` is P-constructible, read off where `power_law 1 8` crosses a quartic graph.
4. `β` is a root of `φ − C y`, which has degree `≤ 7` and is nonzero, so the septic theorem
   `root_Pconstructible_deg7_coeffs` recovers it.

Steps 2–4 are routine ports. Step 1 is the new mathematics, and almost all of it is a port
of the septic construction from dimension 6 to dimension 7.

---

## 0. Status of the draft sketch

The draft of `OcticNonreal.lean` this plan started from cites the following names, and every
one exists in the repo as of 2026-11-01 (checked with `rg`):
`powerLaw_cubic_root_Pconstructible` (Basic:976), `quarticGraph_PConstructibleCurve` /
`quarticGraph` / `quarticVal` (TotallyReal/Engines), `powerLaw_root_pos_Pconstructible`,
`exists_rat_isolating`, `charpoly_aeval_coeff_6_5_4_eq_zero`, `companionN`,
`companionN'_trace_pow`, `companionN_charpoly_aeval_isRoot`,
`charpoly_aeval_companionN_coeff_Pconstructible` (TotallyReal/YSpace), the Newton lemmas
`esymm_one_eq_sum'` / `two_mul_esymm_two'` / `three_mul_esymm_three'` (TotallyReal/Newton),
`resolvent_powerLaw`, `natDegree_ne_zero_of_trace_zero`, `Gram`, `Lcomb`, `coeff6`,
`p1vec`, `p3vec`, `qform`, `qform_Hmat_Lcomb`, `polyOfVec`,
`exists_cone_point_Pconstructible`, `exists_pos_quadratic_root`, `stereo`,
`exists_sextic_along_line`, `exists_sign_change`, `roots_eq_pair_add_real`,
`exists_rat_vec_pos`, `root_Pconstructible_le_six_coeffs`, `root_Pconstructible_deg7_coeffs`,
`root_Pconstructible_of_nonSeparable_eight`, `root_Pconstructible_totallyReal_eight`,
`exists_nonreal_root_of_not_splits`.

**Corrections to the sketch. Read these before you start.**

1. **The `s = 1` / `s ≥ 2` split must stay.** The sketch has one sign-change lemma (C3)
   "uniform in `s ≥ 1`", but the septic proof does not work that way, and the reason carries
   over to degree 8.
   - `s ≥ 2` (two or more conjugate pairs): no sign change is needed. Take two distinct pairs
     `z`, `w`, build definite 2-planes (`neg_dir_of_pair`, `pos_dir_of_pair`), project them
     orthogonally to `P₀`, and get a second P-constructible cone vector `x ⊥ P₀` that is not
     parallel to `P₀`. Then `span(P₀, x)` is a totally isotropic plane, `p₃` restricted to it
     is a binary cubic, and `binary_cubic_zero` finds a P-constructible zero
     (`exists_tschirnhaus_traces`, DegreeSeven:4211).
   - `s = 1`: here there is *no* totally isotropic plane (`isotropic_plane_trivial`,
     DegreeSeven:3102), so the stereographic sign-change route is required. Its
     non-degeneracy step (`vstar ≠ 0` in `root_Pconstructible_of_one_conjugate_pair`) relies
     on exactly that triviality.

   A uniform C3 would still need the binary-cubic fallback whenever `vstar = 0` for `s ≥ 2`,
   so it saves nothing. The 599/600 numerical result is evidence, not a proof. **Use the
   split.** For the octic, `Q` restricted to `V = {Tr φ = 0}` has signature `(7 − s, s)`, so:
   `s = 1` gives `(6, 1)`, and no isotropic plane exists, as in degree 7. `s = 2, 3, 4`
   gives a negative 2-plane from any two pairs, and the positive part has dimension
   `7 − s ≥ 3`. `s = 4` leaves no real roots, so it is vacuous under `hβ`, but the `s ≥ 2`
   route does not need that fact.
2. `exists_sign_change8` needs the hypothesis
   `hone : ∀ w, … eval w = 0 → w.im ≠ 0 → w = z ∨ w = conj z` (as `exists_sign_change` has).
   The sketch omits it.
3. `exists_tschirnhaus_traces8` therefore splits into two lemmas: `…_two_pairs8` (hypotheses
   `z, w` from distinct pairs, as at DegreeSeven:4211) and the `s = 1` assembly
   (`root_Pconstructible_of_one_conjugate_pair8`, as at DegreeSeven:4352). The sketch's single
   `root_Pconstructible_of_nonreal_separable_eight` becomes a case split on whether a second
   pair exists, copying `root_Pconstructible_of_nonreal_root` (DegreeSeven:4488).
4. **Part A, positive branch.** `powerLaw_root_pos_Pconstructible` cannot be reused
   directly: it needs a `ℚ`-polynomial (it crosses with `poly_graph`), and our quartic has
   P-constructible real coefficients. Copy its *shape* (crop with `restrict`, isolate with
   `exists_rat_isolating`, read off with `inter_x`), but cross `power_law 1 8` with
   `quarticGraph_general_PConstructibleCurve`. `powerLaw_cubic_root_Pconstructible`
   (Basic:976, crossing `power_law` with `cubicGraph`) is the closer template.
5. **Final case split.** `root_Pconstructible_totallyReal_eight` already handles the
   non-separable case internally. The degree-8 theorem is therefore: `natDegree ≤ 7` → septic
   theorem; otherwise normalise to monic `q₀`, then `q₀.Splits` → totally real theorem;
   `¬Splits ∧ ¬Separable` → `root_Pconstructible_of_nonSeparable_eight`;
   `¬Splits ∧ Separable` → `exists_nonreal_root_of_not_splits`, then the new theorem.
6. Use `companionN (n := 8)` throughout. Do **not** introduce a `companion8`.
   `TotallyReal/YSpace` already proves the generic facts, and the septic file's `companion7`
   lemmas exist only because they predate `companionN`.

---

## 1. Constants that change from 7 to 8

Port these by hand and do not trust a copy-paste; each one is a silent wrong-number risk:

| Septic | Octic | Where |
|---|---|---|
| `svec_zero : svec q 0 = 7` | `= 8` | trace of identity |
| `trace_sq_sub_scalar … + c ^ 2 * 7` | `* 8` | DegreeSeven:1832 |
| `pos_dir_of_pair` mean shift `C (2 / 7)` | `C (2 / 8)` | DegreeSeven:1848 |
| `natDegree_ne_zero_of_trace_zero`: `Tr (C c) = 7c` | `8c` | DegreeSeven:2416 |
| `roots_eq_pair_add_real`: `R.card = 5` | `6` | DegreeSeven:2675 |
| interpolation degree `≤ 6` at 7 roots | `≤ 7` at 8 roots | `exists_poly_value_at_root` |
| `Fin 7` coefficient vectors, `Fin 6` coordinates | `Fin 8`, `Fin 7` | everywhere |
| `polyOfVec_natDegree_le : ≤ 6` | `≤ 7` | DegreeSeven:2000 |
| tail: `root_Pconstructible_le_six_coeffs` / `root_Pconstructible_of_powerLaw` | `root_Pconstructible_deg7_coeffs` | recovery |

Several things do **not** change: the Newton/esymm algebra, the stereographic formula, the
sextic degree of `Ψ` (still `≤ 6`, because `stereo` is quadratic and `p₃` is cubic), the
`ω = e^{2πi/3}` sign certificate (its traces are still `0, 0, 3`), and `binary_cubic_zero`.

---

## 2. File layout and dependency graph

All files are in `Pptc/Octic/`, under namespace `Pconstructible`, with targeted imports only.

```
            Engine ──────────────┐
                                 ▼
TraceForm ──► Resolvent ◄── (YSpace, Newton, DegreeSeven, TotallyReal.Main)
   │                             │
   ├──► Roots ──┐                │
   │            ▼                │
   ├──► Cone ──► TwoPairs ───────┤
   │      │                      ▼
   └──► Sextic ──► OnePair ──► Main
           Roots ─┘
```

Three files have no new dependencies and can start in parallel on day one: `Engine`,
`TraceForm`, and `Resolvent` (except its final lemma, which imports `Engine`).

### 2.1 `Octic/Engine.lean` (Part A, about 150 lines)

Imports: `Pptc.TotallyReal.Engines`, `Pptc.Basic`.

- `quarticGraph_general_PConstructibleCurve` (`c₄ ≠ 0`): show
  `quarticGraph c₀ … c₄ = (fun p => (p.1, c₄ * p.2)) '' quarticGraph (c₀/c₄) … (c₃/c₄) 1`,
  then apply `scale_y c₄` to Lemma Q.
- `powerLaw_quartic_root_Pconstructible` (`β⁸ = quarticVal c₀ … c₄ β`), with three branches:
  - `c₄ = 0`: `powerLaw_cubic_root_Pconstructible (n := 8)`, after rewriting `quarticVal … 0`
    to `cubicVal`;
  - `β > 0`: cross `restrict (power_law 1 8)` with `quarticGraph_general`. Uniqueness in a
    rational window comes from `X⁸ − quartic ≠ 0` (monic of degree 8), whose finite root set
    gives `exists_rat_isolating`;
  - `β < 0`: reflect, mapping `(c₁, c₃) ↦ (−c₁, −c₃)` (`(−β)⁸ = β⁸`), as in the cubic engine.
  - `β = 0` is trivial.
- Tag `@[pconstructible_cond]` only if the side condition fits the tactic's convention
  (see `Tactic.lean`). The engine probably should not be tagged.

### 2.2 `Octic/TraceForm.lean` (about 700 lines; the bulk of the port)

Imports: `Pptc.DegreeSeven`, `Pptc.TotallyReal.YSpace`. This is a port of DegreeSeven §§
1230–2050 to `companionN (n := 8)`:

- `companionN_trace_pow_aeval8`: `algebraMap ℝ ℂ (Tr (φ(C)^k)) = Σ_{roots} φ(z)^k`. Compose
  `companionN_aeval_map_eq` and `companionN'_trace_pow`; this is the one lemma everything
  else rests on.
- Data: `Hmat8 : Matrix (Fin 8) (Fin 8) ℝ`, `svec8`, `p1vec8`, `p3vec8`, `polyOfVec8`,
  `vecOf8`, `bvec8 (j : Fin 7)`, `coeff7`, `Lcomb8 : (Fin 7 → ℝ) → Fin 8 → ℝ`,
  `Gram8 : Matrix (Fin 7) (Fin 7) ℝ`.
- Facts: `Gram8_symm`, `Gram8_Pconstructible`, `Hmat8_Pconstructible`, `p1vec8_eq_trace`,
  `p1vec8_Lcomb8 = 0`, `Lcomb8_coeff7`, `Lcomb8_injective`,
  `qform_Gram8_Lcomb8 : qform (Gram8 q) x = Tr ((polyOfVec8 (Lcomb8 q x))(C)²)` (the
  sketch's `qform_Gram8_eq_trace_sq`), `bilin_Gram8_Lcomb8`, `Lcomb8_Pconstructible`,
  `polyOfVec8_*` (coefficients, `natDegree ≤ 7`, `≠ 0`), `p3vec8_eq_sum` (triple-sum
  formula), `continuous_p3vec8`, `p3vec8_smul`.
- `qform`, `bilin` and their algebra (`bilin_comm`, `qform_add`, `qform_smul_add`,
  `continuous_qform`, …) are **already generic in `n`**. Reuse them; do not copy them.

### 2.3 `Octic/Resolvent.lean` (Part B, about 250 lines)

Imports: `Pptc.TotallyReal.Main`, `Pptc.Octic.Engine`. This file uses only `companionN`
and does not need `TraceForm`.

- `charpoly_aeval_coeff_7_6_5_eq_zero`: copy of DegreeSeven:1149, via the roots multiset,
  `companionN'_trace_pow`, and the primed Newton lemmas.
- `resolvent_quarticPowerLaw`: `c_k := −R.coeff k` for `k ≤ 4`, with
  `companionN_charpoly_aeval_isRoot 8` and
  `charpoly_aeval_companionN_coeff_Pconstructible 8`.
- `natDegree_ne_zero_of_trace_zero8`: `Tr (C c · 1) = 8c`.
- `root_Pconstructible_of_tschirnhaus8`, the tail: steps 2–4 of the route, ending in
  `root_Pconstructible_deg7_coeffs` on `φ − C (φ.eval β)`. That polynomial is nonzero
  because `natDegree φ ≥ 1`, and its degree is `≤ 7`.

### 2.4 `Octic/Roots.lean` (about 600 lines)

Imports: `Pptc.Octic.TraceForm`. A port of DegreeSeven 460–950 and 2666–2765:

- `exists_poly_value_at_root8`: a real `f` with `deg f ≤ 7` and `f(z) = c`,
  `f(z̄) = c̄`, vanishing at every other root. This is Lagrange interpolation via
  `q /ₘ conjQuad z`. `conjQuad*` and `eval_map_conj` are degree-free and reused as is.
- `exists_neg_trace8`, `exists_pos_trace8` (both for `C1`), then `exists_value_pair8`,
  `exists_neg_pair8`, `exists_pos_pair8` (for `s ≥ 2`).
- `roots_eq_pair_add_real8`: with `hone`, the roots are `z, z̄` plus a nodup
  `R : Multiset ℝ` of card `6`.
- `multiset_sum_eq_two_of_vanish` and `exists_linear_eval` are degree-free; reuse them.

### 2.5 `Octic/Cone.lean` (about 400 lines)

Imports: `Pptc.Octic.Roots`.

- **Generalize, don't copy.** `stereo`, `qform_stereo_eq_zero`, `stereo_smul_add_smul`,
  `exists_orth_projection`, `exists_orth_neg_Pconstructible`,
  `smul_add_smul_eq_zero_of_not_parallel` and `continuous_stereo` are stated for `Fin 6`, but
  their proofs never use the 6. Restate them once for `Fin n` (`stereoN`, …) here. Leave
  `DegreeSeven` untouched: re-pointing it at the generic versions would mean moving them
  below `DegreeSeven` in the import graph, which is a separate cleanup (§5).
- `neg_dir_of_pair8`, `pos_dir_of_pair8` (with the `2/8` shift).
- `exists_cone_point8` (C1): port of DegreeSeven:4054, via `exists_neg_trace8` /
  `exists_pos_trace8` and `exists_pos_quadratic_root`.
- `exists_isotropic_orth_Pconstructible8`, `exists_pos_isotropic_param8`.

### 2.6 `Octic/Sextic.lean` (about 250 lines)

Imports: `Pptc.Octic.Cone`.

- `exists_sextic_along_line8` (C2): port of DegreeSeven:3781. It is mostly degree
  bookkeeping, plus the private `coeff_*_Pc` / `natDegree_*_le` helpers, which are
  dimension-free. Copy the helpers as `private` or make them public in a shared place.
- `continuous_Phi8`, `stereoN_Pconstructible`.

### 2.7 `Octic/TwoPairs.lean` (`s ≥ 2`, about 200 lines)

Imports: `Pptc.Octic.Cone`, `Pptc.Octic.Resolvent`.

- `exists_tschirnhaus_traces_two_pairs8`: port of DegreeSeven:4211. It applies
  `binary_cubic_zero` to the cubic `p3vec8 (Lcomb8 (s • P₀ + t • x))` and expands that cubic
  with `trace_cube_smul_add` (port to `Fin 8`). Non-degeneracy comes from
  `smul_add_smul_eq_zero_of_not_parallel` and `Lcomb8_injective`.
- `root_Pconstructible_of_two_conjugate_pairs8`: the lemma above plus
  `root_Pconstructible_of_tschirnhaus8`.

### 2.8 `Octic/OnePair.lean` (`s = 1`, about 900 lines; the hardest file)

Imports: `Pptc.Octic.Sextic`, `Pptc.Octic.Resolvent`.

- `exists_lagrange_value8` (port of DegreeSeven:2781).
- `isotropic_plane_trivial8` (port of DegreeSeven:2975–3257). The contradiction is unchanged:
  `Σ_r H(r)² + 2 Re H(z)² = 0` over the 6 real roots, and `H` with `deg ≤ 7` that vanishes
  at 8 distinct roots is `0`.
- The `ω` certificate (`omegaC*`, `omegaC_prod*` are degree-free, so reuse them),
  `ofReal_trace_mul_eq_sum8`, `exists_direction_of_value8`, and `exists_sign_change8` (C3,
  with `hone`).
- `root_Pconstructible_of_one_conjugate_pair8`: port of DegreeSeven:4352. It rationalises
  with `exists_rat_vec_pos 7`, solves the sextic by IVT plus
  `root_Pconstructible_le_six_coeffs`, gets `vstar ≠ 0` from `isotropic_plane_trivial8`, and
  finishes with the tail. Keep the `maxHeartbeats 1000000` override and note why.

### 2.9 `Octic/Main.lean` (about 150 lines)

Imports: `Pptc.Octic.TwoPairs`, `Pptc.Octic.OnePair`.

- `root_Pconstructible_of_nonreal_root8`: normalise to monic, then split on separability and
  on whether a second pair exists (copy DegreeSeven:4488).
- `root_Pconstructible_deg8_coeffs`, with the split from §0.5.
- Add `import Pptc.Octic.Main` to `Pptc.lean`.
- Edit the module docstring of `TotallyReal/Main.lean`, which currently says the nonreal octic
  is future work. Point it to `Pptc.Octic.Main` instead.

---

## 3. Order of work and fan-out

| Wave | Files (parallel) | Notes |
|---|---|---|
| 1 | `Engine`, `TraceForm`, `Resolvent` (all but the tail) | no shared edits |
| 2 | `Roots`; `Resolvent` tail | `lake build Pptc.Octic.TraceForm` first, for the `.olean` |
| 3 | `Cone` | |
| 4 | `Sextic`, `TwoPairs` | independent once `Cone` builds |
| 5 | `OnePair` | split into two calls: (a) `exists_lagrange_value8` + `isotropic_plane_trivial8`; (b) sign change + assembly |
| 6 | `Main` | |

Subagent rules (from `CLAUDE.md`): use `@lean-prover`, one deliverable per call, one file per
worker, iterate with `lean_diagnostic_messages` / `lean_goal` / `lean_multi_attempt`, and run
`lake_check` only for the final per-file check. Each worker logs to
`HANDOFF-octic-<file>.md` at the repo root. Build `.olean`s one narrow target at a time
(`lake build Pptc.Octic.Foo`). Never chain the big targets: `DegreeSeven` and
`TotallyReal.Main` are already heavy.

**Porting tip.** Start each lemma by asking `lean_hover_info` for the septic original's exact
statement, then rewrite `companion7 q` → `companionN (n := 8) q`, `Fin 7` → `Fin 8`,
`Fin 6` → `Fin 7`, and update §1's constants. Most proofs that use `Fin.sum_univ_seven` or
`fin_cases` need `Fin.sum_univ_eight` or `Fin.sum_univ_succ`; check those spots first.

---

## 4. Definition of done

- No `sorry` anywhere in `Pptc/Octic/`.
- `#print axioms root_Pconstructible_deg8_coeffs` (or `lean_verify`) shows only `propext`,
  `Classical.choice`, `Quot.sound`.
- `lake build Pptc.Octic.Main` succeeds, built on its own and not as part of a full build.
- Every theorem has its `-- Theorem: …` line. Each file has a `/-! … -/` header explaining the
  geometry: signature `(7 − s, s)`, why `s = 1` and `s ≥ 2` differ, and why the sextic
  degree is still 6.
- No lines over 100 characters; CRLF line endings (handled by the guard plugin).
- Commit locally to `main` (git root is `pptc/`). **Ask before pushing.**

---

## 5. Risks and follow-ups

- **`OnePair` size.** The septic `s = 1` file is the 2666–4480 block, about 1800 lines with
  helpers. Expect the octic version to be the same size. The risk is heartbeat blow-ups in
  `ring`/`nlinarith` over 8-term sums. Mitigation: prove sums over `Fin 8` as
  `Fin.sum_univ_succ` followed by the septic-style lemma, not by `simp [Fin.sum_univ_eight]`.
- **Interpolation at degree 7.** `exists_poly_value_at_root` divides by `conjQuad z`. Check
  early that the quotient's degree bound (`≤ 5` → `≤ 6`, plus a linear correction giving
  `≤ 7`) goes through.
- **Optional cleanup, not part of this plan.** Once the octic file has `Fin n` versions of
  `stereo` and friends, move them into a small shared module imported by `DegreeSeven` and
  re-derive the `Fin 6` statements from them. This follows the repo's "generalize, don't
  copy" convention, but it rebuilds `DegreeSeven` and everything above it, so do it as a
  separate commit after `Octic.Main` is green.
- **Degree 9 is not next in line.** `Pptc/Nonic/` already covers rational nonics, using
  Meyer's theorem instead of this route. The real-coefficient nonic would need a sextic
  power-law engine (`y⁹ = quintic`), and quintic graphs are not drawable
  (`archived files/PLAN-totallyreal.md` §5).
