# Workstream B.1 — orthoCompl + restrict (Witt layer)

Target: `Pptc/HasseMinkowski/QuadraticForm/Restriction.lean`, namespace `Pptc.HasseMinkowski`.
Plan: recon Mathlib API, then append defs/theorems incrementally, verify with lean-lsp.

## Log
- start: created log.
- recon: `QuadraticMap.restrict` DOES exist (Basic.lean:253); `LinearMap.BilinForm.orthogonal`
  + finrank/IsCompl API exist (BilinearForm/Orthogonal.lean); `QuadraticMap.Nondegenerate`
  is a structure in Radical.lean; `nondegenerate_associated_iff` available.
- gotcha: dot notation `Q.associated.orthogonal`/`.restrict` resolves to `LinearMap.*`
  (wrong); must write `LinearMap.BilinForm.orthogonal`/`LinearMap.BilinForm.restrict`.
- wrote full file; fixed 3 elaboration errors; LSP diagnostics now EMPTY (success).
- `lake_check Pptc/HasseMinkowski/QuadraticForm/Restriction.lean` -> OK, no errors or warnings.
- `lean_verify` on finrank_add_finrank_orthoCompl, orthoCompl_orthoCompl_eq_of_nondegenerate,
  restrict_nondegenerate_iff_isCompl_orthoCompl,
  restrict_orthoCompl_span_singleton_nondegenerate -> axioms {propext, Classical.choice, Quot.sound}.
- no `sorry`/`admit`/`axiom` in file. DONE (items 1-9 all delivered; item 8's `IsCompl`
  correctly carries `(restrict Q W).Nondegenerate`, since `IsCompl W Wᗮ` is FALSE for arbitrary
  W under merely `Q.Nondegenerate` -- isotropic line in a hyperbolic plane -- while the
  finrank identity does hold under `Q.Nondegenerate` alone).

# Workstream B.3 — orthogonal splitting isometry

Target: append to `Pptc/HasseMinkowski/QuadraticForm/Restriction.lean`:
`isometryEquiv_prod_of_isCompl (Q) (h : IsCompl W (orthoCompl Q W)) :`
`Nonempty (QuadraticMap.IsometryEquiv ((restrict Q W).prod (restrict Q Wᗮ)) Q)`.

## Log
- start: created section; reading file + recon Mathlib API for `prod`, `IsometryEquiv`,
  `LinearEquiv.ofIsCompl`/`prodEquivOfIsCompl`.
- recon: `QuadraticMap.prod` + `QuadraticMap.IsometryEquiv` + `QuadraticMap.prod_apply` +
  `QuadraticMap.associated_isOrtho` (`Q.associated x y = 0 ↔ Q.IsOrtho x y`, `[simp]`) +
  `QuadraticMap.associated_isSymm` all exist. `Submodule.prodEquivOfIsCompl (h) : p×q ≃ₗ E`
  with `Submodule.coe_prodEquivOfIsCompl' : ... x = x.1 + x.2` (rfl) exists.
  Added imports `Mathlib.LinearAlgebra.QuadraticForm.Prod` and `Mathlib.LinearAlgebra.Projection`.
- gotcha: a bare `refine ⟨{ toLinearEquiv := ..., map_app' := ?_ }⟩` / `exact ⟨...⟩` fails
  ("expected type could not be determined") because the structure literal's type is not
  inferable from fields alone. Fix: declare it as a `noncomputable def` with an explicit
  return type (or ascribe the type), then the theorem is `⟨theDef Q h⟩`.
- gotcha: after `intro m` the goal's LHS is `Q ((↑e).toFun m)`, and `rw
  [Submodule.coe_prodEquivOfIsCompl']` does not match it. `change Q (↑m.1 + ↑m.2) = ...`
  works (the linear equiv's `toFun` is defeq to addition).
- MAIN: `isometryEquivProdOfIsCompl` + `isometryEquiv_prod_of_isCompl` compile; LSP
  diagnostics EMPTY (success). Statement shape is the requested `Nonempty
  (IsometryEquiv (prod (restrict Q W) (restrict Q Wᗮ)) Q)`, forward direction (prod → Q).
- optional adds (compile, same file): `isometryEquiv_prod_of_nondegenerate_restrict`
  (hypothesis `(restrict Q W).Nondegenerate`, via
  `restrict_nondegenerate_iff_isCompl_orthoCompl`) and
  `finrank_eq_add_finrank_orthoCompl_of_isCompl` (IsCompl → complementary dimensions, via
  `LinearEquiv.finrank_eq` + `Module.finrank_prod`, needs `[FiniteDimensional k V]`).
- `lake_check Pptc/HasseMinkowski/QuadraticForm/Restriction.lean` -> OK, no errors/warnings.
- `lean_verify Pptc.HasseMinkowski.isometryEquiv_prod_of_isCompl` -> axioms
  {propext, Classical.choice, Quot.sound}. No sorry/admit/axiom. DONE.

## Deliverable summary (B.3)
Declarations appended before `end Pptc.HasseMinkowski` (existing decls untouched):
- `noncomputable def isometryEquivProdOfIsCompl` — the actual isometry (linear equiv is
  `Submodule.prodEquivOfIsCompl`; `map_app'` uses `associated_isOrtho` + `mem_orthoCompl`);
- `theorem isometryEquiv_prod_of_isCompl` — the requested `Nonempty` statement;
- `theorem isometryEquiv_prod_of_nondegenerate_restrict`;
- `theorem finrank_eq_add_finrank_orthoCompl_of_isCompl`.
Imports added: `Mathlib.LinearAlgebra.QuadraticForm.Prod`,
`Mathlib.LinearAlgebra.Projection` (for `Submodule.prodEquivOfIsCompl`).

# Mathlib-4.33 recon: quaternion/Hilbert symbol + Witt/isometry (read-only subagent)

`rg` was NOT on the subagent's PATH, and the read-only agent cannot append to this file, so the
findings are recorded here for it.

Q1 (quaternion / Hilbert symbol) — EXISTS: `QuaternionAlgebra R a b c` (`Algebra/Quaternion.lean:65`),
`Quaternion R := QuaternionAlgebra R (-1) 0 (-1)`, `Quaternion.normSq : ℍ[R] →*₀ R` (multiplicative,
`normSq_mul`, `normSq_def`). ABSENT: no `HilbertSymbol`/norm-residue, no `IsNorm`, no Hilbert 90, no
Kummer theory, no index-2 norm-group theorem, and **no bridge from a quaternion norm form to
`QuadraticMap`**. So A.1 must stay case-based (it did).

Q2 (Witt / isometry) — EXISTS: `LinearMap.BilinForm.IsometryEquiv`/`Equivalent`,
`QuadraticMap.IsometryEquiv`/`Equivalent` (namespace is `QuadraticMap`!), `QuadraticMap.prod` (+
`IsometryEquiv.prod`, `Equivalent.prod`), `QuadraticMap.restrict`/`comp`/`associated_comp`,
full orthoCompl API (`LinearMap.BilinForm.orthogonal`, `le_orthogonal_orthogonal`,
`finrank_orthogonal`, `orthogonal_orthogonal`, `isCompl_orthogonal_iff_disjoint`,
`restrict_nondegenerate_iff_isCompl_orthogonal`), `LinearMap.BilinForm.exists_orthogonal_basis`,
`QuadraticMap.IsOrtho`/`associated_isOrtho`, `QuadraticForm.equivalent_weightedSumSquares`.
ABSENT (the real work): **Witt cancellation**, **Witt extension** (isometry of a subspace extends),
`LinearMap.BilinForm.prod`, and any `IsCompl W Wᗮ ⇒ Q ≅ Q|_W ⊗ Q|_Wᗮ` lemma. The last of these is
now supplied by `isometryEquiv_prod_of_isCompl` in `Restriction.lean` (B.3 above).

# Workstream B.3-b — orthogonal reflections + rank-one transitivity (Witt.lean)

Target (NEW FILE): `Pptc/HasseMinkowski/QuadraticForm/Witt.lean`, ns `Pptc.HasseMinkowski`.
Plan: `reflection` as a `LinearEquiv` `x ↦ x - 2·(B(x,a)/Q a)·a`, prove apply /
involutive / self / isometry; then rank-one transitivity.

## Log
- start: read `Restriction.lean` (264 lines) and this log.
- MATH GOTCHA: the task's stated formula `x ↦ x - (B(x,a)/Q a)·a` (no factor 2) is
  mathematically INCOMPATIBLE with `reflection_self a = -a`, involutivity and isometry:
  with `B(a,a)=Q a` it sends `a ↦ 0` while `Q a ≠ 0`, so it cannot preserve `Q`. Using the
  correct standard orthogonal reflection with the factor 2:
  `x ↦ x - (2 * (Q.associated x a * (Q a)⁻¹)) • a`. `reflection_apply` will reflect this.
- M1 DONE: LSP diagnostics EMPTY on Witt.lean. Decls: `polar_eq_two_mul_associated`,
  `map_add_eq_associated`, `map_sub_eq_associated`, `reflectionLinearMap` (+ `_apply`),
  `associated_reflectionLinearMap`, `reflectionLinearMap_involutive`, `reflectionLinearMap_self`,
  `reflection` (LinearEquiv.ofInvolutive), `reflection_apply`, `reflection_involutive`,
  `reflection_self`, `reflection_isometry` (noncomputable def of `IsometryEquiv Q Q`).
- gotchas: `two_nsmul_associated` is ℕ-nsmul (not k-smul); proof of polar bridge used
  `QuadraticMap.associated_apply` + `Module.End.smul_def` + `half_moduleEnd_apply_eq_half_smul`.
  In `map_smul'` simp needs `RingHom.id_apply` (else `module` sees `(RingHom.id k) c` vs `c`).
- M2 start: `exists_isometryEquiv_of_Q_eq`, case Q(v-w)≠0 use reflection in (v-w);
  case Q(v-w)=0 use reflection in (v+w) then in w (sends v→-w→w).
- M2 DONE: compiles first try (LSP diagnostics EMPTY). `exists_isometryEquiv_of_Q_eq`.
- no sorry/admit/axiom; no lines >100 chars. `lean_verify` on `reflection_isometry` and
  `exists_isometryEquiv_of_Q_eq` -> axioms {propext, Classical.choice, Quot.sound}.
- `lake_check Pptc/HasseMinkowski/QuadraticForm/Witt.lean` -> OK, no errors or warnings.
- NOTE: `reflection_apply` uses factor 2 (`x - 2*(B x a/Q a)•a`), not the task's literal
  (factorless, false) formula; `reflection_self`/involutive/isometry all hold with it.



# Workstream B.3-proper � rank-one Witt cancellation (Witt.lean)

Target: append to `Pptc/HasseMinkowski/QuadraticForm/Witt.lean`:`ntheorem isometryEquiv_orthoCompl_span_of_Q_eq (Q) (hQ : Q.Nondegenerate) {v w} (hv : Q v != 0) (h : Q v = Q w) :`n  Nonempty (IsometryEquiv (restrict Q (orthoCompl Q (span {v}))) (restrict Q (orthoCompl Q (span {w}))))`n
Plan: get phi from exists_isometryEquiv_of_Q_eq; show phi preserves associated (polar); map orthoCompl onto orthoCompl; restrict to linear equiv; package IsometryEquiv.

## Log
- start: read Witt.lean (182 lines) + handoff. Created log.
- recon: IsometryEquiv has fields toLinearEquiv + map_app' (map_app : Q2 (f m) = Q1 m, @[simp]). LinearEquiv.submoduleMap (p) : p =k= p.map e, submoduleMap_apply = rfl. Submodule.mem_map : x in map f p <-> exists y in p, f y = x. Submodule.mem_span_singleton : x in k . y <-> exists a, a . y = x.
- plan confirmed; writing associated preservation + restriction-to-orthoCompl def + main theorem.
- M1 DONE: ssociated_isometryEquiv_map (isometry preserves Q.associated, via polar + map_add).
- M2 DONE: isometryEquivOrthoComplSpanOfQeq + isometryEquiv_orthoCompl_span_of_Q_eq.
- LSP diagnostics EMPTY on Witt.lean (success). File sorry-free.
- gotchas: (a) exists_isometryEquiv_of_Q_eq returns a Prop Exists; cannot obtain/eliminate into a Type-valued def -> used Classical.choose/choose_spec. (b) Submodule.map f.toLinearEquiv needs the LinearEquiv->LinearMap coercion: wrote (f.toLinearEquiv : V ->?[k] V). (c) w [mem_orthoCompl] at goal fails when goal shows x in ?(orthoCompl ...); used change. (d) target x in map f p third component has  = ?f.toLinearEquiv, so pply_symm_apply for IsometryEquiv did not match; used LinearEquiv.apply_symm_apply f.toLinearEquiv y.
- fixed line 210 (>100 chars) by breaking the hmap_le type; all lines <= 100 now.
- lake_check Pptc/HasseMinkowski/QuadraticForm/Witt.lean -> OK, no errors or warnings.
- lean_verify on isometryEquiv_orthoCompl_span_of_Q_eq, isometryEquivOrthoComplSpanOfQeq -> axioms {propext, Classical.choice, Quot.sound}.
- REQUIRED MILESTONE (B.3 proper) DONE. Declarations added (Witt.lean):
  * theorem associated_isometryEquiv_map (isometry preserves Q.associated);
  * noncomputable def isometryEquivOrthoComplSpanOfQeq (the restricted isometry);
  * theorem isometryEquiv_orthoCompl_span_of_Q_eq (rank-one Witt cancellation, Nonempty form).
- Stretch (general Witt cancellation by induction on finrank W): NOT started (required milestone took the budget). Remains open.

# Workstream B.3 general - Witt cancellation (induction on finrank)

Target: append to Pptc/HasseMinkowski/QuadraticForm/Witt.lean: isometryEquiv_orthoCompl_of_isometryEquiv_restrict.
Plan: read Restriction.lean; recon iterate over linear independence / finrank; either induction or Witt extension.

## Log
- start: read Witt.lean (266 lines) + handoff.
- PLAN: proved Witt extension via strong induction on finrank of the abstract space Y, then cancellation. Avoids proving submodule nondegeneracy by working abstractly (Y, QY) with two isometric embeddings into V.
- DONE: associated_map_of_apply_eq; exists_isometryEquiv_of_Q_eq_fixing; exists_isometryEquiv_of_isometric_embeddings (Witt extension); isometryEquiv_orthoCompl_of_isometryEquiv_restrict (main target). LSP diagnostics EMPTY (success), no warnings.
- gotchas: Nat.strong_induction_on case name is 'h' not 'ind'; smul_zero vs zero_smul for 0 � x; w [mem_orthoCompl] at goal needs change due to coercion; Submodule.mem_map_of_mem takes membership first ((f := ...)); ssociated_map_of_apply_eq has implicit Q/QY.
- NEXT: lake_check + lean_verify.
- lake_check Pptc/HasseMinkowski/QuadraticForm/Witt.lean -> OK, no errors or warnings (after one .olean.private read error, killed lean/lake and retried).
- lean_verify (main + both helpers) -> axioms {propext, Classical.choice, Quot.sound}. File sorry-free (grep clean).
- DONE. General Witt cancellation is proved.
