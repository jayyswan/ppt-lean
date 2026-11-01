# HANDOFF: Octic TraceForm

## Result

`Pptc/Octic/TraceForm.lean` created. **Compiles** (`lake build Pptc.Octic.TraceForm`:
"Build completed successfully"), no `sorry`/`admit`/`axiom`, no diagnostics.
`lean_verify` on `companionN_trace_pow_aeval8`, `qform_Gram8_Lcomb8`, `Lcomb8_coeff7`,
`p3vec8_eq_sum`, `svec8_zero`, `Gram8_symm` reports only
`propext, Classical.choice, Quot.sound`.

68 declarations, all in `namespace Pconstructible`, all with `-- Theorem:` comments,
all lines ≤ 100 characters.

## Declarations produced (in order)

companionN_trace_pow_aeval8, trace_pow_companion8_Pconstructible, hermiteForm8, polyOfVec8,
aeval_polyOfVec8, aeval_polyOfVec8_sq, trace_aeval_polyOfVec8_sq, hermiteForm8_eq_trace_sq,
Hmat8, svec8, p1vec8, p3vec8, Hmat8_Pconstructible, Hmat8_symm, svec8_Pconstructible,
svec8_zero, p1vec8_eq_trace, qform_Hmat8_eq_hermiteForm8, e8 (+ e8_apply_self,
e8_apply_ne), bvec8, coeff7, Lcomb8, Gram8, bvec8_apply_zero, bvec8_apply_succ,
bvec8_Pconstructible, p1vec8_bvec8, p1vec8_Lcomb8, Lcomb8_coeff7, Lcomb8_injective,
bilin_Gram8_Lcomb8, qform_Gram8_Lcomb8, qform_Gram8_eq_trace_sq, Gram8_Pconstructible,
Gram8_symm, vecOf8, polyOfVec8_vecOf8, polyOfVec8_smul_add, p1vec8_vecOf8,
aeval_C_mul_smul8, qform_Hmat8_smul_add_vecOf8, smul_mul_smul8, trace_sq_smul_add8,
Lcomb8_smul_add, aeval_sub_C8, trace_sq_sub_scalar8, aeval_sub_C_smul_add8, cube_add8,
smul_pow8, cube_smul_add8, trace_cube_smul_add8, Lcomb8_smul, Lcomb8_sub,
Lcomb8_Pconstructible, bilin_eq_sum8, bilin_Hmat8_Lcomb8, trace_pow_Pconstructible8,
trace_mul_Pconstructible8, polyOfVec8_coeff_Pconstructible, polyOfVec8_natDegree_le,
polyOfVec8_ne_zero, aeval_polyOfVec8_smul_add, p1vec8_smul_add, p3vec8_eq_sum,
continuous_p3vec8, p3vec8_smul.

## Deviations from the task spec (IMPORTANT for downstream files)

1. **`bvec8` differs from the literal formula in the task.** The task gave
   `if i = 0 then 0 else if i = j+1 then 1 else 0`, which is the shift vector `e_{j+1}`; that
   vector is *not* in `{p1vec8 = 0}` (`p1vec8 (bvec8 j) = svec8 (j+1)`), so
   `p1vec8_bvec8`, `p1vec8_Lcomb8` and `Lcomb8_coeff7` would all be false. I used the
   DegreeSeven analogue instead (as `PLAN.md` §2.5 implies via `pos_dir_of_pair8`
   "with the `2/8` shift"):
   `bvec8 q j = e8 (Fin.succ j) - (svec8 q (Fin.succ j) / 8) • e8 0`.
   Consequences for downstream:
   - `bvec8_apply_zero q j : bvec8 q j 0 = -svec8 q (Fin.succ j) / 8`
   - `bvec8_apply_succ q j k : bvec8 q j (Fin.succ k) = if k = j then 1 else 0`
2. **Names that already exist for `Fin 7` in `Pconstructible` got an `8` suffix**
   (redeclaring them was impossible): `smul_mul_smul8`, `trace_sq_smul_add8`,
   `trace_sq_sub_scalar8`, `cube_add8`, `smul_pow8`, `cube_smul_add8`,
   `trace_cube_smul_add8`, `trace_pow_Pconstructible8`, `trace_mul_Pconstructible8`,
   `aeval_C_mul_smul8`, `aeval_polyOfVec8_smul_add` (task said `aeval_polyOfVec_smul_add`),
   `p1vec8_smul_add` (task said `p1vec_smul_add`). Extra helpers: `aeval_sub_C8`,
   `aeval_sub_C_smul_add8`, `bilin_eq_sum8`, `bilin_Hmat8_Lcomb8`,
   `trace_pow_companion8_Pconstructible`, `e8`, `e8_apply_self`, `e8_apply_ne`.
3. **`qform_Gram8_Lcomb8`** has the shape of `qform_Hmat_Lcomb`
   (`qform (Hmat8 q) (Lcomb8 q x) = qform (Gram8 q) x`). The trace form requested in the
   task is provided separately as
   `qform_Gram8_eq_trace_sq : qform (Gram8 q) x =
     Matrix.trace ((aeval (companionN (n := 8) q) (polyOfVec8 (Lcomb8 q x))) ^ 2)`
   (the `qform_Gram8_eq_trace_sq` of `PLAN.md` §2.2).
4. `companionN_trace_pow_aeval8` is derived from `companionN_aeval_map_eq` and
   `companionN'_trace_pow` (via `RingHom.mapMatrix_apply`, `map_pow`,
   `AddMonoidHom.map_trace`), not by porting `companion7_trace_aeval`.

## Constants checked

- `svec8_zero : svec8 q 0 = 8`
- `trace_sq_sub_scalar8 : … + c ^ 2 * 8`
- coefficient vectors `Fin 8`, coordinate vectors `Fin 7`
- `polyOfVec8_natDegree_le : (polyOfVec8 v).natDegree ≤ 7`
- `polyOfVec8_vecOf8` / `polyOfVec8_smul_add` / `p1vec8_vecOf8` take `natDegree ≤ 7`
- `Fin.sum_univ_succ` used where `Fin 7` used it (works for `Fin 8 = Fin (7+1)`);
  `Fin.sum_univ_eq_sum_range … 8` in `polyOfVec8_vecOf8`.
- `neg_dir_of_pair` / `pos_dir_of_pair` / `aeval_sub_C`-based pair lemmas are *not* here
  (they belong in `Cone.lean`, as instructed).

## Remaining issues

None. `qform`, `bilin` and their generic algebra are reused from `Pptc.DegreeSeven` as
required; nothing else was edited.
