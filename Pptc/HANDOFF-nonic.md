# HANDOFF — nonic (WP6.4): `Pptc.Nonic.exists_tschirnhaus9`

Target (unchanged, still the only `sorry` in the library):
`Pptc/Nonic.lean:31` `Pconstructible.exists_tschirnhaus9`.

New file: `Pptc/NonicMeyer.lean` (sorry-free, LSP diagnostics clean).
`Pptc/Nonic.lean` was **not** modified.

## Status of the two gaps

* **Gap 1 (`trace_sq_traceZeroPol`) — DONE.**  Proved (line 414 below).
* **Gap 2 (`indefinite_gramTraceZero`) — REFUTED (it is false).**  See below.

## Gap 2 is FALSE — explicit counterexample

The trace form on the `ψ = X` subspace `{f : f.natDegree ≤ 6, Tr f = 0}` (the form of
`gramTraceZero q`) need **not** be indefinite:

  `q = (X² + 1)(X + 13)(X + 12)(X + 3)(X + 2)(X - 2)(X - 8)(X - 11)`

is monic, separable, `natDegree = 9`, with the nonreal roots `±i`.  Its Gram matrix
`gramTraceZero q` has leading principal minors

  `504`, `17062416`, `7177780688000`, `1120883224656340000000 / 9`,
  `109927918051745733200000000000`, `705355934905388066193936000000000000000`

— all positive (Sylvester), so the form is **positive definite**: `Tr (f²) > 0` for every
nonzero `f ∈ V`.  Hence there is **no** nonzero isotropic vector for `ψ = X`, and

  `¬ Indefinite (QuadraticForm.baseChange ℝ (Matrix.toQuadraticForm' (gramTraceZero q)))`.

Cross-check by hand: with `s_1 = -9`, `s_2 = 513`, `f = X + 1` has `Tr f = 0` and
`Tr f² = 504 > 0`; `G_01 = -1596`, `G_00 G_11 - G_01² = 17062416 > 0` ✓.

**Conclusion:** the correct statement must allow a Tschirnhaus transformation `ψ ≠ X`.
The subspace `{φ (ψ x) : deg φ ≤ 6} ∩ {Tr = 0}` depends on `ψ`, and
`NOTES-nonic-meyer.md` §2.2/§4 chooses `ψ` to make its trace form indefinite
(`ψ = X` for `r₂ ≥ 3`; a real-collision `ψ` for `r₂ ∈ {1,2}`).  For the counterexample
above (`r₂ = 1`, seven real roots) the collision choice is required.

## What is proved (file `Pptc/NonicMeyer.lean`, line numbers)

| line | declaration | statement |
|---|---|---|
| 38  | `companion9'_trace_pow` | `Tr((companion9' q)^k) = ∑ z∈q.roots, z^k` (K alg. closed, q monic sep. deg 9) |
| 81  | `companion9'_trace_aeval` | `Tr(aeval (companion9' q) φ) = ∑ z∈q.roots, φ.eval z` |
| 106 | `companion9'_charpoly_aeval_eq_prod` | charpoly = `∏ z∈q.roots, (X - C (φ.eval z))` |
| 160 | `companion9_aeval_map_eq_complex` | `(aeval (companion9' q) φ).map (ℚ→ℂ) = aeval (companion9' (q.map _)) (φ.map _)` |
| 176 | `companion9_trace_pow_aeval` | complex trace of a power = sum of powers of `φ.eval z` |
| 199 | `esymm_eq_zero_of_powerSums_two` | `p₁ = p₂ = 0 ⇒ e₁ = e₂ = 0` over ℂ |
| 216 | `charpoly_aeval_coeff_8_7_eq_zero` | `Tr N = Tr N² = 0 ⇒ charpoly.coeff 8 = 0 ∧ coeff 7 = 0` |
| 284/288/292/300/310 | `hermiteForm9`, `polyOfVec9`, `aeval_polyOfVec9`, `..._sq`, `trace_aeval_polyOfVec9_sq` | Hermite form machinery, `Tr((aeval M (polyOfVec9 v))²) = hermiteForm9 q v` |
| 332/335 | `ps9`, `gramTraceZero` | `s_m = Tr(M^m)`; `G_{ij} = s_{i+j+2} - s_{i+1}s_{j+1}/9` |
| 339 | `traceZeroPol` | `v ↦ ∑_k v_k X^{k+1} - C((∑_k v_k s_{k+1})/9)` |
| 344/353/361 | `natDegree_sum_shift_le`, `traceZeroPol_natDegree_le`, `coeff_traceZeroPol` | deg ≤ 6 and `coeff (k+1) = v k` |
| 373/382/390 | `aeval_sum_shift`, `trace_aeval_sum_shift`, `trace_traceZeroPol` | `Tr(traceZeroPol q v) = 0` |
| 403 | `sum_shift_sq` | `(∑ C(v k) X^{k+1})² = ∑∑ C(v i v j) X^{i+j+2}` |
| **414** | **`trace_sq_traceZeroPol`** | **Gap 1: `Tr((aeval M (traceZeroPol q v))²) = ∑∑ v i * G i j * v j`** |
| 482 | `gramTraceZero_symm` | `(gramTraceZero q)ᵀ = gramTraceZero q` |
| 491 | `exists_tschirnhaus9_of_isotropic` | the `ψ = X` reduction (kept; valid only when that form is indefinite) |
| 510 | `TschirnhausDatum` | `∃ ψ f, deg ≤ 6, nonconstant, `Tr N = Tr N² = 0` for `N = f(ψ x)` |
| **517** | **`exists_tschirnhaus9_of_isotropic_comp`** | the target conclusion from a **general** `ψ` with trace-isotropic `f(ψ x)` |
| 532 | `exists_tschirnhaus9_of_datum` | `TschirnhausDatum q →` the target conclusion |

## What remains to close `exists_tschirnhaus9`

Exactly one mathematical input, in corrected form:

> There exist `ψ, f ∈ ℚ[X]`, both nonconstant of degree `≤ 6`, such that
> `Tr N = Tr N² = 0` for `N = aeval (companion9' q) (f.comp ψ)`.
> Equivalently (`exists_tschirnhaus9_of_datum`), `TschirnhausDatum q`.

The plan's route to this is `NOTES-nonic-meyer.md` §2.2/§4:
* `r₂ ≥ 3`: `ψ = X`, dimension count on Hermite's signature `(8 - r₂, r₂)` of
  `{Tr = 0}`;
* `r₂ ∈ {1,2}`: choose real `ψ` with two real-root collisions, use interpolation to make
  the form indefinite, then round `ψ` to `ℚ⁷` by openness + density.

Both need either Hermite's signature theorem for the trace form or the openness/density
argument over `ℝ⁷`; neither is currently formalised.  The `ψ = X` shortcut is **not**
available (counterexample above).

## Closing the target (once the datum is available)

`Pptc/Nonic.lean` would `import Pptc.NonicMeyer` and replace the `sorry` with
`exists_tschirnhaus9_of_datum hmon h9 hsep <datum>`.  (`NonicMeyer.lean` imports
`Pptc.NonicPowerLaw`/`Pptc.NonicRecovery`, so there is no import cycle; and
`Pptc.HasseMinkowski.Main` is only needed if one insists on going through `meyer`.)

## Environment notes

- `lake env lean` / `lake_check` intermittently fails **before reading this file**, on
  random toolchain files (`failed to read file '…/Init/Data/…/….olean.private'`); the
  files exist and are non-empty.  Environment/file-locking issue, not a file problem.
- `lean_diagnostic_messages Pptc/NonicMeyer.lean` reports `success: true`, zero
  errors/warnings.
- `Pptc/Nonic.lean` untouched; its single `sorry` remains.
