# HANDOFF — nonic (WP6.4): `Pptc.Nonic.exists_tschirnhaus9`

Target (unchanged, still the only `sorry` in the library):
`Pptc/Nonic.lean:31` `Pconstructible.exists_tschirnhaus9`.

New file: `Pptc/NonicMeyer.lean` (sorry-free, compiles clean per LSP diagnostics).
`Pptc/Nonic.lean` was deliberately **not** modified.

## What is now proved (file `Pptc/NonicMeyer.lean`, line numbers)

| line | declaration | statement |
|---|---|---|
| 37  | `companion9'_trace_pow` | over alg. closed `K`: `Tr((companion9' q)^k) = ∑ z∈q.roots, z^k` (q monic sep. deg 9) |
| 80  | `companion9'_trace_aeval` | `Tr(aeval (companion9' q) φ) = ∑ z∈q.roots, φ.eval z` |
| 105 | `companion9'_charpoly_aeval_eq_prod` | `(aeval (companion9' q) φ).charpoly = ∏ z∈q.roots, (X - C (φ.eval z))` |
| 159 | `companion9_aeval_map_eq_complex` | `(aeval (companion9' q) φ).map (ℚ→ℂ) = aeval (companion9' (q.map _)) (φ.map _)` |
| 175 | `companion9_trace_pow_aeval` | `(Tr((aeval (companion9' q) φ)^k) : ℂ) = ∑ z∈(q.map _).roots, (φ.map _).eval z ^ k` |
| 198 | `esymm_eq_zero_of_powerSums_two` | `p₁ = p₂ = 0 ⇒ e₁ = e₂ = 0` for a multiset over ℂ |
| 215 | `charpoly_aeval_coeff_8_7_eq_zero` | **the reduction**: q monic sep. deg 9, `Tr(aeval M φ)=Tr((aeval M φ)²)=0 ⇒ charpoly.coeff 8 = 0 ∧ coeff 7 = 0` |
| 283 | `hermiteForm9` | trace form on degree-≤6 polynomials in the monomial basis |
| 287 | `polyOfVec9` | coefficient-vector polynomial |
| 291/299/309 | `aeval_polyOfVec9`, `..._sq`, `trace_aeval_polyOfVec9_sq` | `Tr((aeval M (polyOfVec9 v))²) = hermiteForm9 q v` |
| 331 | `ps9` | `s_m = Tr((companion9' q)^m)` |
| 334 | `gramTraceZero` | proposed Gram matrix of the trace form on `{deg ≤ 6, Tr = 0}` in the parametrisation below |
| 338 | `traceZeroPol` | `v ↦ ∑_k v_k X^{k+1} - C((∑_k v_k s_{k+1})/9)`, `k : Fin 6` |
| 343/352 | `natDegree_sum_shift_le`, `traceZeroPol_natDegree_le` | `(traceZeroPol q v).natDegree ≤ 6` |
| 360 | `coeff_traceZeroPol` | `(traceZeroPol q v).coeff (k+1) = v k` |
| 372/381 | `aeval_sum_shift`, `trace_aeval_sum_shift` | `aeval M (∑ C(v k) X^{k+1}) = ∑ v k • M^{k+1}`, its trace `= ∑ v k s_{k+1}` |
| 389 | `trace_traceZeroPol` | `Tr(aeval M (traceZeroPol q v)) = 0` |
| 400 | `exists_tschirnhaus9_of_isotropic` | **the full Tschirnhaus conclusion** from `∃ f, 1 ≤ deg f ≤ 6, Tr f = Tr f² = 0` |

## The remaining gap (exactly two facts; nothing else)

Both are stated in the `/-! ### The remaining gap -/` comment at the end of
`Pptc/NonicMeyer.lean`.

1. **Gram identification** (pure algebra, `Fin 6` bookkeeping over ℚ):
```lean
theorem trace_sq_traceZeroPol (q : ℚ[X]) (v : Fin 6 → ℚ) :
    Matrix.trace ((aeval (companion9' q) (traceZeroPol q v)) ^ 2)
      = ∑ i, ∑ j, v i * gramTraceZero q i j * v j
```
   Proof route: write `traceZeroPol q v = p - C c` with `p = ∑ C(v k) X^{k+1}`,
   `c = (∑ v k s_{k+1})/9`; expand `(p - C c)^2` in the *commutative* ring `ℚ[X]`,
   then use `trace_aeval_sum_shift`, `Tr(1) = 9`, and `p^2 = ∑∑ C(v i v j) X^{i+j+2}`.
   (I had this fully designed but ran out of step budget; it is ~40 lines of `Finset`
   manipulation.)

2. **Indefiniteness of the trace form** (the mathematical heart; needs Hermite's
   signature theorem, not in Mathlib at 4.33):
```lean
theorem indefinite_gramTraceZero (q : ℚ[X]) (hmon : q.Monic) (h9 : q.natDegree = 9)
    (hsep : q.Separable)
    (hrel : ∃ z : ℂ, (q.map (algebraMap ℚ ℂ)).eval z = 0 ∧ z.im ≠ 0) :
    Indefinite (QuadraticForm.baseChange ℝ (Matrix.toQuadraticForm' (gramTraceZero q)))
```
   - `r₂ ≥ 3` (`r₂` = #conjugate pairs): `ψ = X`; `V = {deg ≤ 6, Tr = 0}` has positive
     index `≤ 8 - r₂ ≤ 5 < 6` and negative index `≤ r₂ ≤ 4 < 6`, so the form is neither
     definite; indefinite-or-radical gives the isotropic vector (Meyer for the indefinite
     case, radical otherwise). See `NOTES-nonic-meyer.md` §4.
   - `r₂ ∈ {1,2}`: the real-collision/interpolation + openness/density argument,
     `NOTES-nonic-meyer.md` §2.2/§5.

## Closing the target

Given (1) and (2):
```lean
-- V := Fin 6 → ℚ, Q := Matrix.toQuadraticForm' (gramTraceZero q)
-- finrank ℚ V = 6, so 5 ≤ finrank
obtain ⟨v, hvne, hv0⟩ := Pptc.HasseMinkowski.meyer Q (by norm_num) (indefinite_… q …)
-- trace_sq_traceZeroPol turns hv0 : Q v = 0 into Tr((traceZeroPol q v)²) = 0
-- trace_traceZeroPol gives Tr(traceZeroPol q v) = 0
-- coeff_traceZeroPol + hvne give 1 ≤ (traceZeroPol q v).natDegree
exact exists_tschirnhaus9_of_isotropic hmon h9 hsep ⟨traceZeroPol q v, …, …⟩
```
Then `Pptc/Nonic.lean` would `import Pptc.NonicMeyer` (note: `NonicMeyer.lean` currently
imports `Pptc.Nonic`, so this needs the import flipped to `Pptc.NonicResolvent` to avoid a
cycle) and replace the `sorry` by the one-liner above.

## Environment notes

- `lake env lean Pptc/NonicMeyer.lean` (and `lake_check`) currently fails **before reading
  my file**, on random toolchain files: `failed to read file
  '.../lib/lean/Init/Data/…/….olean.private'` (three different files on three attempts;
  the files exist and are non-empty). This is an environment/file-locking issue, not a
  problem in `NonicMeyer.lean`.
- `lean_diagnostic_messages Pptc/NonicMeyer.lean` reports `success: true`, zero
  errors/warnings, so the file elaborates against the warm LSP environment.
- `Pptc/Nonic.lean` untouched; its single `sorry` remains.
