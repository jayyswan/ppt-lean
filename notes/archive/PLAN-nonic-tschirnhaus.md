# PLAN — closing `exists_tschirnhaus9` (corrected nonic Tschirnhaus route)

This plan replaces the plan's "Gap 2" and §2.2/§4/§5 of `NOTES-nonic-meyer.md` as the **Lean route**.
The mathematics in the notes is not wrong. The problem is that the Lean breakdown asked for
more than the notes claim, and the notes' own route needs Hermite's signature theorem, which
this plan avoids.

Target: `Pptc/Nonic.lean:31` `Pconstructible.exists_tschirnhaus9`. It is the only `sorry` in
the library.

---

## 0. What went wrong, and what survives

`HANDOFF-nonic.md` (DeepSeek) tried to prove "Gap 2": with `ψ = X`, the trace form on
`{f : deg f ≤ 6, Tr f = 0}` (`gramTraceZero q`) is indefinite. **This is false.** For
`q = (X²+1)(X+13)(X+12)(X+3)(X+2)(X−2)(X−8)(X−11)` all six leading principal minors of
`gramTraceZero q` are positive: `504, 17062416, 7177780688000, 1120883224656340000000/9,
109927918051745733200000000000, 705355934905388066193936000000000000000`. Claude
re-verified these with exact sympy arithmetic. This matches the notes, which only claim
`ψ = X` works when `r₂ ≥ 3`.

**Still valid and reused** (all in `Pptc/NonicMeyer.lean`, sorry-free):
`companion9'_trace_aeval`, `companion9_trace_pow_aeval`, `charpoly_aeval_coeff_8_7_eq_zero`,
`polyOfVec9`, `traceZeroPol`, `trace_traceZeroPol`, `trace_sq_traceZeroPol` (the Gram
identity), `TschirnhausDatum`, `exists_tschirnhaus9_of_datum`.

**Dropped:** Hermite's signature theorem, the `r₂ ≥ 3` / `r₂ ∈ {1,2}` case split, the
"radical" branch of notes §4, and every irreducibility or `dim V_ψ = 6` requirement.

## 1. The corrected argument (one case, any `r₂ ≥ 1`)

Notation: `M = companion9' q`, `R = roots of q in ℂ` (9 distinct), `z ∈ R` nonreal (from `hrel`).
For real `ψ = Σ_{j≤6} ψ_j Y^j` and `v ∈ ℝ⁶`, put `g(ρ) = Σ_k v_k ψ(ρ)^{k+1}` and

    spread(ψ, v) = Re( Σ_{ρ∈R} g(ρ)² − (Σ_{ρ∈R} g(ρ))² / 9 ).

For rational `ψ, v`, this equals `Tr(N²) − (Tr N)²/9` with `N = p_v(ψ(M))`, i.e. the Gram form
`vᵀ · gramOf(ψ(M)) · v`.

1. **Real witness.**
   - `q_ℝ = P · R₇` with `P = (x−z)(x−z̄)`. Since irreducible real polynomials have degree `≤ 2`,
     `R₇` has a monic real divisor `D` with `3 ≤ deg D ≤ 4`. Also `D(z) ≠ 0`.
   - Put `ψ₀ = (x − t)·D`, `deg ψ₀ ≤ 5`. The roots of `D` (at least 3 of them) all map to `0`,
     so the node set `N = ψ₀(R) ∪ {0}` has `|N| ≤ 7`.
   - Choose `t ∈ ℝ` so that (a) `w := ψ₀(z) ∉ ℝ` and (b) `ψ₀(ρ) ≠ w` for all `ρ ∈ R, ρ ≠ z`.
     Each bad condition is linear in `t` with at most one solution, so the bad set is finite.
     - (a): `Im((z−t)D(z)) = Im(zD(z)) − t·Im D(z)`. If `Im D(z) = 0` then
       `Im(zD(z)) = Im z · D(z) ≠ 0`.
     - (b): `t(D(ρ)−D(z)) = ρD(ρ) − zD(z)`. If `D(ρ) = D(z)`, the right side is
       `(ρ−z)D(z) ≠ 0`.
   - `N` is closed under conjugation. Interpolate at `N` over `ℂ` and take real parts of the
     coefficients; this gives a real `F`, `deg F ≤ 6`, with prescribed targets on `N`
     whenever `r(ν̄) = conj r(ν)`.
     - `r₋`: `i` at `w`, `−i` at `w̄`, `0` elsewhere gives `spread = −2`.
     - `r₊`: `1` at `w` and `w̄`, `0` elsewhere gives `spread = 2 − 4/9 = 14/9`.
   - Drop `F`'s constant term. `spread` is invariant under `g ↦ g + c` because `|R| = 9`.

   *Checked exactly on the counterexample, with `t = 1/2` and `D = (x+13)(x+12)(x+3)`:* both
   interpolants are real of degree 6, and `spread = −2` and `14/9`. The rational `ψ₀` there
   already has an indefinite Gram matrix.
2. **Round.** `spread` is continuous on `ℝ⁷ × ℝ⁶`, and `ℚ⁷×ℚ⁶×ℚ⁶` is dense. The set
   `{spread(ψ,v₋) < 0 < spread(ψ,v₊)}` is open and nonempty, so it has a rational point.
3. **Meyer.** For rational `ψ`, `A := aeval M ψ`, the form `v ↦ vᵀ gramOf(A) v` on `ℚ⁶` takes both
   signs (step 2 plus the link), so its base change to `ℝ` is `Indefinite`. `meyer` then gives
   `v ≠ 0` isotropic. Take `f := tzPolOf A v`:
   - `1 ≤ deg f ≤ 6`, because `coeff (k+1) = v k`;
   - `aeval M (f.comp ψ) = aeval A f`, so `Tr = 0` and `Tr² = 0`;
   - `ψ` is nonconstant, since for `ψ = c` we get `gramOf A = 0`, contradicting the negative
     value.

   This yields `TschirnhausDatum q`, and `exists_tschirnhaus9_of_datum` finishes.

## 2. Work packages

One deliverable per `@lean-prover` call. Each call keeps its own log `HANDOFF-nonic-WPn.md` at
the repo root. Iterate with `lean_diagnostic_messages`, and run `lake_check` only once at the
end. WP1 and WP2 can run in parallel (different files). WP3 needs only the *statement* of WP2
(take it as a hypothesis). WP4 comes last.

### WP1 — generalised Gram + Meyer ⇒ datum (`Pptc/NonicMeyer.lean`)
Generalise the ψ = X apparatus from `companion9' q` to an arbitrary `A : Matrix (Fin 9) (Fin 9) ℚ`.
The existing proofs use nothing about `M` beyond traces of powers, so this is mostly renaming.
```lean
def psOf (A : Matrix (Fin 9) (Fin 9) ℚ) (m : ℕ) : ℚ := Matrix.trace (A ^ m)
def gramOf (A) : Matrix (Fin 6) (Fin 6) ℚ :=
  fun i j => psOf A (i+j+2) - psOf A (i+1) * psOf A (j+1) / 9
noncomputable def tzPolOf (A) (v : Fin 6 → ℚ) : ℚ[X] :=
  (∑ k, C (v k) * X ^ (k.val+1)) - C ((∑ k, v k * psOf A (k.val+1)) / 9)
theorem trace_tzPolOf (A v) : Matrix.trace (aeval A (tzPolOf A v)) = 0
theorem trace_sq_tzPolOf (A v) :
    Matrix.trace ((aeval A (tzPolOf A v)) ^ 2) = ∑ i, ∑ j, v i * gramOf A i j * v j
-- also the unprojected form, used by WP4:
theorem gram_eq_trace_shift (A v) : ∑ i, ∑ j, v i * gramOf A i j * v j =
    Matrix.trace ((aeval A p) ^ 2) - (Matrix.trace (aeval A p)) ^ 2 / 9
  -- where p = ∑ k, C (v k) * X ^ (k.val+1)
theorem tschirnhausDatum_of_signs {q ψ : ℚ[X]} (hψ : ψ.natDegree ≤ 6)
    (hneg : ∃ v, ∑ i, ∑ j, v i * gramOf (aeval (companion9' q) ψ) i j * v j < 0)
    (hpos : ∃ v, 0 < ∑ i, ∑ j, v i * gramOf (aeval (companion9' q) ψ) i j * v j) :
    TschirnhausDatum q
```
- Redefine `ps9 q := psOf (companion9' q)` and `gramTraceZero q := gramOf (companion9' q)` so the
  old lemmas and the counterexample docs survive. Do not delete `exists_tschirnhaus9_of_isotropic`.
- Meyer: `Q := Matrix.toQuadraticForm' (gramOf A)` on `Fin 6 → ℚ`, and `finrank = 6`
  (`Module.finrank_fin_fun`). For indefiniteness of `Q.baseChange ℝ`, evaluate at `1 ⊗ₜ v`
  (look up `QuadraticForm.baseChange_tmul`). Check that `toQuadraticForm'` agrees with the
  `∑∑` form. Add `import Pptc.HasseMinkowski.Main`.
- Nonconstant `ψ`: if `ψ.natDegree = 0` then `A = c • 1`, `psOf A m = 9 c^m`, `gramOf A = 0`.

### WP2 — real witness (`Pptc/NonicWitness.lean`, new; Mathlib imports only)
```lean
noncomputable def spread (q : ℚ[X]) (ψ : Fin 7 → ℝ) (v : Fin 6 → ℝ) : ℝ :=
  let g : ℂ → ℂ := fun z =>
    ∑ k : Fin 6, (v k : ℂ) * (∑ j : Fin 7, (ψ j : ℂ) * z ^ (j : ℕ)) ^ (k.val + 1)
  let R := (q.map (algebraMap ℚ ℂ)).roots
  ((R.map fun z => g z ^ 2).sum - (R.map g).sum ^ 2 / 9).re

theorem exists_real_signs {q : ℚ[X]} (hmon : q.Monic) (h9 : q.natDegree = 9)
    (hsep : q.Separable)
    (hrel : ∃ z : ℂ, (q.map (algebraMap ℚ ℂ)).eval z = 0 ∧ z.im ≠ 0) :
    ∃ (ψ : Fin 7 → ℝ) (v₋ v₊ : Fin 6 → ℝ), spread q ψ v₋ < 0 ∧ 0 < spread q ψ v₊
```
Suggested sub-lemmas (split into separate calls if one stalls):
1. `exists_real_divisor`: `∃ D : ℝ[X], D.Monic ∧ 3 ≤ D.natDegree ∧ D.natDegree ≤ 4 ∧
   D ∣ q.map (algebraMap ℚ ℝ) ∧ (D.map ofReal).eval z ≠ 0`.
   - Use `Irreducible.natDegree_le_two` and `WfDvdMonoid.exists_irreducible_factor` two or three
     times on the cofactor of `X² − C(2 z.re) X + C(normSq z)`.
   - `D(z) ≠ 0` because `z` is a simple root of `q` that is already a root of `P`.
2. Root bookkeeping: `q_ℂ = D_ℂ · E_ℂ`, `roots = roots D_ℂ + roots E_ℂ` (`Polynomial.roots_mul`),
   and `card (roots E_ℂ) = 9 − deg D ≤ 6`. So `(R.map ψ₀.eval).toFinset ∪ {0}` has `card ≤ 7`.
   `R` is `Nodup` (`nodup_roots` of separable), has `card = 9`, and is closed under `conj`
   (`q` has real coefficients).
3. `exists_good_t`: `t : ℝ` avoiding the finite bad set of §1 (a),(b).
4. `exists_real_interp (N : Finset ℂ) (hN : N.card ≤ 7) (hc : ∀ ν ∈ N, conj ν ∈ N)
   (r : ℂ → ℂ) (hr : ∀ ν ∈ N, r (conj ν) = conj (r ν)) :
   ∃ c : Fin 7 → ℝ, ∀ ν ∈ N, ∑ k, (c k : ℂ) * ν ^ (k : ℕ) = r ν`.
   - Build `L := Lagrange.interpolate N id r` (`eval_interpolate_at_node`,
     `degree_interpolate_lt`) and set `c k := (L.coeff k).re`.
   - At `ν`: `Σ re(c_k) ν^k = (L(ν) + conj(L(conj ν)))/2 = r ν`. No uniqueness argument needed.
5. `spread_add_const`: shifting `g` by a constant leaves `spread` unchanged (uses `card R = 9`).
   This lets the witness use `F` with a constant term, then pass `v k := c (k+1)`.
6. Evaluate the two sums: only `ρ = z, z̄` hit `w, w̄` (for `ψ₀ ρ = w̄` conjugate to get
   `conj ρ = z`), giving `−2` and `14/9`.

### WP3 — density (`Pptc/NonicWitness.lean`, after or alongside WP2)
```lean
theorem continuous_spread (q) : Continuous fun p : (Fin 7 → ℝ) × (Fin 6 → ℝ) => spread q p.1 p.2
theorem exists_rat_signs {q : ℚ[X]}
    (h : ∃ (ψ : Fin 7 → ℝ) (v₋ v₊ : Fin 6 → ℝ), spread q ψ v₋ < 0 ∧ 0 < spread q ψ v₊) :
    ∃ (ψ : Fin 7 → ℚ) (v₋ v₊ : Fin 6 → ℚ),
      spread q (fun j => ψ j) (fun k => v₋ k) < 0 ∧ 0 < spread q (fun j => ψ j) (fun k => v₊ k)
```
- Continuity: `fun_prop`, with `continuous_multiset_sum` or a rewrite to a `Finset` sum if
  needed.
- Density: `Rat.denseRange_cast`, pushed through `Pi`/`Prod` (`DenseRange.piMap`,
  `DenseRange.prodMap`, or whatever loogle finds), then `DenseRange.exists_mem_open`.

### WP4 — link and assembly (`Pptc/NonicMeyer.lean` or a new `Pptc/NonicTschirnhaus.lean`)
```lean
theorem spread_rat_cast {q : ℚ[X]} (hmon) (h9) (hsep) (ψ : Fin 7 → ℚ) (v : Fin 6 → ℚ) :
    spread q (fun j => ψ j) (fun k => v k)
      = ((∑ i, ∑ j, v i * gramOf (aeval (companion9' q) (polyOfVec9 ψ)) i j * v j : ℚ) : ℝ)
theorem tschirnhausDatum_of_nonreal (hmon) (h9) (hsep) (hrel) : TschirnhausDatum q
```
- Link: `gram_eq_trace_shift`, `Polynomial.aeval_comp`, `companion9_trace_pow_aeval`
  (`k = 1, 2`) for `φ = p_v.comp (polyOfVec9 ψ)`, then `Complex.ofReal` casts and `.re`.
  `polyOfVec9_natDegree_le` may need a one-line lemma.
- Then in `Pptc/Nonic.lean`: import the assembly file and replace the `sorry` with
  `exists_tschirnhaus9_of_datum hmon h9 hsep (tschirnhausDatum_of_nonreal hmon h9 hsep hrel)`.
  Confirm with `lean_verify Pconstructible.root_Pconstructible_of_rat_nonic_nonreal`
  (only `propext`, `Classical.choice`, `Quot.sound`).

## 3. Risks

- **Imports / oleans.** Memory notes that full `lake build` is broken and new modules are
  verified through the LSP. For `Nonic.lean` to import the chain, run
  `lake build Pptc.NonicMeyer` (then `Pptc.NonicWitness`), one target at a time and never
  chained. Do this *before* WP4. If a module cannot produce an `.olean`, fall back to putting
  WP2–WP4 in the same file as WP1.
- **Memory.** `Pptc.HasseMinkowski.Main` is a heavy import. Keep WP2/WP3 free of it so they
  elaborate cheaply.
- **Casts in `spread`.** If `.re` of multiset sums gets painful, WP2 may restate `spread` as a
  `Finset` sum over `R.toFinset` (valid because `R` is nodup). Change the definition once,
  before WP3/WP4 start.
- **`toQuadraticForm'` convention.** Confirm with `lean_hover_info` whether it is `v ⬝ᵥ A *ᵥ v`
  or involves a symmetrisation factor. `gramOf` is symmetric (`gramTraceZero_symm`
  generalises), so either way it matches `∑∑`.
