# HANDOFF: WP5 HighRank.lean toolkit

Goal: rewrite `Pptc/HasseMinkowski/HighRank.lean` as WP5 toolkit.
- WP5.1: `isotropic_weightedSumSquares_three_units`, `isotropic_of_three_units`
- WP5.2: `isSquare_div_of_close_real`, `isSquare_div_of_close_padic`, `exists_rat_close_vec`

Target file: `Pptc/HasseMinkowski/HighRank.lean`, namespace `Pptc.HasseMinkowski.HighRank`.

Plan: read Plan-v3 WP4/WP5 + reference files, then build up.

## Log
- read plan/reference files next
- Read Plan-v3 WP4/WP5, RankCriteria outline, Local.lean. Next: Padic.lean, Squares, RatApproximation.
- Read Squares.lean (`isSquare_of_dist_one_lt_one`, `..._pow`), RatApproximation (`approximation'`, `norm_sub_le`). `hilbertSym_padicInt_units` at Padic.lean:172.
- NOTE: stated `isotropic_of_three_units` with `w : ι → ℚ_[p]` and `IsUnit (w (u j))` is mathematically FALSE (IsUnit in a field = nonzero; ⟨1,1,1⟩ anisotropic over ℚ_2). Will deliver integral-unit version.
- NOTE2: stated `isSquare_div_of_close_padic` FALSE for p=2 (a₀=1,a=2: ‖1‖<1 but 2 not square). Will split odd/even: odd with given hyp, p=2 with `< 2^-2`.
- `Real.isSquare_iff` in Mathlib.Data.Real.Sqrt. Legendre outline timed out; skip. Next: write draft.
- Wrote full draft of HighRank.lean (5 declarations). Next: diagnostics.
- First diagnostics: 7 errors. Fixed: deprecated import -> Mathlib.Analysis.Real.Sqrt; norm rewrite; Ne.symm; `Padic.isSquare_of_dist_one_lt_one (p:=p)`; `(-u2)*u0` shape; TYPE ERROR in task: `ℚ_[p] ^ (Fin 2)` must be `Fin 2 → ℚ_[p]`. Re-diagnosing.
- Second diagnostics: 2 errors (`Finset.single_le_sum` needs explicit `f :=`). Fixed. Now success:true, no diagnostics.
- Added `isotropic_of_three_units_int` (integral weights, literal `IsUnit`). Still clean.
- Next: lake_check final.
- `lake_check` attempt 1+2: "failed to read ...Vandermonde.olean.private"; attempt 3: INTERNAL PANIC: out of memory. attempt 4/5: "failed to read ...olean.private" (toolchain / Jacobson). OOM/IO symptoms under memory pressure (a sibling subagent's lean worker held 2 GB). LSP diagnostics (warm) = success, zero diagnostics; `lean_verify` gives {propext, Classical.choice, Quot.sound}.
- `lake_check` FINAL (after sibling worker freed memory): "OK - no errors or warnings." DONE.

## Final declarations (all in `Pptc.HasseMinkowski`, file compiles clean)
- L42  `isotropic_weightedSumSquares_three_units` (exactly as requested)
- L71  `isotropic_of_three_units` (w : ι → ℚ_[p], ∃ unit witness)
- L126 `isotropic_of_three_units_int` (w : ι → ℤ_[p], literal `IsUnit`)
- L136 `isSquare_div_of_close_real` (exactly as requested)
- L154 `isSquare_div_of_close_padic` (odd p; added `hp : p ≠ 2`)
- L165 `isSquare_div_of_close_padic_two` (p=2, threshold 2⁻²)
- L174 `local instance factPrimeOfPrimesHighRank`
- L183 `exists_rat_close_vec` (`Fin 2 → ℚ_[p]`, not the invalid `^`)

## Statement adjustments (all forced; see summary)
- `IsUnit (w (u j))` for `w : ι → ℚ_[p]` is `w (u j) ≠ 0` (field), and the claim is FALSE
  (⟨1,1,1⟩ is anisotropic over ℚ_2). Replaced by an explicit `ℤ_[p]ˣ` witness; added the
  integral-weight variant for the literal `IsUnit` form.
- `isSquare_div_of_close_padic` is FALSE for p = 2 (a₀=1, a=2); split off the p=2 case with
  `‖a-a₀‖ < 2⁻²‖a₀‖`.
- `ℚ_[p] ^ (Fin 2)` does not typecheck (no `HPow Type Type`); used `Fin 2 → ℚ_[p]`.

---

# ROUND 2: WP5.3 `diagonal_hm_five_le`

Goal: prove, in the same file,
`diagonal_hm_five_le (h4 : RankFourDiagonalHM) : ∀ {n}, 5 ≤ n → ∀ w : Fin n → ℚ, ...`
plus general-index `isotropic_of_five_le_card`.

Plan: strong induction on n (base n=4 via h4); split `w = ![w0,w1] ⊞ rest`;
local places S = primes | some w_i, plus 2, plus ∞; `iso_prod_neg` for a_v; weak
approximation + openness; good primes use `isotropic_of_three_units`.

## Round-2 log
- Read RankFourDiagonalHM def (HighRank.lean L225), Prod.lean helpers
  (`prod_isotropic_iff` L280, `iso_prod_neg` L371, `represents_of_isotropic_nondegenerate` L328).
- Next: find reindexing/prod lemmas for `weightedSumSquares`.
- Found: `PadicInt.mkUnits`/`mkUnits_eq` (norm-1 -> unit), `PadicInt.isUnit_iff`. `badPrimes` in Reciprocity is `private` -> define own.
- Design: h := wss ![w0,w1]; g0 := wss (w(j+2)); local common value via
  `prod_isotropic_iff` on `h.prod g0` + `represents_of_isotropic_nondegenerate`.
  W := Fin.cons (-a) (fun j => -w(j+2)); IH gives W isotropic; extract.
- Writing helper batch 1: sum_fin_add_two, wss_add_two_val, prod_isotropic_of_wss,
  wss_tail_isotropic, nondegenerate_wss_of_ne, exists_local_common_value.
- Batch 1 + `exists_local_common_value` + `exists_rat_close_vec'` +
  `exists_padicUnit_of_norm_eq_one` + `wss_pair_close` all COMPILE (LSP green).
  NOTE: `x∞` is not a legal identifier (`∞` is a notation token); use `xr`.
- Remaining for full WP5.3: (a) place set `smallPrimes` + "p ∉ S ==> `(w i : ℚ_[p])`
  is an integral unit" (via `padicNorm.nat_eq_one_iff` on num/den);
  (b) value-approximation lemma choosing a common tolerance
  `ε := 1/(1 + Σ_{c ∈ cand} c)` over `cand = {1, 1/ηR} ∪ {1/ηP p}` (this sum trick
  avoids `Finset.min'` positivity), then `wss_pair_close` + `isSquare_div_of_close_*`;
  (c) final assembly with `Fin.cons (-a) (fun j => -w (j+2))` and IH; (d) `Fintype.equivFin`
  reindexing for `isotropic_of_five_le_card`.
- NOT DELIVERED: `diagonal_hm_five_le`, `isotropic_of_five_le_card`.
- FINAL `lake_check Pptc/HasseMinkowski/HighRank.lean`: **OK - no errors or warnings.**
  No `sorry`/`axiom`. File compiles with all 9 WP5.3 helper lemmas.

## Status: PARTIAL
Delivered (all proved, LSP + lake_check green):
  L241 `sum_fin_add_two`, L249 `wss_add_two_val`, L260 `prod_isotropic_of_wss`,
  L278 `wss_tail_isotropic`, L291 `nondegenerate_wss_of_ne`,
  L306 `exists_local_common_value`, L332 `exists_rat_close_vec'`,
  L353 `exists_padicUnit_of_norm_eq_one`, L365 `wss_pair_close`.
Not delivered: `diagonal_hm_five_le`, `isotropic_of_five_le_card`.

## Remaining recipe (for the next worker)
1. **Place set** `S : Finset Nat.Primes := insert 2 (primes ≤ N)` with
   `N := 2 + max_i ((w i).num.natAbs + (w i).den)`.  Then `p ∉ S` ==> `(p:ℕ) ≠ 2`,
   `p > (w i).num.natAbs`, `p > (w i).den` for all `i`, hence (via
   `padicNorm.nat_eq_one_iff` and `Rat.num_div_den` + `norm_div`) `‖(w i : ℚ_[p])‖ = 1`.
   Conclude an integral unit witness with `exists_padicUnit_of_norm_eq_one`, then
   `isotropic_of_three_units` (odd `p`, `Fin 3 ↪ Fin (n-2)`) gives `g₀_p` isotropic.
2. **Value approximation** `exists_rat_value_close {w2 : Fin 2 → ℚ} ...` (state with
   `w2` to avoid coercions): hypotheses `hxa : ∀ p, (wss ℚ_[p] (fun i => (w2 i : ℚ_[p])))
   (x p) = a p`, `hxr` likewise over ℝ; conclusion `∃ q, (wss ℚ w2) q ≠ 0 ∧
   IsSquare(((wss ℚ w2) q : ℝ)/ar) ∧ ∀ p, IsSquare(((wss ℚ w2) q : ℚ_[p])/a p)`.
   Proof: let `Br := 1+‖xr 0‖+‖xr 1‖`, `Cr := ‖w2 0‖_ℝ+‖w2 1‖_ℝ`, `Bp p`, `Cp p`,
   `thrP p := if (p:ℕ)=2 then 2^(-2)*‖a p‖ else ‖a p‖`, `η := thr/(C*(1+2B)+1)`; take
   `ε := 1/(1 + Σ_{c∈{1,1/ηR}∪{1/ηP p}} c)` (positivity + `ε ≤ each η` via
   `Finset.single_le_sum`; avoids `Finset.min'`).  `exists_rat_close_vec' hεpos`, then
   `wss_pair_close` + `wss_cast_val` (base change: prove
   `((wss ℚ v) z : K) = (wss K (fun i => (v i : K))) (fun i => (z i : K))` by
   `simp only [weightedSumSquares_apply, Fin.sum_univ_two, smul_eq_mul]; push_cast; ring`),
   then `isSquare_div_of_close_real` / `isSquare_div_of_close_padic` (p odd,
   `rw [h2] at hbp ⊢` for p=2) / `isSquare_div_of_close_padic_two`.  `q ≠ 0`-value from
   `‖h(q)-ar‖ < ‖ar‖` (a = 0 contradicts).
3. **Assembly**: `exists_local_common_value` at each `p ∈ S` and at ℝ gives `a_v ≠ 0`,
   `h rep a_v`, `g₀ rep -a_v`; with `x_v`; feed (2) to get `q`, `A := (wss ℚ w2) q ≠ 0`
   with `A/a_v` a square; set `W := Fin.cons (-A) (fun j => -w (j.succ.succ))`.
   `weightedSumSquares ℚ W` isotropic at each `p` (S: from `g₀_p rep -A`, via
   `-A·1² + (-g₀)(y) = 0`; p∉S: `g₀_p` isotropic) and at ℝ; IH (rank `n-1 ≥ 4`, base
   `h4` at 4) gives `W` isotropic over ℚ; `Fin.sum_univ_succ` extracts `u`;
   `u 0 = 0` ==> `g₀` isotropic ==> `wss_tail_isotropic`; `u 0 ≠ 0` ==> `g₀ rep -A`,
   combine with `h rep A` (vector `Fin.cons (q 0) (Fin.cons (q 1) y)`).
4. **General index**: reindex by `Fintype.equivFin ι` (a linear isometry
   `(ι → ℚ) ≃ₗ (Fin n → ℚ)` sending `w` to `w ∘ e.symm`), then apply the `Fin n` version.
