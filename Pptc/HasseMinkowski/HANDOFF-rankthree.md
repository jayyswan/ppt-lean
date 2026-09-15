# HANDOFF: rank-3 Hasse–Minkowski (isotropic_of_rank_three)

Target file: `Pptc/HasseMinkowski/RankThree.lean` (namespace `Pptc.HasseMinkowski`).
Goal: `isotropic_of_rank_three` for rank-3 nondegenerate forms over ℚ, per `Targets.lean`.
Log path: `Pptc/HasseMinkowski/HANDOFF-rankthree.md`.

## Log
- [start] Created log. Read `Targets.lean`, `RankCriteria.lean`, `RankTwo.lean`, `Locally.lean`,
  `HasseInvariant.lean`, `Basic.lean`, `HilbertSymbol/{Defs,Real,Reciprocity,Existence}.lean`,
  `Scratch/win7-reference.md`, `Plan.md`.
- Recon: rank-3 criterion available and unconditional:
  `weightedSumSquares_isotropic_iff_hilbertSym_eq_one (a b c) (ha hb hc) :
     (weightedSumSquares k ![a,b,c]).Isotropic ↔ hilbertSym (-c*a) (-c*b) = 1`
  (no `HasBilinHilbertSym` needed).  `represents_zero_iff_of_rank_three_diag` DOES need
  `[HasBilinHilbertSym k]` and `hasseMinkowskiInvAux`; not used here.
- Recon: NO local-global / Hasse-norm theorem exists in the project.  `Reciprocity.lean` only
  proves reciprocity when one argument is a square and records the general statement as the
  unproved `HilbertReciprocity : Prop`.  Therefore the reverse direction
  "local symbols all 1 ⇒ global symbol 1" is genuinely missing and is the only gap.
- Decision: isolate the missing input as `HilbertSymLocalGlobal : Prop` (explicit hypothesis),
  exactly as `RankCriteria.lean` isolates `hasseMinkowskiInv.eq_of_equivalent`.  Prove the full
  reduction sorry-free.  Do NOT write a `sorry`-filled `Targets`-shaped theorem.
- [milestone] LSP diagnostics clean for the whole file (0 errors, 0 warnings).  Only fix needed
  was `exact_mod_cast hwq` → `Rat.cast_ne_zero.mpr hwq` for the base-changed weights.
- [verify] `lean_verify Pptc.HasseMinkowski.isotropic_of_rank_three` → axioms
  `{propext, Classical.choice, Quot.sound}`; no `sorry`/`admit` in the file.

## Declarations delivered (all sorry-free)

File `Pptc/HasseMinkowski/RankThree.lean`, namespace `Pptc.HasseMinkowski`:

- `def HilbertSymLocalGlobal : Prop`
  `∀ A B : ℚ, A ≠ 0 → B ≠ 0 → (∀ p [Fact p.Prime], hilbertSym (A:ℚ_[p]) (B:ℚ_[p]) = 1) →
     hilbertSym (A:ℝ) (B:ℝ) = 1 → hilbertSym A B = 1`
  This is the **missing** Hasse-norm-theorem input (only the reverse/local⇒global direction).
- `private theorem weightedSumSquares_fin3_eq` — `weightedSumSquares k ![w 0,w 1,w 2]`
  equals `weightedSumSquares k w`.
- `private theorem hilbertSym_neg_mul_of_isotropic` — reads the rank-3 criterion off an
  isotropic diagonal form with nonzero weights.
- `theorem isotropic_of_rank_three (hloc : HilbertSymLocalGlobal) (Q : QuadraticForm ℚ V)
     [FiniteDimensional ℚ V] (hr : finrank ℚ V = 3) (hQ : Q.Nondegenerate)
     (hQ' : EverywhereLocallyIsotropic Q) : Isotropic Q`  **[PROVED]**

## Proof sketch (as implemented)

1. `hQ'` splits into `hQ'f` (all `p`) and `hQ'R` (ℝ).
2. `hsep : (associated Q).SeparatingLeft` from `hQ` via `nondegenerate_associated_iff`.
3. `equivalent_weightedSumSquares_units_of_nondegenerate'` diagonalizes Q as `⟨w₀,w₁,w₂⟩`,
   `wᵢ : ℚˣ`; reindex `Fin (finrank) → Fin 3` by `rw [hr]` (RankTwo's trick).
4. `wq i := (w i : ℚ)`; `hw' : Q.Equivalent (weightedSumSquares ℚ wq)`.
5. `A := -wq 2 * wq 0`, `B := -wq 2 * wq 1`, both nonzero.
6. For each prime `p`: `hw'.baseChange` + `baseChange_weightedSumSquares` gives
   `Isotropic (weightedSumSquares ℚ_[p] (fun i => algebraMap ℚ ℚ_[p] (wq i)))` from `hQ'f p`;
   `hilbertSym_neg_mul_of_isotropic` yields the local symbol `= 1`.  Same over ℝ from `hQ'R`.
7. `hloc A B hA hB hlocp hlocR : hilbertSym A B = 1`.
8. `weightedSumSquares_isotropic_iff_hilbertSym_eq_one` turns that into
   `Isotropic (weightedSumSquares ℚ wq)`, and `hw'.isotropic_iff` transfers to `Isotropic Q`.

## Exact gap vs. `Targets.isotropic_of_rank_three`

The asserted theorem here has one extra explicit hypothesis `hloc : HilbertSymLocalGlobal`.
Discharging it is precisely the Hasse norm theorem for quadratic extensions of ℚ (equivalently,
Hasse–Minkowski for the conic `z² = A x² + B y²`, i.e. the very rank-3 statement), so it cannot
be derived from the current library.  Everything else — diagonalization, the ternary criterion,
base change of the local isotropy data, and the final transfer back — is fully proved here.

Note: the *forward* half of the local–global statement (global symbol 1 ⇒ all local symbols 1)
is immediate by base-changing a rational conic point; only the reverse is missing.  The forward
half is not needed for this theorem.

## Final status
- LSP: file compiles, no diagnostics.
- `lake_check Pptc/HasseMinkowski/RankThree.lean`: **OK - no errors or warnings.**
- No scratch files left; only `Pptc/HasseMinkowski/RankThree.lean` and this log were written.

## C.0 (wave after A.2): can `HilbertSymLocalGlobal` be discharged?

Target: `theorem hilbertSymLocalGlobal : HilbertSymLocalGlobal`.

- [recon] A.2 is DONE: `theorem hilbertReciprocity : HilbertReciprocity` —
  `(∏ᶠ p (A,B)_p) * (A,B)_ℝ = 1`.  But under the *hypotheses* of `HilbertSymLocalGlobal`
  every factor is already `1`, so reciprocity's conclusion `1 * 1 = 1` is automatic.
  **Therefore reciprocity gives literally zero information about `(A,B)_ℚ`; candidate
  route 1 (product-formula route of `Plan-next.md` §C.0) is mathematically invalid.**
- [evidence] Under the hypotheses, `hilbertProd A B = 1` holds by
  `finprod_eq_one_of_forall_eq_one`; the target's conclusion is a *different* symbol (over
  `ℚ`, not over a completion), so no algebraic manipulation of the product can reach it.
- [recon] The global conic symbol `(A,B)_ℚ` is the splitting bit of the quaternion algebra
  `(A,B)`, and is **not** multiplicative over `ℚ`: `(2,3)_ℚ = (2,5)_ℚ = (2,15)_ℚ = -1`
  (each ruled out of the norm group of `ℚ(√2)` by an infinite-descent mod-3 argument),
  whereas multiplicativity would give `(2,15)_ℚ = (2,3)_ℚ·(2,5)_ℚ = 1`.  Hence no
  `HasBilinHilbertSym ℚ` instance exists, and the "index-2 norm group" shortcut is false.
- [recon] `HilbertSymLocalGlobal` is *exactly* the rank-three local–global principle for
  the diagonal form `⟨-A,-B,1⟩` (Legendre's theorem / Hasse–Minkowski rank 3), via the
  unconditional ternary criterion `weightedSumSquares_isotropic_iff_hilbertSym_eq_one`.
  It is the Hasse norm theorem for quadratic extensions.  Neither this project nor the
  reference WiN7 has it: WiN7's `QuadraticForm/RankThree.lean` is `sorry`
  (`Scratch/win7-reference.md` §7).  Proving it needs Legendre descent (Minkowski /
  geometry of numbers) or global class field theory.
- [verdict] **`hilbertSymLocalGlobal` is NOT reachable in one session.**  Deliver the
  formal equivalence instead (it pins the obstruction exactly), plus this report.
- [plan] Append `RankThreeDiagonalLocalGlobal` and prove
  `hilbertSymLocalGlobal_iff_rankThreeDiagonal : HilbertSymLocalGlobal ↔
  RankThreeDiagonalLocalGlobal`.  Full proof of the target would additionally need the
  descent/Hasse-norm theorem.
- [done] Appended to `RankThree.lean` (lines 164–241), sorry-free:
  * `def RankThreeDiagonalLocalGlobal : Prop` — local isotropy everywhere of `⟨-A,-B,1⟩`
    (all `ℚ_[p]` and `ℝ`) implies global isotropy of `⟨-A,-B,1⟩` over `ℚ`.
  * `theorem hilbertProd_eq_one_of_local_eq_one` — under the target's hypotheses the
    product formula's conclusion is automatic (formal witness that A.2 is vacuous here).
  * `theorem hilbertSymLocalGlobal_iff_rankThreeDiagonal :
      HilbertSymLocalGlobal ↔ RankThreeDiagonalLocalGlobal` — the target is *exactly*
    rank-three Hasse–Minkowski (Legendre's theorem).
- [verify] `lean_verify` on both new theorems → axioms `{propext, Classical.choice,
  Quot.sound}`; no `sorry`/`admit`/`axiom` anywhere (only the words appear in comments).
- [final] LSP clean; `lake_check Pptc/HasseMinkowski/RankThree.lean` → **OK - no errors or
  warnings**.  Max line length 97.
- [conclusion] **The deliverable `theorem hilbertSymLocalGlobal` was NOT produced** because
  it is the Hasse norm theorem for quadratic extensions of `ℚ` (equivalently rank-three
  Hasse–Minkowski / Legendre's theorem), which is `sorry` in the reference WiN7 and requires
  an elementary-descent (Minkowski/geometry-of-numbers) or global-class-field-theory proof.
  The product-formula route of `Plan-next.md §C.0` is mathematically invalid: reciprocity is
  a tautology under these hypotheses.  Recorded the exact equivalence instead.
