# PLAN: Hasse–Minkowski and Meyer's theorem in Lean (Pptc)

**Goal.** Prove, sorry-free, in the `Pptc` package:

1. **Hasse–Minkowski over ℚ** (isotropy form): a nondegenerate finite-dimensional
   quadratic form `Q` over `ℚ` is isotropic iff it is isotropic over every completion
   (`ℝ` and `ℚ_[p]` for all primes `p`).
2. **Meyer's theorem**: an indefinite quadratic form over `ℚ` in `≥ 5` variables is
   isotropic (and the degenerate-case radical statement). This is the corollary needed
   by `Pptc/Nonic.lean`.

The final public entry point will be `Pptc.HasseMinkowski.Meyer.meyer`, imported by
`Pptc/Nonic.lean` in place of the current `sorry` in `exists_tschirnhaus9`.

## Status at start (Lean 4.33, Mathlib of Pptc)

* Mathlib has only the **linear-algebraic** quadratic-form theory: `QuadraticMap`,
  `weightedSumSquares`, `prod` (orthogonal sum), `Nondegenerate`, `Anisotropic`,
  `discr`, `equivalent_weightedSumSquares(_units_of_nondegenerate')`,
  `equivalent_one_neg_one_weighted_sum_squared` (over `ℝ`).
* Mathlib **lacks**: `Isotropic`/`represents` API, base-change of equivalences,
  `nondegenerate_of_anisotropic`, any `ℚ`/`ℚ_[p]` square classification for `Padic`,
  Hilbert symbol, Hasse invariant, local-field classification, Hasse–Minkowski, Meyer.
* Present and reusable: `padicValRat` (full API), `Padic.valuation_ratCast`,
  `Rat.isSquare_iff` (`IsSquare q ↔ IsSquare q.num ∧ IsSquare q.den`), `Real.isSquare_iff`,
  `hensels_lemma`, Chevalley–Warning (`char_dvd_card_solutions*`), Legendre/Jacobi
  reciprocity (`legendreSym.quadratic_reciprocity`).
* External reference: `github.com/mariainesdff/HassePrinciple` (WiN7, Lean 4.34-rc2,
  Apache-2.0). Its rank ≤ 2 and rank 4 (modulo rank 3) are proved; **rank 3 and the
  rank ≥ 5 case (literally Meyer) are `sorry`**. Use it as a structural blueprint and
  for API naming, but its proof of our target does not exist.

## Architecture (Serre, *A Course in Arithmetic*, Ch. IV), bottom-up

```
Layer 5  Meyer.lean            Meyer: n >= 5 + indefinite => isotropic          [TARGET]
Layer 4  HasseMinkowski.lean   Isotropic <-> EverywhereLocallyIsotropic          [HARD]
Layer 3  QuadraticForm/
           RankTwo.lean        rank <= 2 over Q (square classes, valuations)     [medium]
           RankThree.lean      ternary isotropy = Legendre criterion            [HARD]
           RankFour.lean       rank 4 via Hilbert reciprocity + rank 3          [HARD]
           HighRank.lean       local isotropy n>=5 + reduction from rank 4      [HARD]
Layer 2  HilbertSymbol/
           Basic.lean          (a,b)_v definition, bilinearity, symmetry         [medium]
           Reciprocity.lean    prod_v (a,b)_v = 1 (uses quadratic reciprocity)   [HARD]
           HasseInvariant.lean Hasse invariant, classification over Q_v         [HARD]
Layer 1  Padics/
           Squares.lean        Q_p*/Q_p*^2 classification, Hensel-based          [medium]
         RatSquares.lean       q square iff nonneg + all padicValRat even        [medium]
Layer 0  Basic.lean            Isotropic/represents/nondegeneracy/base-change    [cheap]
```

Dependency order: Layer 0 → 1 → 2 → 3 → 4 → 5. Layers 3 and 4 are the research-heavy
parts; Layers 0–1 are the foundation and are the current session's focus.

## File layout

All Hasse–Minkowski code and notes live under `pptc/Pptc/HasseMinkowski/`
(namespace `Pptc.HasseMinkowski`). Subagent logs: `HANDOFF-<topic>.md` in the same dir.

```
Pptc/HasseMinkowski/
  Plan.md                 this file
  HANDOFF.md              running progress log
  Basic.lean              Layer 0
  RatSquares.lean         Layer 1
  Padics/Squares.lean     Layer 1
  HilbertSymbol/Basic.lean
  QuadraticForm/RankTwo.lean
  ... (later layers)
  Meyer.lean              final entry importing upwards
```

## Conventions

* Targeted imports only, never `import Mathlib`.
* `Isotropic Q : Prop := ∃ x, x ≠ 0 ∧ Q x = 0`; `Anisotropic` is Mathlib's.
* Every theorem: `-- Theorem: ...` line. No `sorry` in a delivered layer.
* Confirm with `lake_check Pptc/HasseMinkowski/<file>.lean`. Never whole-project build.
* Mirror WiN7 naming where sensible (`EverywhereLocallyIsotropic`, `isotropic_of_rank_*`).

## Milestones

* **M0 (this session).** `Basic.lean` compiling sorry-free; `RatSquares.lean` and
  `Padics/Squares.lean` underway; plan + handoffs written.
* **M1.** Rank ≤ 2 Hasse–Minkowski over ℚ (needs Layer 1).
* **M2.** Hilbert symbol + reciprocity; Hasse invariant.
* **M3.** Rank 3 and rank 4.
* **M4.** Local isotropy for n ≥ 5; global Hasse–Minkowski; Meyer.
* **M5.** Wire `Pptc/Nonic.lean` to `Pptc.HasseMinkowski.Meyer.meyer`; remove the
  `exists_tschirnhaus9` `sorry` together with the Hermite-signature / collision layer.
