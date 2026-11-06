# PLAN v3 — Hasse–Minkowski & Meyer, Serre's route (supersedes `Plan.md`, `Plan-next.md`)

All paths are relative to `pptc/`. Source of truth for the mathematics: **Serre, *A Course in
Arithmetic*, Ch. III §2 (Hilbert symbol over ℚ, Thm 3–4) and Ch. IV §2–3 (Thm 6, Thm 8)**.
Follow Serre, not WiN7: WiN7 has `sorry` exactly at the hard points, and its chain lemma is vacuous.

**Goal (unchanged).** Sorry-free `hasseMinkowski` and `meyer` (the statements in `Targets.lean`),
then wire `meyer` into `Pptc/Nonic.lean` (`exists_tschirnhaus9`, a 6-variable indefinite form).

---

## 0. Course correction — read this before doing anything

### 0.1 Where things went wrong
1. **The Hasse invariant's well-definedness is NOT on the critical path.** It was treated as the
   critical path (Workstream B), which produced the false hypothesis `hconn`, the vacuous
   `hwell`, `ChainHypothesis`, and Witt cancellation. None of it is needed. Over ℚ, and over
   every completion, **every nondegenerate form is equivalent to a diagonal one**
   (`QuadraticForm.equivalent_weightedSumSquares_units_of_nondegenerate'`), and isotropy is
   invariant under equivalence (`Equivalent.isotropic_iff`). Serre's proof of Thm 8 only ever
   uses Hilbert symbols **of explicit diagonal coefficients**. So every local criterion below is
   stated for `weightedSumSquares` with named weights, and no invariant has to be well-defined.
2. **Rank 3 was misclassified as "Hasse norm theorem, needs class field theory / geometry of
   numbers, out of scope."** Over ℚ, the rank-3 case is *Legendre's theorem*, and Serre proves it
   (Thm 8, case n = 3) by an **elementary descent** on `|a| + |b|`. It needs no reciprocity, no
   geometry of numbers and no class field theory, only CRT and the fact that a norm group is a
   group. (The worker was right that the "product-formula route" for C.0 was invalid, but wrong
   about what replaces it.)
3. **Conditional theorems with invented hypotheses.** `hconn` turned out to be false, so three
   files of "sorry-free" results are vacuous. New rule in §4: a hypothesis `Prop` may only be a
   statement from Serre, cited in the docstring and believed true.

### 0.2 Frozen: do not edit, extend, import or "fix"
`Chain.lean`, `BasisChain.lean`, `HasseInvariantWellDef.lean`, `RankCriteriaGeneral.lean`,
`QuadraticForm/Witt.lean`, `QuadraticForm/Restriction.lean`. They are correct as far as they go but
off-route. (`HasseInvariant.lean` stays: `hasseMinkowskiInvAux` is just a formula in explicit
weights, used in `RankCriteria.represents_zero_iff_of_rank_three_diag`.) Old Workstreams B.4, B.5,
C.1, C.2 and C.3 are **cancelled**.

### 0.3 Assets we keep and build on
| File | What we use |
|---|---|
| `Basic.lean`, `Locally.lean`, `Prod.lean` | `Isotropic`, `represents`, `EverywhereLocallyIsotropic`, `baseChange_weightedSumSquares`, `prod_isotropic_iff`, `represents_of_isotropic_nondegenerate`, `weightedSumSquares_mul_squares_equivalent`, `Equivalent.isotropic_iff` |
| `HilbertSymbol/{Defs,Real,Padic,Two}.lean` | `hilbertSym`, `HasBilinHilbertSym ℝ`/`ℚ_[2]`, `hilbertSym_padic_odd_mul_left`, odd + 2-adic closed formulas, `hilbertSym_padicInt_units`, `hilbertSym_mul_square_eq` (field-generic) |
| `HilbertSymbol/Norm.lean` | `hilbertSym_eq_one_iff_isNorm` (generic field, `QuadraticAlgebra k b 0`) |
| `HilbertSymbol/Reciprocity.lean` | `hilbertReciprocity`, `almost_all_one` |
| `HilbertSymbol/Existence.lean` | the `S`/`T`/`A`/`M` construction (its "status" docstring is stale: the formulas it waits for now exist) |
| `RankCriteria.lean`, `RankThree.lean` | diagonal rank-3 criterion; `isotropic_of_rank_three (hloc : HilbertSymLocalGlobal)` |
| `RatApproximation.lean`, `Padics/Squares.lean` | `approximation'`, openness of squares, `isSquare_of_zmodPow` |
| Mathlib | Dirichlet: `Nat.forall_exists_prime_gt_and_eq_mod`; `Int.bmod`; `Nat.sq_mul_squarefree` |

---

## 1. The route (Serre Ch. IV Thm 8), in one screen

Everything is diagonal: `f = ⟨a₁,…,aₙ⟩`, `aᵢ ∈ ℚ*`, WLOG squarefree integers.

* **Local facts** (any `k ∈ {ℝ, ℚ_p}`, `HasBilinHilbertSym k`):
  - rank 3: `⟨a,b,c⟩` isotropic ⟺ `(-ac, -bc) = 1` (have).
  - rank 2: `⟨a,b⟩` represents `x ≠ 0` ⟺ `(x, -ab) = (a,b)`.
  - rank 5 over `ℚ_p`: always isotropic (needed only for Meyer).
* **n = 2.** Done (`RankTwo.lean`).
* **n = 3 (Legendre descent).** `z² − a x² − b y²`, `a,b` squarefree, `|a| ≤ |b|`, induct on `|a|+|b|`.
  If `|b| = 1`, then `(a,b)_ℝ = 1` forces `a` or `b` to be `1`. Otherwise, for each `p | b`,
  `(a,b)_p = 1` makes `a` a square mod `p`, so by CRT `t² ≡ a (mod b)` with `|t| ≤ |b|/2`.
  Then `t² − a = b b'`, `|b'| < |b|`, and since `bb'` is a norm from `k(√a)`,
  `(a,b)_v = (a,b')_v` at **every** field. Strip squares from `b'` and apply induction.
* **n = 4.** `f = ⟨a₁,a₂⟩ ⊥ −⟨−a₃,−a₄⟩`. At each place pick `x_v` represented by both halves.
  The **existence theorem** (Serre III Thm 4) gives `x ∈ ℚ*` with
  `(x,−a₁a₂)_v = (a₁,a₂)_v` and `(x,−a₃a₄)_v = (−a₃,−a₄)_v` for all `v`. By the rank-2 criterion,
  `⟨a₁,a₂,−x⟩` and `⟨−a₃,−a₄,−x⟩` are locally isotropic everywhere. Rank 3 then shows both
  halves represent `x` over ℚ, so `f` is isotropic.
* **n ≥ 5.** `f = h ⊥ −g`, `h = ⟨a₁,a₂⟩`, `S = {∞, 2, p | aᵢ}`. For `v ∈ S`, pick `h(x_v) = a_v = g(y_v)`.
  Approximate `(x_v)_{v∈S}` by `x ∈ ℚ²` and set `a = h(x)`, so that `a/a_v` is a square at every
  `v ∈ S`. Then `f₁ = ⟨a⟩ ⊥ −g` (rank `n−1`) is locally isotropic everywhere: at `v ∈ S` because
  `g` represents `a_v ~ a`; at `v ∉ S` because `g` has ≥ 3 unit coefficients at an odd prime.
  By induction `g` represents `a` over ℚ, and `h(x) = a`, so `f` is isotropic.
* **General `Q`.** A degenerate `Q` is isotropic (a radical vector). Otherwise diagonalize,
  transport `EverywhereLocallyIsotropic` through base change, and dispatch on rank.
* **Meyer.** HM + (rank ≥ 5 ⇒ isotropic over every `ℚ_p`) + `Indefinite.isotropic` over ℝ.

---

## 2. Work packages

Size: **S** ≤ half a session, **M** ≈ one session, **L** = split further before delegating.
Each numbered item is **one subagent task** with its statement given verbatim. Lean statements
below are targets; adjust binders and coercions, but never the mathematical content.

### WP0 — Baseline (S, main session, first)
- [ ] 0.1 `git add Pptc/HasseMinkowski && git commit` (the whole directory is currently
  **untracked**; one bad worker edit could lose weeks). Commit locally only; never push.
- [ ] 0.2 `lean_diagnostic_messages` on every file in §0.3; record any errors here before starting.
- [ ] 0.3 Put a banner at the top of the frozen files (§0.2) and fix the stale docstrings in
  `RankThree.lean` (`HilbertSymLocalGlobal` "not provable…") and `Existence.lean` ("Status").

### WP1 — Legendre / rank 3 (new file `Legendre.lean`) — **critical path**
- [ ] **1.1 (S) Norm transfer**, generic field:
  ```lean
  theorem hilbertSym_eq_of_sq_sub_eq_mul {k : Type*} [Field k] [Invertible (2 : k)]
      {a b b' t : k} (hb : b ≠ 0) (hb' : b' ≠ 0) (h : t ^ 2 - a = b * b') :
      hilbertSym a b = hilbertSym a b'
  ```
  Hint: if `a = 0`, both sides are `0`. If `IsSquare a`, both are `1` (`z = √a, x = 1, y = 0`).
  Otherwise use `hilbertSym_comm` + `hilbertSym_eq_one_iff_isNorm` in `QuadraticAlgebra k a 0`:
  `b b' = N(t + √a)`. If `b = N(u)`, then `b' = N((t+√a)·ū) / b² = N((t+√a)·ū·b⁻¹)`, and the
  symmetric argument gives the other direction. Use only `norm_mul` and conjugation, not a field
  instance on the algebra.
- [ ] **1.2 (S) Local ⇒ square mod p:**
  ```lean
  theorem exists_sq_mod_of_hilbertSym (a b : ℤ) (hb : Squarefree b) (p : ℕ) [Fact p.Prime]
      (hpb : (p : ℤ) ∣ b) (h : hilbertSym (a : ℚ_[p]) (b : ℚ_[p]) = 1) :
      ∃ t : ℤ, (p : ℤ) ∣ t ^ 2 - a
  ```
  Hint: if `p ∣ a` take `t = 0`; if `p = 2` take `t = a`. Otherwise scale the local zero to a
  primitive `(z,x,y) ∈ ℤ_p³` and reduce with `toZMod`. If `p ∣ x`, then `p ∣ z`, so `p² ∣ b y²`;
  since `p² ∤ b` this gives `p ∣ y`, contradicting primitivity. Hence `a ≡ (z/x)² (mod p)`.
- [ ] **1.3 (S) CRT with a size bound:**
  ```lean
  theorem exists_sq_mod_squarefree (a b : ℤ) (hb : Squarefree b)
      (h : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ b → ∃ t : ℤ, (p : ℤ) ∣ t ^ 2 - a) :
      ∃ t : ℤ, b ∣ t ^ 2 - a ∧ 2 * |t| ≤ |b|
  ```
  Hint: CRT over the distinct prime factors, then replace `t` by `Int.bmod t b.natAbs`.
- [ ] **1.4 (S) Squarefree normal form:** `∀ A : ℚ, A ≠ 0 → ∃ a : ℤ, Squarefree a ∧ ∃ s : ℚ,
  s ≠ 0 ∧ A = a * s ^ 2`, plus the integer version `∀ n : ℤ, n ≠ 0 → ∃ m u, Squarefree m ∧
  u ≠ 0 ∧ n = m * u ^ 2` (`Nat.sq_mul_squarefree`).
- [ ] **1.5 (M) Descent:**
  ```lean
  theorem legendre_int (a b : ℤ) (ha : Squarefree a) (hb : Squarefree b)
      (hp : ∀ (p : ℕ) [Fact p.Prime], hilbertSym (a : ℚ_[p]) (b : ℚ_[p]) = 1)
      (hr : hilbertSym (a : ℝ) (b : ℝ) = 1) : hilbertSym (a : ℚ) (b : ℚ) = 1
  ```
  Strong induction on `a.natAbs + b.natAbs`; WLOG `|a| ≤ |b|` via `hilbertSym_comm`. Base case
  `|b| = 1`: `hilbertSym_real_eq`. Step: 1.2 + 1.3 give `t`. If `t² = a`, then `a` is a square and
  we are done. Otherwise `b' := (t² − a)/b ≠ 0` and `|b'| ≤ |b|/4 + 1 < |b|` (use `|b| ≥ 2`,
  `|a| ≤ |b|`). Write `b' = b'' u²` with 1.4. Transfer every local hypothesis to `(a, b'')` with
  1.1 (cast `t,a,b,b'` into `ℚ_[p]` / `ℝ`) and `hilbertSym_mul_square_eq`, apply the IH, and
  transfer back over ℚ with 1.1.
- [ ] **1.6 (S) Close rank 3:** `theorem hilbertSymLocalGlobal : HilbertSymLocalGlobal` (1.4 +
  `hilbertSym_mul_square_eq` + 1.5), then an unconditional
  `isotropic_of_rank_three' := isotropic_of_rank_three hilbertSymLocalGlobal` (in `Legendre.lean`,
  importing `RankThree.lean`).

### WP2 — Local Hilbert-symbol API (new file `HilbertSymbol/Local.lean`) — parallel with WP1
- [ ] **2.1 (S)** `instance [Fact p.Prime] : HasBilinHilbertSym ℚ_[p]`, by cases on `p = 2`, from
  `hilbertSym_padic_odd_mul_left` and `Two.instHasBilinHilbertSym`.
- [ ] **2.2 (S) Rank-2 criterion**, generic `k` with `[HasBilinHilbertSym k] [Invertible (2:k)]`:
  ```lean
  theorem represents_weightedSumSquares_two_iff {a b x : k} (ha : a ≠ 0) (hb : b ≠ 0)
      (hx : x ≠ 0) : (weightedSumSquares k ![a, b]).represents x ↔
        hilbertSym x (-(a * b)) = hilbertSym a b
  ```
  Proof: `represents x ⟺ ⟨a,b,−x⟩ isotropic`. If the zero has last coordinate `0`, then `⟨a,b⟩` is
  isotropic and represents everything. Otherwise use the rank-3 criterion `(ax, bx) = 1` and
  expand: `(ax,bx) = (a,b)(x,ab)(x,x) = (a,b)(x,−ab)`.
- [ ] **2.3 (S) Nondegeneracy over `ℚ_[p]`:** `c ≠ 0 → ¬IsSquare c → ∃ x ≠ 0, hilbertSym x c = -1`.
  Witnesses from the closed formulas, with `c = p^α u`:
  - `p` odd: if `α` is odd, take a unit non-residue; if `α` is even, take `p`.
  - `p = 2`: if `α` is odd, take `5`; if `α` is even and `u ≡ 3 (mod 4)`, take `−1`; if `α` is
    even and `u ≡ 5 (mod 8)`, take `2`.
  Also over ℝ: `c < 0` with `x = −1`.
- [ ] **2.4 (S) Two prescribed symbols**, generic `k`, assuming 2.3 as a hypothesis `hnd`:
  if `c₁, c₂, c₁c₂` are all non-squares and `e₁, e₂ ∈ {±1}`, then
  `∃ x ≠ 0, (x,c₁) = e₁ ∧ (x,c₂) = e₂`. Proof: combine witnesses `y` for `(y,c₁) = −1`,
  `w` for `(w,c₂) = −1` and `z` for `(z,c₁c₂) = −1`; their products realise all four sign patterns.
- [ ] **2.5 (S)** Over `ℚ_[p]`: `∀ c, ∃ c₂, ¬IsSquare c₂ ∧ ¬IsSquare (c * c₂)`. Among three pairwise
  non-square-equivalent non-squares (`{u₀, p, u₀p}` for odd `p`, `{−1, 2, −2}` for `p = 2`), at
  most one is `~ c`.
- [ ] **2.6 (M) Local rank 5:** `∀ w : Fin 5 → ℚ_[p], (∀ i, w i ≠ 0) →
  (weightedSumSquares ℚ_[p] w).Isotropic` (then any `n ≥ 5`, by restricting to 5 coordinates).
  Route (Serre IV Thm 6):
  - First, `⟨b₁,b₂,b₃⟩` represents `x` whenever `¬IsSquare (−b₁b₂b₃·x)`. Find `y` represented
    by `⟨b₁,b₂⟩` and by `⟨−b₃, x⟩` using 2.2 + 2.4 with `c₁ = −b₁b₂`, `c₂ = b₃x`; the degenerate
    cases `c₁` or `c₂` square are direct.
  - Then for `f`: if `−w₀w₁` is a square, `⟨w₀,w₁⟩` is isotropic. Otherwise choose `x` with
    `(x, −w₀w₁) = (w₀,w₁)` and `x ≁ w₂w₃w₄`. Get it from 2.4, with `c₂` from 2.5 and `e₂ ≠ (w₂w₃w₄, c₂)`.
    Then `⟨w₀,w₁⟩` and `⟨−w₂,−w₃,−w₄⟩` both represent `x`.

### WP3 — Existence theorem (extend `HilbertSymbol/Existence.lean`) — parallel with WP1/WP2
Target (Serre III Thm 4; `I` finite, or just `Fin 2` if that is materially easier):
```lean
theorem exists_rat_hilbertSym (a : I → ℚ) (ha : ∀ i, a i ≠ 0)
    (ε : I → Nat.Primes → ℤ) (εR : I → ℤ)
    (h1 : ∀ i, {p | ε i p ≠ 1}.Finite)
    (h2 : ∀ i, (∏ᶠ p, ε i p) * εR i = 1)
    (h3 : ∀ p : Nat.Primes, ∃ x : ℚ_[p], x ≠ 0 ∧ ∀ i, hilbertSym (a i : ℚ_[p]) x = ε i p)
    (h3R : ∃ x : ℝ, x ≠ 0 ∧ ∀ i, hilbertSym (a i : ℝ) x = εR i) :
    ∃ x : ℚ, x ≠ 0 ∧ (∀ i p, hilbertSym (a i : ℚ_[p]) x = ε i p) ∧
      ∀ i, hilbertSym (a i : ℝ) x = εR i
```
- [ ] **3.1 (M) Disjoint case** (`aᵢ` squarefree integers, `S ∩ T = ∅`, `εR ≡ 1`): take
  `x = A·ℓ` with `ℓ` a prime, `ℓ ≡ A (mod M)` and `ℓ` larger than everything in `S ∪ T`
  (`Nat.forall_exists_prime_gt_and_eq_mod`). Check each place:
  - `v ∈ S`: `x ≡ A² (mod M)`, so `x` is a square in `ℚ_v` (odd `p`: unit square mod `p`;
    `p = 2`: `≡ 1 (mod 8)`; `x > 0`), and the symbol is `1 = ε`.
  - `v ∈ T`: `v(x) = 1`, so the symbol is the Legendre symbol `(aᵢ/v)`. `h3` forces
    `ε_{i,v} = (aᵢ/v)`, because some `ε_{j,v} = −1` makes `v(x_v)` odd.
  - `v ∉ S ∪ T ∪ {ℓ}`: both arguments are units, so the symbol is `1`.
  - `v = ℓ`: `hilbertReciprocity` on both sides.
- [ ] **3.2 (M) General case:** for `v ∈ S` take `x_v` from `h3`; `approximation'` + openness of
  squares give `x'` with `x'/x_v` a square at every `v ∈ S`. Apply 3.1 to
  `η_{i,v} := ε_{i,v}·(aᵢ,x')_v` (check (1) `almost_all_one`, (2) `hilbertReciprocity`, (3)
  realised by `x_v x'`). Then `x = x'y`. Reduce rational `aᵢ` to squarefree integers with 1.4 +
  `hilbertSym_mul_square_eq`.

### WP4 — Rank 4 (`RankFour.lean`, replace skeleton; stop importing `Targets`) — after WP1, 2.2, WP3
- [ ] **4.1 (S)** Local splitting: `⟨a₁,a₂,a₃,a₄⟩_v` isotropic ⇒ `∃ x_v ≠ 0` represented by
  `⟨a₁,a₂⟩` and `⟨−a₃,−a₄⟩` (`prod_isotropic_iff` + `represents_of_isotropic_nondegenerate`).
- [ ] **4.2 (M)** Diagonal rank-4 HM: `∀ w : Fin 4 → ℚ, (∀ i, w i ≠ 0) → (∀ p, isotropic over
  ℚ_[p]) → isotropic over ℝ → isotropic over ℚ`. Feed 4.1 + 2.2 into `exists_rat_hilbertSym`
  (for `v` with nothing to prescribe take `x_v = 1`; `(a₁,a₂)_p = 1` a.e. by `almost_all_one`).
  Then 2.2 + 1.6 give ℚ-representations of `x` by both halves.

### WP5 — Rank ≥ 5 (`HighRank.lean`, replace skeleton) — can start before WP4
Develop against the hypothesis `(h4 : RankFourDiagonalHM)`, a `Prop` that is literally the true
statement of 4.2, then discharge it with 4.2.
- [ ] **5.1 (S)** Odd `p`, units `u₁,u₂,u₃ : ℤ_[p]ˣ` ⇒ `⟨u₁,u₂,u₃⟩` isotropic over `ℚ_[p]`
  (rank-3 criterion + `hilbertSym_padicInt_units`), and so is any diagonal form with ≥ 3 unit weights.
- [ ] **5.2 (S)** Openness: for `k ∈ {ℝ, ℚ_[p]}`, `a₀ ≠ 0 ⇒ ∃ δ > 0, ∀ a, ‖a − a₀‖ < δ →
  IsSquare (a / a₀)`. Vector approximation: `x_v ∈ ℚ_v²` for `v ∈ S` ⇒ `∃ x ∈ ℚ²` close at every `v`
  (componentwise `approximation'`).
- [ ] **5.3 (M)** Diagonal HM for `n ≥ 5` by induction on `n` with base `h4`, following §1.
  Handle the two degenerate choices of `a_v` (when `h_v` or `g_v` is isotropic) with
  `prod_isotropic_iff`.

### WP6 — Assemble (new `HasseMinkowski/Main.lean`), then Nonic
- [ ] **6.1 (S)** A degenerate `Q` over a char-0 field is isotropic (a nonzero radical vector `x` has
  `Q x = associated Q x x = 0`).
- [ ] **6.2 (M)** `hasseMinkowski` for general `Q`: 6.1, else diagonalize
  (`equivalent_weightedSumSquares_units_of_nondegenerate'`), transport local isotropy through base
  change of the equivalence (`Basic.lean`) + `baseChange_weightedSumSquares`, and dispatch
  `finrank = 0,1,2,3,4,≥5`.
- [ ] **6.3 (S)** `meyer`: 6.1, else HM with 2.6 at every `p` and `Indefinite.isotropic` at ℝ.
- [ ] **6.4 (S)** Delete `Targets.lean`; point `Pptc/Nonic.lean` at `Main.meyer`; re-read
  `exists_tschirnhaus9` for the extra (non-Meyer) inputs it needs.

### Dependency order
```
WP0 ─┬─ WP1 (1.1–1.6) ──────────────┐
     ├─ WP2 (2.1–2.5) ─┬─ 2.6 ──────┼──────────────── 6.3
     └─ WP3 (3.1–3.2) ─┴────── WP4 ─┴─ WP5 (on h4) ─ 6.2 ─ 6.4
```
Waves (one heavy worker at a time, per the RAM notes): **1.1, 2.1, 1.4** → **1.2, 1.3, 2.2** →
**1.5, 2.3, 2.4** → **1.6, 2.5, 3.1** → **3.2, 2.6, 5.1, 5.2** → **4.1, 4.2** → **5.3** → **6.x**.

---

## 3. Definition of done
`lean_verify` on `Pptc.HasseMinkowski.hasseMinkowski` and `…meyer` reports only
`{propext, Classical.choice, Quot.sound}`; `rg -n 'sorry' Pptc/HasseMinkowski --glob '*.lean'`
finds nothing outside comments and frozen files; `Targets.lean` is deleted; `Nonic.lean` no longer
has the Meyer `sorry`.

---

## 4. Rules for workers (these replace the ones that failed)

1. **Serre is the spec.** If a step is not in Serre III.2 / IV.2–3 or in this file, do not do it.
   No new infrastructure (orthogonal complements, chains, invariants) without the orchestrator's
   sign-off.
2. **One task = one statement from §2, given verbatim.** Do not widen scope or start the next item.
3. **Never add a hypothesis to "make it go through."** If a statement looks false, stop and report
   a concrete counterexample. If a lemma is genuinely missing, report its exact statement. A
   conditional `Prop` hypothesis is allowed only if it is a theorem of Serre, cited in the docstring.
4. **Never declare something "out of scope" / "research-level" / "needs CFT."** Report "stuck at
   <goal>" with the proof state; the orchestrator decides.
5. **Do not edit plan files or frozen files.** Log progress only in `HANDOFF-<topic>.md`, one line
   every ~6 tool calls, and when a task finishes add one line to `HANDOFF.md` (what was proved,
   file, line).
6. **LSP-first** (`lean_diagnostic_messages`, `lean_goal`, `lean_multi_attempt`); one final
   `lake_check` per file; never a whole-project `lake build`; kill only `lean`/`lake`.
7. **Commit after each finished item** (local commit on `main`, message names the item, e.g.
   `HM 1.3: CRT with size bound`). Never push.
8. Conventions: targeted imports, `-- Theorem:` lines, ≤ 100-char lines, no `sorry`/`axiom` in
   delivered code, `lean_verify` the main declaration.
