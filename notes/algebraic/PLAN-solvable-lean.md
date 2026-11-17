# PLAN-solvable-lean: solvable real algebraic numbers in Lean

**Status (2026-11-09): plan only.** No Lean changes yet. This file answers the two
questions issue #14 asks before implementation:

1. **What statement shape?** Use `Group.IsSolvable q.Gal` as the headline, and
   `z ∈ solvableByRad ℚ ℂ` as the formal engine. Both are needed; see §2.
2. **Which Mathlib Galois API?** The exact declarations are listed in §3 and §6.
   The short answer: `Polynomial.Gal`, `IsSplittingField`,
   `IntermediateField.adjoin_rootSet_isSplittingField`, `IsGalois.of_separable_splitting_field`,
   `IsGalois.of_fixedField_normal_subgroup`, `IsGalois.normalAutEquivQuotient`, and
   `exists_root_adjoin_eq_top_of_isCyclic` / `isCyclic_tfae` (both in the root namespace).

**Implementation status (2026-11-09).**

- Milestones 1–5 are implemented and compile under LSP with no `sorry`.
- `Pptc/Solvable/Basic.lean` and `Pptc/Solvable/Roots.lean` contain
  `PConstructibleC`, the subfield `PComplex`, `exists_P_angle`,
  `exists_PComplex_nth_root`, `PComplex.mem_of_pow_mem`, and the unconditional
  `mem_PComplex_of_mem_solvableByRad`.
- `Pptc/Solvable/Galois.lean` contains the maximal-normal-prime-quotient group
  lemma and the solvable tower lemma `le_solvableByRad_of_solvable_tower`.
- `Pptc/Solvable/AbelRuffini.lean` proves the engine
  `mem_solvableByRad_of_isSolvable_gal`: a complex algebraic number with solvable
  minimal-polynomial Galois group lies in `solvableByRad ℚ ℂ`.  The prime
  divisibility step is proved by restricting `Gal(E/K₀)` injectively to the
  splitting field of the minimal polynomial, not by a degree bound.
- `Pptc/Solvable/Main.lean` contains the headline
  `root_Pconstructible_of_solvable_gal` and its complex counterpart.
  `Pptc.lean` imports the new module.  `lean_verify` reports only the standard
  axioms `propext`, `Classical.choice`, and `Quot.sound`.

**Target (paper statement, X1 §2.2 and §4).** Every real algebraic number whose
Galois closure over `ℚ` has solvable Galois group is `PConstructible`.

**Paper source.** `notes/algebraic/X1.md` §2.2 (complex radicals are free) and §4
(verdict table). The P-specific content is a single lemma: `P` is closed under
complex `n`-th roots when the real and imaginary parts of the power are P. The rest is
Mathlib Galois/Kummer theory.

---

## 1. Why this is not already in Mathlib

Mathlib has **one direction** of Abel–Ruffini:

* `solvableByRad ℚ E → Group.IsSolvable (minpoly ℚ x).Gal`
  (`isSolvable_gal_minpoly`, `isSolvable_gal_of_irreducible`,
  `Mathlib/FieldTheory/AbelRuffini.lean:316,331`).

It does **not** have the converse:

* `Group.IsSolvable (minpoly ℚ x).Gal → x ∈ solvableByRad ℚ ℂ`.

The converse is classical: a finite solvable Galois extension can be filtered by cyclic
extensions of prime degree; after adjoining the relevant roots of unity, each step is
Kummer, hence an `n`-th root. This is the main new formalization of issue #14. It is
ordinary Galois theory, not new mathematics; it is simply absent from Mathlib.

Two further gaps are P-specific:

* `PConstructible` is a predicate on `ℝ`, not on `ℂ`;
* there is no lemma saying that complex `n`-th roots preserve P-constructibility.

---

## 2. Statement shape: decision

We use **both** shapes, with different jobs.

### 2.1 Engine (the formal workhorse)

```lean
/-- A complex number whose real and imaginary parts are P-constructible. -/
def PConstructibleC (z : ℂ) : Prop :=
  PConstructible z.re ∧ PConstructible z.im

/-- Every element of the radical closure of `ℚ` in `ℂ` has P-constructible
real and imaginary parts. -/
theorem mem_PComplex_of_mem_solvableByRad {z : ℂ}
    (hz : z ∈ solvableByRad ℚ ℂ) : PConstructibleC z
```

This is the exact formal content of X1 §2.2. It is unconditional, needs no Galois
correspondence, and is a meaningful theorem on its own. It is also the only part that
uses the P-constructors (`sqrt`, `arccos`, `rpow`, `cos`, `sin`, `pi`).

### 2.2 Bridge (the missing Abel–Ruffini converse)

```lean
/-- Converse Abel–Ruffini, over `ℂ` (which contains all roots of unity). -/
theorem mem_solvableByRad_of_isSolvable_gal {z : ℂ}
    (hz : IsAlgebraic ℚ z) (h : Group.IsSolvable (minpoly ℚ z).Gal) :
    z ∈ solvableByRad ℚ ℂ
```

### 2.3 Headline (the issue's target)

Preferred polynomial form, matching the existing
`root_Pconstructible_deg8_coeffs` style:

```lean
theorem root_Pconstructible_of_solvable_gal {q : ℚ[X]} (hq : q ≠ 0)
    (hgal : Group.IsSolvable q.Gal) {α : ℝ} (hα : aeval α q = 0) :
    PConstructible α
```

and the minimal-polynomial form:

```lean
theorem solvable_real_algebraic_Pconstructible {α : ℝ}
    (hα : IsAlgebraic ℚ α) (hgal : Group.IsSolvable (minpoly ℚ α).Gal) :
    PConstructible α
```

The first is the useful interface (it accepts any rational polynomial with a solvable
splitting field). The second is the literal statement of the issue and follows from the
first with `q = minpoly ℚ α`.

**Why not use only `solvableByRad`?** Because it would not answer the issue: the issue
names the solvable-Galois-group hypothesis. The radical-tower form is the formal engine,
not the public statement.

**Why not use only `IsSolvable q.Gal`?** Because the P-specific work is naturally stated
as radical closure, and because `solvableByRad` is what Mathlib's induction principle
and `solvableByRad_le` operate on. Splitting the two keeps the difficult Galois bridge
isolated from the P-construction.

---

## 3. Mathlib API used (checked against Mathlib `v4.33.0`)

The pinned revision is `lake-manifest.json: mathlib db584cd6...`, toolchain
`leanprover/lean4:v4.33.0`.

### 3.1 Radicals and Abel–Ruffini

| declaration | file | use |
|---|---|---|
| `solvableByRad F E` | `FieldTheory/AbelRuffini.lean:195` | the radical closure, as an `IntermediateField` |
| `solvableByRad_le` | `AbelRuffini.lean:209` | root-closure criterion: `(∀ x n ≠ 0, x^n ∈ s → x ∈ s) → solvableByRad F E ≤ s` |
| `solvableByRad.rad_mem` | `AbelRuffini.lean:213` | membership of an `n`-th root |
| `isSolvable_gal_minpoly` | `AbelRuffini.lean:316` | already-proved forward Abel–Ruffini direction |

`solvableByRad` is the `sInf` of all intermediate fields closed under `n`-th roots
(`n ≠ 0`). This is exactly the closure operator needed to state the engine.

### 3.2 Galois correspondence

| declaration | file | use |
|---|---|---|
| `Polynomial.Gal` | `FieldTheory/PolynomialGaloisGroup.lean:55` | `p.Gal = p.SplittingField ≃ₐ[F] p.SplittingField` |
| `IsSplittingField` | `FieldTheory/SplittingField/IsSplittingField.lean` | splitting-field API |
| `IntermediateField.adjoin_rootSet_isSplittingField` | `IsSplittingField.lean:194` | if `p` splits in `L`, then `adjoin K (p.rootSet L)` is a splitting field |
| `Polynomial.IsSplittingField.finiteDimensional` | `IsSplittingField.lean:126` | finiteness |
| `IsGalois.of_separable_splitting_field` | `FieldTheory/Galois/Basic.lean:534` | separability + splitting ⇒ Galois |
| `IsGalois.tower_top_of_isGalois` | `Galois/Basic.lean:152` | `L/F` Galois, `F ≤ K` ⇒ `L/K` Galois |
| `IntermediateField.fixedField` | `Galois/Basic.lean` | fixed field of a subgroup |
| `IntermediateField.fixingSubgroup` | `Galois/Basic.lean` | subgroup fixing a field |
| `IsGalois.intermediateFieldEquivSubgroup` | `Galois/Basic.lean:350` | order-reversing Galois correspondence |
| `IsGalois.of_fixedField_normal_subgroup` | `Galois/Basic.lean:421` | normal subgroup ⇒ `fixedField H` is Galois over the base |
| `IsGalois.normalAutEquivQuotient` | `Galois/Basic.lean:431` | `Gal(L/K) ⧸ H ≃* Gal(fixedField H / K)` |
| `Polynomial.IsSplittingField.algEquiv` | `FieldTheory/SplittingField/Construction.lean:305` | identify two splitting fields |
| `AlgEquiv.autCongr` | `Algebra/Algebra/Equiv.lean:665` | transport `Gal` across an `AlgEquiv` |

### 3.3 Kummer theory

| declaration | file | use |
|---|---|---|
| `exists_root_adjoin_eq_top_of_isCyclic` | `FieldTheory/KummerExtension.lean:475` | cyclic `L/K` with enough roots of unity ⇒ `L = K(β)`, `β ^ [L:K] ∈ K` |
| `isCyclic_tfae` | `KummerExtension.lean:554` | equivalent characterizations of cyclic extensions |
| `primitiveRoots`, `IsPrimitiveRoot` | `RingTheory/RootsOfUnity/` | `μ_n ⊂ K` hypotheses |

Both Kummer declarations are in the **root namespace** (the file has no
`KummerExtension` namespace), so write `exists_root_adjoin_eq_top_of_isCyclic`, not
`KummerExtension.exists_root_adjoin_eq_top_of_isCyclic`.

### 3.4 Group theory

| declaration | file | use |
|---|---|---|
| `Group.IsSolvable` | `GroupTheory/Solvable.lean:126` | hypothesis |
| `Group.IsSolvable.commutator_lt_top_of_nontrivial` | `GroupTheory/Solvable.lean:189` | nontrivial solvable ⇒ derived subgroup proper |
| `IsSimpleGroup.comm_iff_isSolvable` | `GroupTheory/Solvable.lean:251` | simple solvable ⇒ commutative |
| `IsSimpleGroup.isCyclic` | `GroupTheory/SpecificGroups/Cyclic.lean:228` | simple commutative ⇒ cyclic |
| `IsSimpleGroup.prime_card` | `Cyclic.lean:238` | simple commutative ⇒ prime order |
| `Finset.exists_maximal` | `Order/Preorder/Finite.lean:44` | maximal proper normal subgroup |

### 3.5 P-construction and complex trigonometry

| declaration | file | use |
|---|---|---|
| `PConstructible` | `Pptc/Defs.lean` | target predicate |
| `sqrt_Pconstructible` | `Pptc/Basic.lean:236` | modulus |
| `arccos_Pconstructible_of_mem_Icc` | `Pptc/Basic.lean:1696` | argument |
| `pi_Pconstructible` | `Pptc/Basic.lean:1732` | `π` |
| `rpow_Pconstructible` | `Pptc/Basic.lean:1783` | `r ^ (1/n)` |
| `cos_Pconstructible`, `sin_Pconstructible` | `Pptc/Basic.lean:2673,2678` | De Moivre and roots of unity |
| `Complex.cos_add_sin_mul_I_pow` | `Analysis/Complex/Trigonometric.lean:539` | De Moivre |
| `Complex.exp_ofReal_mul_I` | `Analysis/Complex/Trigonometric.lean:529` | roots of unity as `cos + sin I` |
| `Complex.mem_rootsOfUnity` | `RingTheory/RootsOfUnity/Complex.lean` | explicit classification of `n`-th roots of unity |
| `Real.rpow_inv_natCast_pow` | `Analysis/SpecialFunctions/Pow/Real.lean:511` | `(r^(1/n))^n = r` |

---

## 4. Proof architecture

Five milestones, in dependency order. Milestones 1 and 2 are P-only and can be landed
first; milestone 3 is pure Galois theory; milestone 4 joins them; milestone 5 exposes the
issue's headline.

### Milestone 1: `PConstructibleC` is a subfield of `ℂ`

Define

```lean
def PConstructibleC (z : ℂ) : Prop :=
  PConstructible z.re ∧ PConstructible z.im
```

Prove closure under `0`, `1`, `+`, `-`, `*`, `⁻¹`, and rational constants. The coordinate
formulas are:

```text
(z + w).re = z.re + w.re,          (z + w).im = z.im + w.im
(z * w).re = z.re*w.re - z.im*w.im, (z * w).im = z.re*w.im + z.im*w.re
z⁻¹ = (z.re - z.im*I) / (z.re^2 + z.im^2)
```

The inverse formula is valid with Lean's total division even at `z = 0` (both sides are
`0`), so no nonzero hypothesis is needed for the field structure. Then package:

```lean
def PComplexField : Subfield ℂ where
  carrier := {z | PConstructibleC z}
  ...

def PComplex : IntermediateField ℚ ℂ :=
  PComplexField.toIntermediateField (fun q => ...)   -- `rat_Pconstructible`
```

and the membership lemma `z ∈ PComplex ↔ PConstructibleC z`.

This step is bookkeeping; all ingredients are in `Pptc/Basic.lean`.

### Milestone 2: `PComplex` is closed under roots

Two lemmas.

**(a) Existence of a P-coordinate root.** For `z ∈ PComplex`, `z ≠ 0`, `n ≠ 0`, produce
`w ∈ PComplex` with `w ^ n = z`.

Write `a = z.re`, `b = z.im`, `r = sqrt (a^2 + b^2)`.

* `r` is P-constructible and positive (`sqrt_Pconstructible`).
* `u = a / r ∈ [-1,1]` (from `|a| ≤ sqrt (a^2+b^2)`; `Real.abs_le_sqrt`).
* Define
  ```lean
  θ := if 0 ≤ b then Real.arccos u else -Real.arccos u
  ```
  Then `θ` is P-constructible (`arccos_Pconstructible_of_mem_Icc`, `neg_Pconstructible`).
  Prove the two facts
  ```lean
  Real.cos θ = a / r
  Real.sin θ = b / r
  ```
  using `Real.cos_arccos`, `Real.sin_arccos`, `Real.sqrt_sq_eq_abs`, and the sign
  hypothesis. This is the fiddliest trigonometric lemma; isolate it as
  `exists_P_angle` so the rest of the proof does not see the case split.
* Set
  ```lean
  w := ⟨r ^ (1/n) * Real.cos (θ/n), r ^ (1/n) * Real.sin (θ/n)⟩
  ```
  Its coordinates are P (`rpow_Pconstructible`, `cos_Pconstructible`,
  `sin_Pconstructible`).
* Prove `w ^ n = z` in `ℂ`:
  * `(r^(1/n))^n = r` via `Real.rpow_inv_natCast_pow` and `0 < r`;
  * `(cos(θ/n) + sin(θ/n) I)^n = cos θ + sin θ I` via
    `Complex.cos_add_sin_mul_I_pow` and `n * (θ/n) = θ` (from `n ≠ 0`);
  * multiply by `r` and rewrite `r*(a/r) = a`, `r*(b/r) = b`.

**(b) Root closure.** For `z : ℂ`, `n ≠ 0`, `z ^ n ∈ PComplex`, show `z ∈ PComplex`.

* If `z = 0`, use `0 ∈ PComplex`.
* Otherwise `z^n ≠ 0`. Let `y := z^n`, obtain a P-coordinate root `w` of `y`
  from (a), so `w^n = y = z^n`.
* Then `ζ := z / w` satisfies `ζ^n = 1`, hence `ζ` is a complex root of unity.
* Classify `ζ`: use `Complex.mem_rootsOfUnity n` to write
  `ζ = exp (2πI i/n)` for some `i < n`. (Make `ζ` a unit using `ζ^n = 1`,
  and use `NeZero n`.)
* Show `ζ ∈ PComplex`: rewrite `exp (2πI i/n)` as
  `exp ((2π * i/n) * I)` and use `Complex.exp_ofReal_mul_I`; the angle
  `2π * i/n` is P (`pi_Pconstructible`), hence `cos` and `sin` are P.
* Conclude `z = w * ζ ∈ PComplex` by field closure.

Note the direction: `solvableByRad_le` asks for `x^n ∈ s → x ∈ s`, so (b) is exactly
what is required; the ratio-by-roots-of-unity step is not avoidable, because `z` may be
any one of the `n` roots.

### Milestone 3: solvable `Gal` has a cyclic-prime tower

This is pure field theory, with no P content. Prove the following two lemmas.

**(a) Maximal normal subgroup and prime cyclic quotient.** If `G` is finite, nontrivial,
and solvable, there is `N : Subgroup G` with `N.Normal`, `N < ⊤`, and
`Nat.card (G ⧸ N)` prime.

* Take a maximal proper normal subgroup using `Finset.exists_maximal` on the finite set
  of proper normal subgroups (the top subgroup is excluded).
* `G ⧸ N` is simple, and it is solvable as a quotient of `G`
  (`Group.isSolvable_of_surjective`).
* A simple solvable group is commutative (`IsSimpleGroup.comm_iff_isSolvable`), hence
  cyclic of prime order (`IsSimpleGroup.isCyclic`, `IsSimpleGroup.prime_card`).

**(b) Kummer step.** Let `K ⊆ L` be a finite Galois extension, `Gal(L/K)` solvable,
and suppose `K` contains a primitive `m`-th root of unity with
`Nat.card Gal(L/K) ∣ m`. If `L ≠ K`, then there is an intermediate field
`K ≤ F ≤ L` with:

* `F` is Galois over `K` (`IsGalois.of_fixedField_normal_subgroup`);
* `Gal(F/K)` is cyclic of prime order `p`;
* `p ∣ m`, so `K` contains `μ_p`;
* `F = K(β)` and `β ^ p ∈ K` (`exists_root_adjoin_eq_top_of_isCyclic`);
* `Gal(L/F)` is solvable and `Nat.card Gal(L/F) < Nat.card Gal(L/K)`.

Take `N` from (a), let `F := fixedField N`, and use
`IsGalois.normalAutEquivQuotient N` to identify `Gal(F/K)` with `G ⧸ N`.
The Kummer lemma applies because `K` contains `μ_p`; the degree is `p` because
`[F:K] = Nat.card Gal(F/K) = p`.

### Milestone 4: Galois-solvable implies radical

Prove `mem_solvableByRad_of_isSolvable_gal`. The proof is a well-founded induction on
`Nat.card Gal(L/K)` using Milestone 3.

Set `p := minpoly ℚ z`, `d := Nat.card p.Gal`, `m := d!`, and

```lean
K₀ := IntermediateField.adjoin ℚ ({ζ_m})          -- ζ_m a primitive m-th root of unity in ℂ
L  := IntermediateField.adjoin K₀ (p.rootSet ℂ)   -- splitting field of p over K₀
```

Then:

1. `p ≠ 0` and `p` is separable (char 0), so `L/K₀` is a separable splitting field,
   hence finite Galois over `K₀`.
2. `z ∈ L`, because `z` is a root of `p`.
3. `Gal(L/K₀)` is solvable: it is a subgroup of `Gal(L/ℚ)`, and `L/ℚ` is the compositum
   of the splitting field of `p` over `ℚ` with `K₀`; its group embeds in
   `p.Gal × Gal(K₀/ℚ)`, both solvable.  Equivalently, use
   `IsGalois.tower_top_of_isGalois` and the subgroup instance.
4. **Prime divisibility instead of exact divisibility.**  We do not need
   `Nat.card Gal(L/K₀) ∣ m`; it is enough that every prime dividing
   `Nat.card Gal(L/K₀)` divides `m`.  Indeed,
   * `finrank ℚ L ≤ finrank ℚ (p.SplittingField) * finrank ℚ K₀`
     (`IntermediateField.finrank_sup_le`), and the first factor is `d`
     (`Polynomial.card_of_separable` plus `IsSplittingField.algEquiv`);
   * `finrank ℚ K₀ ≤ m` (the minimal polynomial of `ζ_m` divides `X^m - 1`);
   * so `Nat.card Gal(L/K₀) ∣ Nat.card Gal(L/ℚ) ≤ d * m`;
   * every prime dividing `d * m` divides `m` because `m = d!` contains every prime
     `≤ d`.
   This is why the tower lemma takes the weaker hypothesis
   `∀ p, p.Prime → p ∣ Nat.card Gal(L/K) → p ∣ m`.
5. `K₀ ⊆ solvableByRad ℚ ℂ`: `ζ_m^m = 1`, so `ζ_m` is in the radical closure; then use
   `adjoin_le_iff`.
6. Apply the induction lemma of Milestone 3 to the extension `L/K₀`:
   * every prime occurring in the tower divides `m`, so `K₀` contains the needed roots
     of unity (`primitiveRoots p K₀` is nonempty for each such `p`);
   * the induction step replaces `K` by an intermediate field `F` with
     `K ⊆ F ⊆ L`; `F` also contains `K₀`, so the root-of-unity hypothesis persists;
   * at each step, `F = K(β)` with `β^p ∈ K`; since `K ⊆ solvableByRad` and
     `solvableByRad` is a field, `β ∈ solvableByRad` by `solvableByRad.rad_mem`, hence
     `F ⊆ solvableByRad`;
   * at the end, `L ⊆ solvableByRad`, and `z ∈ L`.

**Formalization note.** The induction is over `IntermediateField`s inside `L`, but the
statement `F ⊆ solvableByRad` is about the ambient `ℂ`. Use the coercion
`IntermediateField K L → IntermediateField ℚ ℂ` (`restrictScalars`) or state the
induction with all fields as `IntermediateField ℚ ℂ` and use `Gal(L/K)` with the
`IntermediateField.algebra` instance. Prototype this in `Pptc/Scratch/` before writing
the full file; it is the main Lean-engineering risk, not a mathematical one.

### Milestone 5: headline and corollaries

```lean
theorem root_Pconstructible_of_solvable_gal {q : ℚ[X]} (hq : q ≠ 0)
    (hgal : Group.IsSolvable q.Gal) {α : ℝ} (hα : aeval α q = 0) :
    PConstructible α := by
  -- 1. p := minpoly ℚ α divides q.
  -- 2. Surjection q.Gal →* p.Gal (Gal.restrictDvd_surjective) gives solvability of p.Gal.
  -- 3. minpoly ℚ (α : ℂ) = minpoly ℚ α (minpoly.algebraMap_eq, Complex.ofReal injective).
  -- 4. Milestone 4: (α : ℂ) ∈ solvableByRad ℚ ℂ.
  -- 5. Milestone 2: PConstructibleC (α : ℂ).
  -- 6. (α : ℂ).re = α, so PConstructible α.
```

Corollaries:

```lean
theorem solvable_real_algebraic_Pconstructible {α : ℝ}
    (hα : IsAlgebraic ℚ α) (hgal : Group.IsSolvable (minpoly ℚ α).Gal) :
    PConstructible α

theorem solvable_complex_algebraic_PConstructible {z : ℂ}
    (hz : IsAlgebraic ℚ z) (hgal : Group.IsSolvable (minpoly ℚ z).Gal) :
    PConstructibleC z
```

The complex corollary is useful internally and costs nothing.

---

## 5. File layout and imports

New directory `Pptc/Solvable/`, following the `Pptc/Octic/`, `Pptc/Nonic/` pattern:

| file | content |
|---|---|
| `Pptc/Solvable/Basic.lean` | `PConstructibleC`, `PComplex`, subfield closure, Milestone 1 |
| `Pptc/Solvable/Roots.lean` | `exists_P_angle`, `exists_PComplex_nth_root`, `PComplex.mem_of_pow_mem`, Milestone 2 |
| `Pptc/Solvable/Galois.lean` | maximal normal subgroup, cyclic-prime tower, induction lemma, Milestone 3 |
| `Pptc/Solvable/AbelRuffini.lean` | `mem_solvableByRad_of_isSolvable_gal`, Milestone 4 |
| `Pptc/Solvable/Main.lean` | headline and corollaries, Milestone 5 |

Add `import Pptc.Solvable.Main` to `Pptc.lean`.

**Imports are targeted, never `import Mathlib`:**
`Mathlib.FieldTheory.AbelRuffini`,
`Mathlib.FieldTheory.KummerExtension`,
`Mathlib.FieldTheory.Galois.Basic`,
`Mathlib.FieldTheory.SplittingField.Construction`,
`Mathlib.RingTheory.RootsOfUnity.Complex`,
`Mathlib.Analysis.Complex.Trigonometric`,
`Mathlib.GroupTheory.Solvable`,
`Mathlib.GroupTheory.SpecificGroups.Cyclic`,
`Mathlib.Order.Preorder.Finite`,
plus `Pptc.Basic`.

Do **not** add the Galois imports to `Pptc/Basic.lean`; keep that file's import cost flat.

---

## 6. Detailed Lean targets

These are the signatures to aim at. Names are provisional but the types are the plan.

### 6.1 Complex field

```lean
namespace Pconstructible

def PConstructibleC (z : ℂ) : Prop :=
  PConstructible z.re ∧ PConstructible z.im

theorem PConstructibleC.zero : PConstructibleC 0
theorem PConstructibleC.one : PConstructibleC 1
theorem PConstructibleC.add {z w : ℂ} :
    PConstructibleC z → PConstructibleC w → PConstructibleC (z + w)
theorem PConstructibleC.neg {z : ℂ} : PConstructibleC z → PConstructibleC (-z)
theorem PConstructibleC.mul {z w : ℂ} :
    PConstructibleC z → PConstructibleC w → PConstructibleC (z * w)
theorem PConstructibleC.inv {z : ℂ} : PConstructibleC z → PConstructibleC z⁻¹

def PComplexField : Subfield ℂ
def PComplex : IntermediateField ℚ ℂ

@[simp] theorem mem_PComplex {z : ℂ} :
    z ∈ PComplex ↔ PConstructibleC z

end Pconstructible
```

### 6.2 Angles and roots

```lean
/-- The modulus-angle representation of a nonzero complex number, with P coordinates. -/
theorem exists_P_angle {a b : ℝ} (ha : PConstructible a) (hb : PConstructible b)
    (hne : a ≠ 0 ∨ b ≠ 0) :
    ∃ θ : ℝ, PConstructible θ ∧
      Real.cos θ = a / Real.sqrt (a ^ 2 + b ^ 2) ∧
      Real.sin θ = b / Real.sqrt (a ^ 2 + b ^ 2)

theorem exists_PComplex_nth_root {z : ℂ} (hz : z ∈ PComplex) {n : ℕ} (hn : n ≠ 0) :
    ∃ w : ℂ, w ∈ PComplex ∧ w ^ n = z

theorem PComplex.mem_of_pow_mem {z : ℂ} {n : ℕ} (hn : n ≠ 0)
    (hz : z ^ n ∈ PComplex) : z ∈ PComplex
```

### 6.3 Radical closure

```lean
theorem mem_PComplex_of_mem_solvableByRad {z : ℂ}
    (hz : z ∈ solvableByRad ℚ ℂ) : z ∈ PComplex := by
  refine solvableByRad_le (s := PComplex) ?_ hz
  intro x n hn hx
  exact PComplex.mem_of_pow_mem hn hx
```

This is deliberately short: Milestone 2 carries all the content.

### 6.4 Galois tower

```lean
/-- A finite nontrivial solvable group has a maximal proper normal subgroup with
cyclic quotient of prime order. -/
theorem exists_maximal_normal_prime_quotient {G : Type*} [Group G] [Finite G]
    (h : Group.IsSolvable G) [Nontrivial G] :
    ∃ N : Subgroup G, N.Normal ∧ N < ⊤ ∧ (Nat.card (G ⧸ N)).Prime

/-- Solvable Galois extensions can be filtered by cyclic prime-degree Kummer steps,
provided the base contains enough roots of unity. -/
theorem le_solvableByRad_of_solvable_tower
    {K L : IntermediateField ℚ ℂ} (hK : K ≤ solvableByRad ℚ ℂ) (hKL : K ≤ L)
    [FiniteDimensional K L] [IsGalois K L]
    (hsolv : Group.IsSolvable Gal(L/K))
    (m : ℕ) (hprime : ∀ p, p.Prime → p ∣ Nat.card Gal(L/K) → p ∣ m)
    (hmu : ∀ p, p.Prime → p ∣ m → (primitiveRoots p K).Nonempty) :
    L ≤ solvableByRad ℚ ℂ
```

### 6.5 Main

```lean
theorem mem_solvableByRad_of_isSolvable_gal {z : ℂ}
    (hz : IsAlgebraic ℚ z) (h : Group.IsSolvable (minpoly ℚ z).Gal) :
    z ∈ solvableByRad ℚ ℂ

theorem root_Pconstructible_of_solvable_gal {q : ℚ[X]} (hq : q ≠ 0)
    (hgal : Group.IsSolvable q.Gal) {α : ℝ} (hα : aeval α q = 0) :
    PConstructible α

theorem solvable_real_algebraic_Pconstructible {α : ℝ}
    (hα : IsAlgebraic ℚ α) (hgal : Group.IsSolvable (minpoly ℚ α).Gal) :
    PConstructible α
```

---

## 7. Known gaps, risks, and fallbacks

1. **The converse Abel–Ruffini is the largest piece.** It is not in Mathlib. The plan
   isolates it in `Pptc/Solvable/AbelRuffini.lean`; Milestones 1–2 do not depend on it.
   If it proves too slow, the radical-tower theorem
   `mem_PComplex_of_mem_solvableByRad` is still a publishable intermediate result, and
   the headline can temporarily take `(α : ℂ) ∈ solvableByRad ℚ ℂ` as its hypothesis.
   Do not state the headline with that hypothesis permanently; the issue asks for the
   Galois-group form.

2. **Root-of-unity classification.** `Complex.mem_rootsOfUnity` is the intended API; it
   gives an explicit `exp (2πI i/n)` for every `n`-th root of unity. The alternative,
   proving that `nthRoots n 1` is exhausted by `exp (2πI i/n)` via cardinality, is a
   fallback if the unit coercion is awkward.

3. **`IntermediateField` induction.** The induction in Milestone 4 mixes
   `IntermediateField ℚ ℂ` with `Gal(L/K)`. Prototype the tower lemma in
   `Pptc/Scratch/TowerTest.lean` first. If the mixed instances are painful, state the
   tower lemma for a chain of `IntermediateField ℚ ℂ` and carry `K ≤ L` explicitly.

4. **Divisibility bookkeeping.** The choice `m = Nat.card p.Gal` is deliberate: every
   prime in the tower over `K₀` divides `|Gal(L/K₀)|`, which divides `|Gal(E/ℚ)| = m`
   because restriction to `E` is injective. Keep this argument in the file, not only in
   the plan.

5. **`q.Gal` versus `minpoly`.** `q.Gal` is the Galois group of `q`'s splitting field.
   For the headline, `minpoly ℚ α ∣ q` and `Gal.restrictDvd_surjective` give a surjection
   `q.Gal →* (minpoly ℚ α).Gal`; solvability descends along surjections. Do not try to
   identify the two groups.

6. **Total division in `ℂ`.** The formulas for inverse and for `z / w` use Lean's total
   division; the zero cases evaluate to `0` and are harmless. Do not add nonzero
   hypotheses to the subfield operations; add them only where `w ^ n = z` is used
   (`z ≠ 0` for the root construction).

---

## 8. Benchmarks and acceptance criteria

### 8.1 Concrete test cases

* **`cos (2π/23)`.** The issue's example. The Galois group of the real cyclotomic
  subfield is `(Z/23)^* / ±1`, cyclic of order 11, hence solvable. The minimal
  polynomial has degree 11 (not 22: `cos` lies in the real subfield), so this is a
  genuine new instance beyond the existing degree-≤ 8 theorem.
  The plan should add a small file or example proving
  `PConstructible (Real.cos (2 * Real.pi / 23))` from
  `root_Pconstructible_of_solvable_gal`.
* **`cos (2π/7)`** (cubic, solvable) as a sanity check that overlaps existing degree-3
  machinery.
* **A complex root of `X^2 + 1`** as a unit test for Milestone 2:
  `PConstructibleC Complex.I`.
* **`2 * Real.cos (2π/11)`** (degree 5, cyclic, solvable).

The first and fourth are the important ones: they are not reachable by the existing
degree-≤ 8 theorem.

### 8.2 Acceptance

* No `sorry`, no `admit`, no new axioms.
* `lake build Pptc` succeeds; the new files also checked individually with
  `lake env lean Pptc/Solvable/Main.lean`.
* `lean_verify` on the headline reports only the standard Mathlib axioms
  (`propext`, `Classical.choice`, `Quot.sound`).
* The headline has exactly the hypotheses in §2.3, with no hidden radical-tower
  hypothesis.
* The module docstring states the paper source (`X1` §2.2, §4) and the two directions
  of Abel–Ruffini.

---

## 9. Non-goals

* No induction on the degree of the polynomial. The theorem is uniform in the degree;
  the induction is on the solvable series of the Galois group.
* No real radical towers. The whole point of X1 §2.2 is that complex radicals are free
  in P because `cos`, `sin`, `arccos`, `rpow` are constructors/lemmas. A real-root-only
  proof would hit the swap obstruction in X1 §2.3.
* No change to `Pptc/Defs.lean` and no new constructor.
* No attempt to prove the converse for non-solvable groups (that is false: `S_5`).
* No attempt to formalize Theorem X or the `(SR)` hypothesis from X1; this issue is
  the unconditional solvable case only.

---

## 10. Ordering for the implementer

1. `Pptc/Solvable/Basic.lean`: Milestone 1, with `PConstructibleC` and `PComplex`.
2. `Pptc/Solvable/Roots.lean`: `exists_P_angle` first (standalone trig), then
   `exists_PComplex_nth_root`, then `PComplex.mem_of_pow_mem`.
3. `Pptc/Solvable/Roots.lean`: `mem_PComplex_of_mem_solvableByRad`. This completes the
   unconditional radical-tower theorem.
4. `Pptc/Scratch/TowerTest.lean`: prototype the `IntermediateField` induction and the
   maximal-normal-subgroup lemma on a small example.
5. `Pptc/Solvable/Galois.lean`: Milestone 3.
6. `Pptc/Solvable/AbelRuffini.lean`: Milestone 4.
7. `Pptc/Solvable/Main.lean`: Milestone 5, then the benchmarks.
8. Add imports to `Pptc.lean`, run the full build, and check axioms.
