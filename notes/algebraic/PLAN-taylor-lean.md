# PLAN-taylor-lean: formalizing Taylor ⇒ R_alg ⊆ P in Lean

Status: **proposed (2026-11-11).** Companion to `X1.md` (Theorem X), `PLAN-algebraic.md`
(stream X1), and `Pptc/Solvable/Main.lean`. This plan formalizes the conditional theorem

> Taylor’s question (for the trinomial surface) ⇒ every real algebraic number is
> P-constructible,

and collects weaker point-existence statements that imply the same conclusion. It does **not**
prove Taylor’s question, which is open.

Labels: [Lean], [Proof], [Interface], [Open], [Heuristic].

---

## 0. Executive summary

The proof has two very different halves:

1. **P half (formalizable now).** From a suitable point on the trinomial surface, reconstruct
   the target algebraic number β and show β is P-constructible.
2. **Geometry/arithmetic half (hard, partly open).** Produce that point from Taylor’s question
   or from a weaker hypothesis.

The key recent Lean fact is `Pptc/Solvable/Main.lean`:

```lean
theorem root_Pconstructible_of_solvable_gal {α : ℝ} {q : ℚ[X]}
    (hq : q ≠ 0) (h : Group.IsSolvable q.Gal) (hα : aeval α q = 0) :
    PConstructible α
```

This already proves that **every solvable real algebraic number is P**. Consequently, the
power-law/trinomial engine in the paper proof of X1 Theorem X is **not needed** for the
conditional theorem from (SR): the point over `Q^solv ∩ R` already has P-constructible
coordinates, and the remaining work is the **polynomial-gcd recovery**. The engine becomes an
optional constructive strengthening.

Unlike the rank-one offset deformation of Y1b, this route is **not circular**: the trinomial
`x^D + a*x + b` is a genuine geometric `S_D`/`A_D` engine, and the solvable field supplies only
the coordinates, not the Galois group of the crossing.

This reduces the formalization to:

- a generic **lift/recovery theorem** (`TrinomialLift` → `PConstructible β`);
- a **hypothesis hierarchy** of point-existence statements, all discharging the same
  coordinate predicate;
- a separate, optional **geometry interface** for Taylor ⇒ point existence.

The immediate Lean target is therefore modest and useful:

```lean
theorem realAlgebraic_Pconstructible_of_taylorTrinomial
    (h : ∀ β : ℝ, IsAlgebraic ℚ β → TrinomialLift SolvableReal β) :
    ∀ β : ℝ, IsAlgebraic ℚ β → PConstructible β
```

The full statement with Taylor’s question is obtained by proving the geometric implication
`TaylorPSC → ∀ β, IsAlgebraic ℚ β → TrinomialLift SolvableReal β`, which is the long-term
part.

---

## 1. Target statements

### 1.1 The unconditional-looking target

```lean
/-- Every real algebraic number is P-constructible, conditional on the Taylor/trinomial
point hypothesis. -/
theorem realAlgebraic_Pconstructible_of_taylorTrinomial
    (hTaylor : TaylorTrinomial) :
    ∀ β : ℝ, IsAlgebraic ℚ β → PConstructible β
```

### 1.2 The geometric hypothesis

```lean
/-- Taylor's question, specialized to the trinomial surfaces used in X1 Theorem X. -/
def TaylorTrinomial : Prop :=
  ∀ β : ℝ, IsAlgebraic ℚ β → TrinomialLift SolvableReal β
```

This is the **honest formalization boundary**: `TaylorTrinomial` is the part that needs the
geometry of the trinomial surface and the PSC hypothesis; it is not proved here.

### 1.3 The generalized weaker-hypothesis theorem

```lean
/-- If every coordinate lies in a class `Coord` whose members are P-constructible, then
the lift gives β ∈ P. -/
theorem TrinomialLift.Pconstructible
    {Coord : ℝ → Prop} (hCoord : ∀ x, Coord x → PConstructible x)
    {β : ℝ} (h : TrinomialLift Coord β) :
    PConstructible β
```

This one theorem is the collection mechanism: every weaker hypothesis is an instance of
`Coord`.

---

## 2. What already exists in Lean

Use these, do not reprove them:

| lemma | file | use |
|---|---|---|
| `PConstructible.base_one`, `add`, `sub`, `mul`, `div` | `Pptc/Defs.lean` | field operations on P |
| `PConstructible.inter_x`, `inter_y` | `Pptc/Defs.lean` | reading roots off crossings |
| `PConstructibleCurve.power_law`, `poly_graph`, `linearMap`, `restrict` | `Pptc/Defs.lean` | optional trinomial engine |
| `root_Pconstructible_of_solvable_gal` | `Pptc/Solvable/Main.lean` | **the key shortcut** |
| `algebraic_Pconstructible_le_eight` | `Pptc/Basic.lean` | degree ≤ 8 coordinates |
| `root_Pconstructible_deg8_coeffs` | `Pptc/Octic/Main.lean` | degree ≤ 8 steps with P coefficients |
| `algebraic_Pconstructible_le_six` | `Pptc/Basic.lean` | low-degree sanity checks |
| `rats`/`rat_Pconstructible`, `exists_rat_isolating`, `exists_rat_box_isolating` | `Pptc/Basic.lean` | rational windows, optional engine |
| `linearMap_PConstructibleCurve`, `affineMap_PConstructibleCurve` | `Pptc/Basic.lean` | P-coefficient lines |

The only new foundational object needed is `PReal`, the subfield of P-constructible reals,
for the gcd recovery.

---

## 3. The logical skeleton

### 3.1 The lift data

A point on the relevant trinomial surface gives:

- `D : ℕ`, `D > 0`;
- `a b x₀ : ℝ` with `x₀^D + a*x₀ + b = 0`;
- `q : ℚ[X]`, the minimal polynomial of `y₀ = sqrt(β - c)`;
- `T : ℝ[X]`, the element `τ'` written in the basis `1, y₀, …, y₀^(D-1)`;
- `y₀ : ℝ` with `q(y₀)=0`, `x₀ = T(y₀)`;
- the **distinctness** of the conjugates: `T` is injective on the **complex** roots of `q`
  (not only the real ones; otherwise the gcd can pick up extra complex factors);
- `β = y₀² + c` (after a rational Möbius normalization; the general Möbius inverse is a
  field-operation wrapper).

The P content is independent of how the point was found. This is why the same lift theorem
serves all weaker hypotheses.

### 3.2 The generic lift theorem

```lean
structure TrinomialLift (Coord : ℝ → Prop) (β : ℝ) : Prop where
  D : ℕ
  hD : 0 < D
  a b x₀ : ℝ
  c : ℚ
  q : ℚ[X]
  T : ℝ[X]
  y₀ : ℝ
  ha : Coord a
  hb : Coord b
  hx₀ : Coord x₀
  hT : ∀ i, Coord (T.coeff i)
  hroot : x₀ ^ D + a * x₀ + b = 0
  hq : q ≠ 0
  hqy : aeval y₀ q = 0
  hq_sep : q.Separable
  hxT : x₀ = T.eval y₀
  -- Distinctness must be checked on **all** complex conjugates, not only the real roots:
  -- otherwise the gcd in `PReal[X]` can acquire extra complex factors.
  hinj : ∀ z₁ z₂ : ℂ,
    aeval z₁ (q.map (algebraMap ℚ ℂ)) = 0 →
    aeval z₂ (q.map (algebraMap ℚ ℂ)) = 0 →
    Polynomial.eval z₁ (T.map (algebraMap ℝ ℂ)) =
      Polynomial.eval z₂ (T.map (algebraMap ℝ ℂ)) → z₁ = z₂
  hβ : β = y₀ ^ 2 + c
```

Then:

```lean
theorem TrinomialLift.Pconstructible
    {Coord : ℝ → Prop} (hCoord : ∀ x, Coord x → PConstructible x)
    {β : ℝ} (h : TrinomialLift Coord β) :
    PConstructible β
```

### 3.3 Proof of the lift theorem

1. Convert every coordinate to P using `hCoord`.
2. Let `R(X) = T(X) - x₀`; its coefficients are P.
3. Work in `PReal[X]`, where `PReal` is the subfield of P-constructible reals.
4. Both `q` and `R` have `y₀` as a root, so `gcd(q, R)` is nontrivial.
5. The common roots of `q` and `R` in `ℂ` are exactly the roots `z` of `q` with
   `T(z)=x₀`. By `hinj` (checked on all complex roots), only `z=y₀` occurs. Since `q` is
   separable, `gcd(q, R)` is linear.
6. A linear polynomial over `PReal` with root `y₀` gives `y₀ ∈ PReal`.
7. `β = y₀² + c` is P.

The only delicate Lean point is step 5: the gcd is computed in `PReal[X]`, and its roots in
`ℝ` are the common roots. Mathlib’s `Polynomial.gcd`, `Polynomial.roots`, and separability
lemmas are enough; this is an algebraic task, not algebraic geometry.

---

## 4. PReal and the coordinate classes

### 4.1 PReal

```lean
/-- The subfield of P-constructible real numbers. -/
def PReal : Subfield ℝ where
  carrier := {x | PConstructible x}
  zero_mem' := ...
  one_mem' := PConstructible.base_one
  add_mem' := ...
  mul_mem' := ...
  neg_mem' := ...
  inv_mem' := ...
```

This is a straightforward but useful package. It lets the recovery use `PReal[X]` and
`Polynomial.gcd` without repeatedly unpacking `PConstructible`.

### 4.2 Coordinate predicates

```lean
/-- Real algebraic with solvable Galois closure. -/
def SolvableReal (x : ℝ) : Prop :=
  ∃ q : ℚ[X], q ≠ 0 ∧ Group.IsSolvable q.Gal ∧ aeval x q = 0

/-- Real algebraic of degree at most 8. -/
def DegreeLE8Real (x : ℝ) : Prop :=
  ∃ q : ℚ[X], q ≠ 0 ∧ q.natDegree ≤ 8 ∧ aeval x q = 0

/-- Real algebraic of degree at most 2. -/
def DegreeLE2Real (x : ℝ) : Prop :=
  ∃ q : ℚ[X], q ≠ 0 ∧ q.natDegree ≤ 2 ∧ aeval x q = 0

/-- Numbers reachable from ℚ by a tower of degree ≤ 8 roots with P coefficients, plus
solvable real numbers. -/
inductive PTowerReal : ℝ → Prop
  | rat (q : ℚ) : PTowerReal q
  | root8 {p : ℝ[X]} (hp : p ≠ 0) (hdeg : p.natDegree ≤ 8)
      (hcoeff : ∀ i, PTowerReal (p.coeff i)) {x : ℝ} (hx : p.eval x = 0) :
      PTowerReal x
  | solvable {q : ℚ[X]} (hq : q ≠ 0) (h : Group.IsSolvable q.Gal)
      {x : ℝ} (hx : aeval x q = 0) : PTowerReal x
```

Then:

```lean
theorem SolvableReal.Pconstructible : SolvableReal x → PConstructible x
theorem DegreeLE8Real.Pconstructible : DegreeLE8Real x → PConstructible x
theorem DegreeLE2Real.Pconstructible : DegreeLE2Real x → PConstructible x
theorem PTowerReal.Pconstructible : PTowerReal x → PConstructible x
```

`PTowerReal.Pconstructible` is by induction: `rat` uses rationals, `solvable` uses the
solvable-root theorem, `root8` uses `root_Pconstructible_deg8_coeffs` with the induction
hypothesis on the coefficients.

This is the **main new reusable result**: it turns any point over a P-tower into P.

---

## 5. The hypothesis collection (weaker than Taylor)

The generic `TrinomialLift Coord` turns every row below into the same conclusion `β ∈ P`.
The table records both the mathematical strength and the Lean status.

Here `K_solv = Q^solv ∩ R` and `K_tr,solv = Q^tr ∩ Q^solv`. Note
`K_tr,solv ⊂ K_solv`, so a point over `K_tr,solv` is also a point over `K_solv`.

| hypothesis | statement | why it implies P | Lean status |
|---|---|---|---|
| `TaylorPSC` | PSC for all smooth geometrically integral ℚ-varieties with a real point, over `K_tr,solv` (Taylor’s field) | X1 Theorem X via `SR_tot` | [Interface], open |
| `PSCForI_tot` | PSC only for the trinomial surfaces `I_{K'}`, over `K_tr,solv` | gives `SR_tot` | [Interface], open |
| `PSCForI_solv` | PSC only for `I_{K'}`, over `K_solv` | gives `SR` | [Interface], open |
| `SR_tot` | point of `I_{K'}` over `K_tr,solv` | `K_tr,solv ⊂ K_solv`, then `SR` | [Open], Taylor-specific |
| `SR` | point of `I_{K'}` over `K_solv` | `SolvableReal → P` + recovery | **target** (T1) |
| `SR_tower` | point over `PTowerReal` coordinates | `PTowerReal → P` | **target** (T0/T1) |
| `SR_8` | real point of degree ≤ 8 | `DegreeLE8Real → P` | [Open], searchable |
| `SR_quad` | real point over a real quadratic field | `DegreeLE2Real → P` | [Open], easiest search |
| `SR_0cycle8` | real 0-cycle of degree ≤ 8 (real support) | a real point of degree ≤ 8 | [Open], Faltings/Chabauty |
| `SR_cover8` | rational point on a real degree ≤ 8 cover of `I_{K'}` | image point of degree ≤ 8 | [Open] |
| `SR_Brauer` | a Brauer/Wooley-type theorem for `I_{K'}` | `SR` | [Open], likely out of range |
| `SR_F` | point over `F = P ∩ R_alg` | coordinates are P by definition | [Interface], tautological |

Implication arrows:

```
TaylorPSC
  ⇒ PSCForI_tot
  ⇒ SR_tot
  ⇒ SR
  ⇒ SR_tower
  ⇒ P

PSCForI_solv
  ⇒ SR
  ⇒ SR_tower
  ⇒ P

SR_quad ⇒ SR_8 ⇒ SR_tower ⇒ P
SR_0cycle8 ⇒ SR_8
SR_cover8 ⇒ SR_8
SR_F ⇒ P
```

The arrows `SR_tot → SR`, `SR → SR_tower`, `SR_8 → SR_tower`, `SR_quad → SR_8` are formal
Lean lemmas once the predicates are defined. The arrows involving `TaylorPSC`/`PSCForI` are
the geometric/arithmetic work. `PSCForI_solv` is a **weaker** PSC statement than Taylor
(larger field), but it is still enough for `SR`.

### 5.1 Why these are the right weakenings for our scenario

Taylor’s question is about **all** smooth varieties. Our proof uses **one** surface `I_{K'}`,
so the natural weakening is:

1. **`PSCForI_tot` / `PSCForI_solv`:** PSC only for `I_{K'}`. This is much weaker than
   Taylor and still enough.
2. **`SR_tot` / `SR`:** a point, not a local-global principle; weaker than PSC for `I`.
3. **`SR_tower` / `SR_8` / `SR_quad`:** replace the huge field `K_solv` by a small
   P-constructible field. These are stronger in field size but much easier to search for.
4. **`SR_0cycle8` / `SR_cover8`:** replace a point by a low-degree 0-cycle or a rational
   point on a low-degree cover. This is the most promising “small arithmetic” weakening.

The point of the hierarchy is to separate the **P recovery** (already formalizable) from the
**arithmetic existence** (the actual open problem).

### 5.2 Recommended search targets

The smallest useful experiments are:

- **n = 5**, where the paper already has an end-to-end tower; look for an explicit real
  quadratic or degree ≤ 8 point on `I_{K'}`.
- **n = 7 or 9**, using the trinomial curve equations from H1; search for a real quadratic
  point first, then a degree ≤ 8 point, then a real 0-cycle of degree ≤ 8.
- **Covers:** search for rational points on the natural degree-2 and degree-4 covers of
  `I_{K'}`; a hit gives a degree ≤ 8 point after the image.
- **0-cycles:** use Faltings/Chabauty or explicit equations to look for a real 0-cycle of
  degree ≤ 8 on `Γ_{K'}` / `I_{K'}`.

A hit is an **unconditional** `PConstructible β` for that β after T1/T2; a clean negative
sharpens which weakening is plausible.

---

## 6. Module and task plan

Proposed files under `Pptc/Taylor/`:

| file | contents |
|---|---|
| `Pptc/Taylor/Field.lean` | `PReal`, `SolvableReal`, `DegreeLE8Real`, `DegreeLE2Real`, `PTowerReal`, their `PConstructible` wrappers |
| `Pptc/Taylor/Lift.lean` | `TrinomialLift`, `TrinomialLift.Pconstructible`, Möbius/square recovery |
| `Pptc/Taylor/Statement.lean` | `TaylorTrinomial`, `SR`, the main conditional theorem |
| `Pptc/Taylor/Engine.lean` | optional: P-coefficient line curve, `trinomial_root_Pconstructible`, root isolation |
| `Pptc/Taylor/Geometry.lean` | long-term: the surface `I_{K'}`, smooth/geometrically integral/real point, `TaylorPSC → TaylorTrinomial` |
| `Pptc/Taylor/Main.lean` | imports and final theorem; import this from `Pptc.lean` |

### Tasks

| id | model | deliverable |
|---|---|---|
| T0 | Lean (standard) | **`PReal` and coordinate wrappers.** Prove `PReal` is a subfield; `SolvableReal → P`, `DegreeLE8Real → P`, `DegreeLE2Real → P`, `PTowerReal → P`. |
| T1 | Lean (standard) | **The generic lift theorem.** Define `TrinomialLift`; prove `TrinomialLift.Pconstructible` via `PReal[X]` gcd; add the Möbius inverse wrapper. |
| T2 | Lean (standard) | **Conditional main theorem.** `realAlgebraic_Pconstructible_of_taylorTrinomial`; `SR` as `TrinomialLift SolvableReal`; all weaker-hypothesis corollaries. |
| T3 | Lean (optional) | **Trinomial engine.** P-coefficient line curve; `trinomial_root_Pconstructible`; root isolation. This is a constructive strengthening, not needed for T2. |
| T4 | Lean + math (hard) | **Geometry of `I_{K'}`.** Define the surface, prove smooth/geometrically integral/real point, and derive `TaylorTrinomial` from `PSCForI`/Taylor. |
| T5 | Lean + math (pilot) | **A concrete unconditional case.** For a fixed small β (e.g. n=5 or a chosen n=7), find an explicit real quadratic or degree≤8 point on `I_{K'}`; instantiate `TrinomialLift` and get `PConstructible β` unconditionally. |
| T6 | math (search) | **Low-degree points.** Search `SR_quad`, `SR_8`, `SR_0cycle8`, `SR_cover8` for small K'. A hit is a new unconditional case; a clean negative sharpens the hypothesis. |

### Order

- **T0 → T1 → T2** is the critical path and has no geometric input. This should be the first
  Lean stream.
- **T3** can run in parallel; it is independent of the geometry and useful as a fallback.
- **T5** can start as soon as T1/T2 compile; it turns the conditional theorem into concrete
  unconditional instances.
- **T4/T6** are the long-term research frontier.

---

## 7. Formalization details and challenges

### 7.1 The gcd recovery

This is the main new algebraic lemma. A precise skeleton:

```lean
-- `q` and `R` are in `PReal[X]`; `hinj` says their common roots in `ℂ` are unique.
lemma exists_linear_gcd_of_inj_on_complex_roots
    {q R : PReal[X]} (hq : q ≠ 0) (hsep : q.Separable)
    {y₀ : ℝ} (hy : aeval y₀ q = 0) (hR : aeval y₀ R = 0)
    (hinj : ∀ z₁ z₂ : ℂ,
      aeval z₁ (q.map (algebraMap PReal ℂ)) = 0 →
      aeval z₂ (q.map (algebraMap PReal ℂ)) = 0 →
      aeval z₁ (R.map (algebraMap PReal ℂ)) = 0 →
      aeval z₂ (R.map (algebraMap PReal ℂ)) = 0 → z₁ = z₂) :
    ∃ g : PReal[X], g.natDegree = 1 ∧ aeval y₀ g = 0
```

Then `y₀ ∈ PReal` because a linear polynomial over a field has its root in the field.

If `PReal[X]` gcd is awkward, an alternative is to use the **resultant** of `q` and `R`:
the resultant vanishes, and the unique common root gives a linear factor; but the gcd route
is closer to the paper proof.

### 7.2 The square lift and Möbius map

The paper chooses a rational Möbius map so that β is the largest real conjugate, then sets
`y₀ = sqrt(β - c)`. The Lean lift can take `β = y₀² + c` as the normalized form; the general
case is a rational Möbius transformation

```lean
lemma mobius_Pconstructible {a b c d x : ℝ} (hx : PConstructible x)
    (ha : PConstructible a) ... (hden : c*x+d ≠ 0) :
    PConstructible ((a*x+b)/(c*x+d))
```

This is immediate from field closure. Keep the lift normalized; add the Möbius wrapper
separately.

### 7.3 `PTowerReal` induction

`root8` uses `root_Pconstructible_deg8_coeffs`, which takes a polynomial over `ℝ` with
P-constructible coefficients. The induction hypothesis gives P for each coefficient. The
`sovable` constructor uses `root_Pconstructible_of_solvable_gal` with rational coefficients.
This is a clean induction; the only work is the coefficient conversion.

### 7.4 Geometry

The surface `I_{K'}` and the Taylor implication are the hard part:

- `K' = Q(y₀)`, degree D; the trinomial `X^D + aX + b` has D roots;
- `I_{K'}` is the set of tuples `(x₁,…,x_D,a,b)` with the roots distinct and stable under the
  Galois action of `K'`;
- over `Q̄`, it is the variety of ordered tuples of roots of a common trinomial;
- it is smooth (simple roots) and geometrically integral (monodromy S_D);
- it has a real point because `K'` has 1 or 2 real places and a real trinomial with exactly
  that many real roots;
- Taylor/PSC then gives a point over `K_tr,solv = Q^tr ∩ Q^solv`, hence over
  `K_solv = Q^solv ∩ R`.

Formalizing this with schemes is a large project. The plan deliberately isolates it behind
`TaylorTrinomial` so the P half can land first.

### 7.5 What not to formalize

- Do **not** formalize the full PSC definition or Taylor’s question as an axiom in the core
  development. Keep it as a `Prop`/interface in `Statement.lean` or `Geometry.lean`.
- Do **not** depend on the trinomial engine for T2; the solvable-field shortcut is shorter.
- Do **not** attempt the general PSC scheme theory before T0–T2 are complete.

---

## 8. Risks and mitigations

| risk | mitigation |
|---|---|
| `PReal`/gcd recovery is more involved than expected | Start with the linear-factor lemma for a **separable** q; use `Polynomial.gcd` and `roots`; test on a fixed n=5 example. |
| `PTowerReal` induction has a subtle coefficient issue | Prove the degree≤8 wrapper first; add `solvable` as a separate constructor. |
| The geometry/Taylor interface is not formalizable soon | Keep `TaylorTrinomial` as the boundary; deliver the conditional theorem and concrete T5 instances. |
| The paper’s engine and the Lean shortcut diverge | Document the shortcut; keep T3 optional and independent. |
| Taylor’s question is open | Do not claim an unconditional proof; the Lean theorem is conditional. |

---

## 9. Success criteria

Minimum useful artifact:

- `PReal` compiles as a `Subfield ℝ`.
- `SolvableReal → P`, `DegreeLE8Real → P`, `PTowerReal → P` compile.
- `TrinomialLift.Pconstructible` compiles.
- `realAlgebraic_Pconstructible_of_taylorTrinomial` compiles.

Stronger artifact:

- `TrinomialLift` instances for `SR`, `SR_8`, `SR_quad`, `SR_tower` compile.
- A concrete unconditional `PConstructible β` instance (T5) compiles.
- The optional `trinomial_root_Pconstructible` engine compiles.

Long-term:

- `TaylorTrinomial` derived from a formalized `PSCForI` / Taylor hypothesis.
- A documented hierarchy of weaker hypotheses with Lean proofs of the implications that are
  formal.

---

## 10. Recommendation

Start with **T0 + T1 + T2**. This is the exact formal skeleton of X1 Theorem X, uses the
already-proved solvable-root theorem, and does not wait on the open geometry. In parallel,
run **T5/T6** searches for low-degree points on `I_{K'}`; a hit gives an unconditional case
and a concrete test of the lift. Treat **T4** (full Taylor/PSC geometry) as the long-term
frontier, not as a prerequisite for the Lean conditional theorem.
