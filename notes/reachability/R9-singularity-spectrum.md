# R9 — the singularity spectrum: no `1/log` or `δlogδ` in the tower

**Stream:** R9 of `notes/reachability/PLAN-routes.md` (wave 1, math/proof).
**Deliverable:** this file. Research only: **no `.lean` edit, no `lake` command.**
**Convention:** B (negative claims; R12 §2.5). The results below are B-theorems; under A the two
applications fail (R12 §1.4), while the log rows remain A-robust.

Sources read: `R3-separation.md` §1, §3.3, §4; `R7-dzero.md`; `R8-missing-curve-audit.md` §1–§3;
`R12-convention.md` §1.4, §3; `R2-tower.md` Q2–Q3; `Pptc/Defs.lean` (constructors).

Labels: **[Proof]**, **[Wolfram]**, **[Heuristic]**, **[Open]**. Backend: Wolfram Language,
40-digit working precision; cells in §6.

---

## 0. Verdicts

1. **Classification theorem [Proof sketch].** A graph function of a tower curve built **without
   `arc_of_length`** has only finitely many finite singular points. At each one the local expansion is
   one of:
   - analytic;
   - Puiseux: `c ζ^{p/q} + …`, `p/q ∈ ℚ \ ℤ_{≥0}`;
   - a pole: `c ζ^{-n} + …`;
   - a log branch: `c log ζ + analytic`, with `c ∈ ℂ \ {0}` **constant**.
   In particular there are **no** finite `1/log`, no `ζ log ζ` (`δ log δ`), and no finite essential
   singularities.

2. **`tan x = λx` is Route-I excluded under B.** For fixed `k`,
   ```
   h(u) = sinh u / (gd u + kπ)
   ```
   has a `1/log` singularity at every `u₀ = iπ(m + ½)`: `gd u ~ −i log ζ`, so
   `h ~ Sinh(u₀)/(−i log ζ) = −1/log ζ`. Infinitely many such points; not in the class. Hence no
   single-intersection/box construction with B-affine data solves the `tan` family. **R8 row 6 is
   closed on Route I.**
   [Proof + Wolfram]

3. **The `l = 0` spherical well is Route-I excluded under B.** R8 §3.2 reduces the target's singular
   part at `u₀` to `coth u · gd u`; since `coth u ~ ζ` and `gd u ~ −i log ζ`, it is
   ```
   −i ζ log ζ + … ,
   ```
   a `δ log δ` singularity. Infinitely many such points (the zeros of `coth`), not in the class.
   **R8 row 15 is closed on Route I.** [Proof + Wolfram]

4. **What remains is Route O, not Route I.** `tan`'s catenary route (`d = λ`, `X = λkπ`) is
   B1-sufficient; its necessity is the open B1 span condition of R12 §3.3. `l = 0` has no Route-O
   curve. The beams (8/9) are unchanged: continuous interpolation log-excluded, discrete spectrum C
   open.

5. **The other rows are unchanged.** Involute, rhumb, tractrix, Biot are log-excluded (R3/R8); the
   elastica is excluded by non-elementarity. R9 only adds the two non-log types.

6. **The classification is a B-theorem.** Under A, `1/log` and `δlogδ` are resolvable by real
   P-constructible `φ` (`exp(a/z)`, `z/W(z)`; R12 §1.4), so R9's exclusions are B-only. The log rows
   are A-robust (R12 Lemma 1.2). This is the expected scope split.

---

## 1. The classification theorem

### 1.1 Statement

Let `𝔗` be R3's tower class: algebraic, exp-type `(αt + A₁(e^{λt}), βt + A₂(e^{λt}))`, trig-type
`(αt + A₁(sin t, cos t), βt + A₂(sin t, cos t))`, closed under affine maps, `restrict` and `offset`
(R3 §1). A **graph function** `g_C` is a branch of the abscissa as a function of the ordinate; the
other axis is the same class by an affine swap (R3 Def. 2.2).

> **Theorem 9.1 [Proof sketch].** Let `C ∈ 𝔗` be built without `arc_of_length`. On any branch, `g_C`
> has finitely many finite singular points, and at each one the local expansion is one of (analytic),
> (Puiseux), (pole), or `c log ζ + analytic` with constant `c ≠ 0`.

### 1.2 Proof

The normal form is R3 §1.1. Write the tracing as `(X, Y)` in the inherited parameter, and let `z` be
the exponential/trig variable. The graph function is `g(u) = X(z(u))`, where `z(u)` solves `Y(z) = u`.

**(A) Algebraic.** `g` is a branch of an algebraic function: Puiseux/pole, no log. [Proof]

**(E) Exp tower.** `X(z) = (α/λ) log z + A₁(z)`, `Y(z) = (β/λ) log z + A₂(z)`, `z = e^{λt}`.

- **`β ≠ 0`.** As `z → 0` or `∞`, `Y → ∓∞`, so every finite `u` has `z(u)` finite and nonzero. The
  inverse `z(u)` is analytic except at the critical values `Y'(z) = 0` (finitely many, since `Y'` is
  algebraic) and at the algebraic branch points of `A₂`; there it is Puiseux. At such a point
  `X(z(u))` is Puiseux (or analytic), with no log. **No finite log, no `1/log`, no `δlogδ`.**
- **`β = 0`.** `Y = A₂(z)` is algebraic, so `z(u)` is algebraic (Puiseux/pole). Then
  ```
  g(u) = (α/λ) log z(u) + A₁(z(u)) .
  ```
  If `z(u) = c ζ^{p/q} + …` (including `p/q < 0` for a pole), then
  ```
  log z(u) = (p/q) log ζ + log c + analytic ,
  ```
  a log branch with **constant** coefficient `(α/λ)(p/q)`. The algebraic term `A₁(z(u))` is
  Puiseux/pole. If `z(u)` is analytic and nonzero, `g` is analytic. **No `1/log`, no `ζ log ζ`.**

  The two excluded types are excluded for the same structural reason: the log enters as a
  **summand** `log z`, with a constant coefficient, not as an inverse (`1/log`) and not multiplied by
  the vanishing algebraic factor (`ζ log ζ`). An affine map multiplies the whole coordinate by a
  constant, so it rescales the coefficient but does not change the structure; `offset` only changes
  `A₁, A₂` algebraically (R3 §1.4); `restrict` restricts the domain. None creates a product or an
  inverse of the log.

**(T) Trig tower.** `Y = βt + A₂(sin t, cos t)`. If `β ≠ 0`, `t(u)` is analytic (`A₂` bounded), so
`g` is analytic. If `β = 0`, `u` is bounded; the branch lives on a bounded interval and `g` is
analytic/algebraic. No log. [Proof, R3 Lemma 3.3]

**Base and closure.** Algebraic base curves are case (A); `exp_two` and `sine` are (E)/(T) with the
stated `A_i`; affine/`restrict`/`offset` preserve the class by R3 §1.3–1.4. ∎

### 1.3 Why `arc_of_length` is excluded

`arc_of_length` integrates a tower speed; its graph function can acquire new log points (R3 §4.2).
That is depth 3 once a readout is added, so it is outside Route I's single-intersection class. R9's theorem is
therefore exactly the class R3/R12 use for Route I. A depth-3 construction is not covered — and is
not meant to be: that is where the positive offset-inversion mechanism lives.

### 1.4 The Route-I reduction

> **Theorem 9.2 (Route-I exclusion by singularity type) [Proof].** Let `F` have infinitely many
> finite singular points of type `1/log` or `δlogδ`. Then no construction whose only active step is
> one `inter_x`/`inter_y` or one `box`, with B-affine data, solves `F`.

**Proof.** By R12 §3.1 (Route I under B), such an output is `D = φ ∘ F` with `φ` affine, and `D` is
a difference of two graph functions of tower curves built without `arc_of_length` (R3 Lemma 2.3).
Affine `φ` preserves the local type (R12 Lemma 3.1). By Theorem 9.1, `D` has only finitely many finite
singular points, of the allowed types; it cannot have infinitely many `1/log` or `δlogδ` points.
Contradiction. ∎

**Remark (composition).** The depth-2 composition case (intersection then intersection, R3 Theorem
4.2 case 2) is the same nested bookkeeping as R3 §4.3. The outer graph function is covered by Theorem
9.1, so the conclusion should extend; the full composition is not written out here. The two named
applications below are single-intersection reductions, so the remark does not affect them.

The theorem is type-specific: it does not need the log count, and it does not need the target to be
analytic-identity-like on an interval. This is what R8 §3.1 asked for.

---

## 2. Application: `tan x = λx`

### 2.1 The local form

Fix the branch `k` and write the target as a function of `u` (R8 §3.1):
```
λ = h(u) = sinh u / (gd u + kπ) .
```
At `u₀ = iπ(m + ½)`, `gd` has a log branch point with monodromy `2π` (R3 Lemma 3.2), so
`gd u = −i log ζ + O(1)` with `ζ = u − u₀`. Therefore
```
h(u) = Sinh(u₀) / (−i log ζ + O(1)) = −1/log ζ + o(1/log ζ) ,        (2.1)
```
using `Sinh(iπ/2) = i` and `i/(−i) = −1`. This is a **`1/log` branch point**, not a log branch
point. [Proof + Wolfram, §6 cell 1]

There are infinitely many such points, one for each `m ∈ ℤ`. Hence `h` has infinitely many finite
`1/log` singularities.

### 2.2 The exclusion

> **Corollary 2.1 [Proof].** Under B, no single intersection with B-affine data solves
> `tan x = λx` for a fixed branch `k` and all `λ`. Route I is excluded.

**Proof.** Theorem 9.2 with `F = h`. ∎

This is the result R8 §3.1 flagged as the concrete next step. It does **not** settle Route O: the
catenary construction `d = λ`, `X = λkπ` is B1-legal, and its necessity is the open B1 span
condition of R12 §3.3. The status is now:
```
Route O:  catenary sufficient (B1); necessity open (R12 §3.3)
Route I:  excluded (B) by 1/log singularity type
```
So `tan` is an **offset-route-only** row in the strong sense: the missing curve is needed for the
known Route-O construction, and Route I is now proved impossible (under B), not merely unexplored.

### 2.3 What changed from R8

R8 §3.1 said: "the log test is silent; `1/log` is not a log branch point." That is correct, and R9
supplies the missing invariant. R8's verdict "open on both routes" becomes "Route I excluded,
Route O open" under B. The `1/log` invariant is exactly the one R8 asked for.

---

## 3. Application: the `l = 0` spherical well

### 3.1 The local form

R8 §3.2 records that the `l = 0` target has `gd` multiplied by `coth u`, and that `coth` has a zero
at the same `u₀ = iπ/2` where `gd` has its branch point. Explicitly, near `u₀`:
```
coth u = ζ + O(ζ³) ,        gd u = −i log ζ + O(1) ,
coth u · gd u = −i ζ log ζ + … .                                      (3.1)
```
[Wolfram, §6 cell 2: `Series[Coth[iπ/2 + z], {z,0,2}] = z + …`.] So the singular part is
`δ log δ`, not a log branch point; the monodromy is not additive, and R3's log count is silent.

### 3.2 The exclusion

> **Corollary 3.1 [Proof].** Under B, no single intersection with B-affine data solves the `l = 0`
> well. Route I is excluded.

**Proof.** The target has infinitely many `δlogδ` points (one at each zero of `coth`, i.e. each
`u₀ = iπ(m + ½)`). Theorem 9.2 applies. ∎

The `l = 0` row now has:
```
Route O:  no curve identified
Route I:  excluded (B) by δlogδ singularity type
```
This is stronger than R8's "open on both routes", and it is the second of the two non-log types.

---

## 4. The revised R8 table

Only the two open rows change; the rest are as in R8 §2.

| # | problem | Route O | Route I (B) | verdict |
|---|---|---|---|---|
| 6 | `tan x = λx` | catenary, `d = λ`; necessity **open** (B1) | **excluded**: `1/log` | **offset-route-only** (I excluded) |
| 7 | gear involute | catenary, `d = 1`; B0 | excluded: log | intersection-impossible |
| 8/9 | beams | log-cosine; B0 for interpolation | interpolation excluded; **discrete open** (C) | mixed |
| 10 | rhumb | log-cosine, `d = k`; B0 | excluded: log | intersection-impossible |
| 13 | tractrix | tractrix; B0 | excluded: log | intersection-impossible (B) |
| 14 | elastica | elastica; B0 | excluded: non-elementarity | intersection-impossible (B) |
| 15 | `l = 0` well | no curve | **excluded**: `δlogδ` | **I-excluded, O-none** |
| 16 | Biot | not (OI) | excluded: log | intersection-impossible (B) |
| 12 | goat | formal, legality open | n/a (single) | S-legality |
| 19 | `tan x = x` quartic | — | Route-I with other missing curves | I with missing curves |

The strong rows are now 6, 7, 10, 13, 14, 15, 16; 8/9 remain mixed; 12 and 19 are unchanged.

---

## 5. Caveats and scope

1. **B only.** Under A, `1/log` and `δlogδ` are resolvable: `exp(a/z)` maps `1/log ζ` to `ζ`, and
   `z/W(z)` maps `δ log δ` to `δ` (R12 §1.4). So Corollaries 2.1 and 3.1 are B-theorems. Of the log
   rows, 7 and 10 (and the beam interpolation) are A-robust because their monodromy is real (R12
   Lemma 1.2); 13 (tractrix) and 16 (Biot) are B-only because their monodromy is complex. The
   `1/log`/`δlogδ` rows are B-only.
2. **Depth ≤ 2 / no `arc_of_length`.** Theorem 9.1 is for the class Route I uses. A depth-3
   construction can add log points; R9 does not claim anything about it, and should not — that is the
   positive offset-inversion mechanism.
3. **The target's local form.** (2.1) and (3.1) are the only target-specific inputs. They are
   expansions at the branch points, verified symbolically/numerically; the rest is the general
   classification.
4. **Route O is untouched.** `tan`'s B1 necessity and the `l=0` curve question are separate. R9
   closes Route I, not the offset route.
5. **No Lean.** The classification is complex analysis; the note is prose. The algebraic part (normal
   form closure) is R3 §1, already noted as the formalizable fragment.

---

## 6. Wolfram cells

| cell | check | result |
|---|---|---|
| 1 | `Sinh[iπ/2] / (−i)` | `−1` (the `1/log` coefficient in (2.1)) |
| 1 | `Sin[2 ArcTan[E^u] − π/2] − Tanh[u]` | `0` (the `gd` identity used in R3/R12) |
| 2 | `Series[Coth[iπ/2 + z], {z,0,2}]` | `z + O(z³)` (a simple zero; `coth·gd ~ ζ log ζ`) |
| 2 | `Series[Tanh[iπ/2 + z], {z,0,1}]` | `1/z + z/3 + …` (the pole of `tanh` at the same point; R12) |
| 3 | `Series[Sin[−i log z], {z,0,1}]` | `i/(2z) − i z/2 + …` (the `sin`-resolution turns a log into a pole; R12) |

The branch-point coefficients are the standard residues of `sech`; R3 §3.2 and §6 cell 2 verify the
monodromy `∓2π`. No new numerical identity is needed for the classification itself; the cells check
the two target expansions.

---

## 7. Open items

1. **`tan` Route-O necessity (B1).** The span condition of R12 §3.3. The catenary is the solution;
   the log-cosine and the base catalogue are excluded; the rest of the tower is open.
2. **`l = 0` Route O.** No curve identified. The `δlogδ` exclusion is Route I only.
3. **The classification beyond `arc_of_length`.** Does a depth-3 graph function ever acquire a
   `1/log` or `δlogδ` point? Not needed for Route I; interesting for the positive programme.
4. **A-closure / non-log global question.** Under A, the two corollaries fail; a global argument
   (growth/counting on `φ ∘ F`) would be needed. Parked as an open thread (R12 §1.6).
5. **Formalisation.** The `1/log`/`δlogδ` classification is beyond the current Lean library; the
   useful formalizable fragment remains R3's algebraic normal-form closure.
