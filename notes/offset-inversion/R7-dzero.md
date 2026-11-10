# R7: the `d = 0` case — separation fails

Stream **R7** of issue 18. Deliverable for open item 1 of `SUMMARY.md` §7 ("The `d = 0` separation
case"). Research only: no `.lean` edit, no `lake`, no commit.

Inputs read: `SUMMARY.md`, `PLAN-offset-inversion.md` §2 (R3), `R3-separation.md` §3.9(4) and §4,
`R2-tower.md` Q3, `R1-whewell-base.md` row 1, `Defs.lean` (`exp_two`, `linearMap` closure,
`inter_x`/`inter_y`, `translate_y`), `Basic.lean` (`linearMap_PConstructibleCurve`).

Labels: **[Proof]**, **[Wolfram]**, **[Heuristic]**, **[Open]**.
**Backend:** every number was produced by the Wolfram Language MCP (5 successful evaluator calls,
one further call timed out; 40–60 digit working precision). No Python.

---

## Findings summary

1. **Separation fails at `d = 0`, constructively [Proof].** The parabola's arc-length function
   decomposes *exactly* as a difference of two exponential graph functions:
   ```
   F₀(u) = ¼ sinh 2u + u/2 = (e^{2u}/8 + u/4) − (e^{−2u}/8 − u/4) .
   ```
   Both summands are graph functions of affine images of `exp_two` (one with exponential rate `+2`,
   one with rate `−2`). Intersecting the two curves, with the second translated vertically by `x`,
   has the unique abscissa `u = F₀⁻¹(x)`. This is a **single `inter_x`, depth 1**.

2. **The `d = 0` gap is therefore not a gap in the proof but a genuine failure of the statement
   [Proof].** R3 §3.9(4) asked the wrong question: it asked whether the *graph* of `F₀` is drawable.
   R3's reduction (Lemma 2.3) only needs `F₀` to be a *difference* of two graph functions, and it is.
   So the branch-point invariant's silence at `d = 0` is correct, not a weakness.

3. **The `gd` atom is the entire obstruction.** At `d ≠ 0`, `F_d = F₀ − d·gd u`, and
   `gd u = 2 arctan(e^u) − π/2` has infinitely many finite log branch points (`u = iπ(m+½)`). R3's
   Theorem 3.4 is the rigorous statement that no difference of tower graph functions has those. At
   `d = 0` the atom is absent and the decomposition exists.

4. **The graph of `F₀` is still not a drawable tower curve [Proof sketch, §3],** but that is now a
   side remark: graph reachability was only a *sufficient* condition for a single intersection to
   solve the family, and the necessary condition holds.

5. **Consequence for L2.** L2's `d = 0` instance remains correct, but it is not evidence of a new
   mechanism: at `d = 0` a single intersection already reaches the same root. The offset-inversion
   mechanism's novelty starts at `d ≠ 0`, exactly as the programme's "R" category predicts.

---

## 1. The `d = 0` family and what is at stake

At `d = 0` the whole-curve offset is the identity, and the mechanism
```
parabola → offset(d) → arc_of_length(x) → box
```
reduces to
```
parabola → arc_of_length(x) → box .
```
This is a legal depth-3 construction (R0 §5, L2), and its equation is the parabola's arc-length
inversion. With `w = tan ψ = sinh u` (R1 row 1, R3 (2.4.1)),

```
F₀(u) = ¼ sinh 2u + u/2 ,     F₀'(u) = cosh²u > 0 ,     F₀ : ℝ → ℝ  is a bijection.   (1.1)
```

So the family is `{ F₀(u) = x : x ≥ 0 }`, and its solution function is `U = F₀⁻¹`.

R3's separation statement is: no construction of output depth ≤ 2 (one intersection or one box)
solves `F` uniformly. For `d ≠ 0` this is Theorem 3.4/3.5, proved by counting finite log branch
points: the target `F_d` has infinitely many, a difference of tower graph functions only finitely
many. At `d = 0`, `F₀` is entire and has **no** log branch points, so the count separates nothing.

R3 §3.9(4) framed the remaining question as *constructor reachability of the graph*
`G = {(u, F₀(u))}`: if `G` were a drawable curve, a horizontal line would meet it in one point and
`box_xmax` would read `u` in one step. We show in §3 that `G` is indeed not drawable — but the
construction of §2 does not need `G`, and that is the point.

---

## 2. The exact decomposition and the one-intersection construction

### 2.1 The algebra

> **Proposition 2.1 [Proof].** Define
> ```
> g₁(u) = e^{2u}/8 + u/4 ,        g₂(u) = e^{−2u}/8 − u/4 .
> ```
> Then `g₁(u) − g₂(u) = F₀(u)` for all `u ∈ ℝ`.

**Proof.** Expand: `g₁ − g₂ = (e^{2u} − e^{−2u})/8 + u/2 = ¼ sinh 2u + u/2`. ∎

[Wolfram: `Simplify[g₁[u] - g₂[u] - F₀[u]] = 0`.]

### 2.2 Both graphs are affine images of `exp_two`

Let `E = {(t, 2^t)} = exp_two`. The linear maps
```
M₁ = (a,b,c,d) = ( ln2/2, 0,  ln2/8, 1/8) ,        M₂ = (−ln2/2, 0,  ln2/8, 1/8)
```
act by `(x,y) ↦ (a x + b y, c x + d y)`. On `E`:

```
M₁(t, 2^t) = ( (ln2/2)t , (ln2/8)t + 2^t/8 ) = ( u , e^{2u}/8 + u/4 ) = (u, g₁(u)) ,
M₂(t, 2^t) = (−(ln2/2)t , (ln2/8)t + 2^t/8 ) = ( u , e^{−2u}/8 − u/4 ) = (u, g₂(u)) ,
```
using `2^t = e^{(ln2)t}` and `u = ±(ln2/2)t`. Both matrices have P-constructible entries (`ln2`,
`1/8`), and `linearMap_PConstructibleCurve` (Basic.lean) accepts every such map, so
```
C₁ = {(u, g₁(u))} ,        C₂ = {(u, g₂(u))}
```
are drawable tower curves. [Proof + Wolfram: `2^{(2/ln2)u} − e^{2u} = 0` and the negative-rate
identity.]

Alternatively, write each as `exp_two → scale_x → scale_y → shear`; the shear is the
`linearMap_PConstructibleCurve` step with matrix `[[1,0],[±1/4,1]]`, which is what turns
`(u, e^{±2u}/8)` into `(u, gᵢ(u))`.

### 2.3 The intersection

> **Theorem 2.2 [Proof].** For P-constructible `x`, the two curves `C₁` and `C₂ + (0,x)` meet in
> exactly one point, and its abscissa is `u = F₀⁻¹(x)`. Hence the `d = 0` family is solved by a
> single `inter_x`, at output depth 1.

**Proof.** `C₁ ∩ (C₂ + (0,x))` consists of the points `(u, g₁(u))` with `g₁(u) = g₂(u) + x`, i.e.
`F₀(u) = x` by Prop. 2.1. By (1.1) `F₀` is a strictly increasing bijection `ℝ → ℝ`, so for each `x`
there is exactly one such `u`; the intersection hypothesis of `inter_x` holds. The construction is
`exp_two` (depth 0) → `linearMap` twice (depth unchanged) → `translate_y` by `x` (depth unchanged)
→ `inter_x` (depth 1). ∎

The sub-construction is legal in `Defs`:

```
C₁ = linearMap( ln2/2, 0,  ln2/8, 1/8) '' exp_two
C₂ = linearMap(−ln2/2, 0,  ln2/8, 1/8) '' exp_two
u  = inter_x C₁ (translate_y C₂ x)
```

`translate_y` by the P-constructible family parameter `x` is exactly the "vertical translation" form
of R3's Lemma 2.3 (its remark: a `y`-translation swaps abscissa and ordinate and keeps the same
class). So the construction is the explicit witness for R3's reduction at `d = 0`:
```
x = g₁(u) − g₂(u) = F₀(u) .
```

### 2.4 Numerical confirmation

[Wolfram, 50 digits] The `inter_x` root and the `d = 0` arc-length root are the same:

| `x` | `u` from the intersection | `u` from `F₀(u)=x` | difference |
|---|---|---|---|
| 1/4 | 0.2450365342402738871077 | 0.2450365342402738871077 | `0·10⁻⁵⁰` |
| 1   | 0.8034069886263153878893 | 0.8034069886263153878893 | `0·10⁻⁴⁹` |
| 2   | 1.210114812850278781445 | 1.210114812850278781445 | `0·10⁻⁴⁹` |
| 10  | 2.134675879125779641380 | 2.134675879125779641380 | `0·10⁻⁴⁹` |
| 100 | 3.333901667715958141237 | 3.333901667715958141237 | `0·10⁻⁴⁹` |

### 2.5 Verdict

> **Corollary 2.3 [Proof].** The `d = 0` family is **not separated**: a single intersection, with
> `x` entering as affine data, solves it for every `x`. R3's Theorem 3.4 is correctly stated for
> `d ≠ 0` only.

---

## 3. Why the graph of `F₀` is the wrong target

R3 §3.9(4) asked whether `G = {(u, F₀(u))}` is a drawable curve. It is not, but that is now
secondary.

> **Proposition 3.1 [Proof sketch].** `G` is not a drawable tower curve.

**Sketch.** R3's normal form says every drawable curve is algebraic, exp-type
`(αt + A₁(e^{λt}), βt + A₂(e^{λt}))`, or trig-type. `G` is neither algebraic nor trig-type (it is
transcendental and non-oscillatory). For the exp type, write `z = e^{λt}` and note the end invariant:
as `z → 0`, `A₁, A₂` are analytic at `0`, and the drift `(α, β)` is nonzero for a nondegenerate word
(an invertible affine step maps the initial drift `(1,0)` to a nonzero vector, and `offset` adds only
a bounded normal term because the speed tends to `√(α²+β²) > 0`). Hence every exp-tower word has
```
(x, y) = (αt + O(1), βt + O(1))     as t → −∞ ,     i.e. at most linear growth.
```
`G`, however, has `y = (z − 1/z)/8 + (log z)/4 ~ −1/(8z)` as `z → 0`, i.e. exponential growth at the
`u → −∞` end. So no exp-tower word matches `G`; a restriction to a sub-arc does not help, because the
identity with the entire `G` extends analytically through any finite endpoint (a Puiseux singularity
of the word would have to be a singularity of `G`, and `G` has none). ∎

*Numerical check of the invariant* [Wolfram]: for a length-3 word
`exp → offset(d₁) → affine → offset(d₂)` at `t = −20, −40`:
```
{x/t, y/t, y} = {2.0211…, 0.9410…, −18.8211…}  and  {2.0106…, 0.9705…, −38.8211…} ,
```
so `y` is linear in `t`; while `G_y = (z−1/z)/8 + (log z)/4 = −6.0646·10⁷` at `t = −20`. The two
cannot agree.

**Why this does not matter.** Reachability of `G` is a *sufficient* condition for a single
horizontal-line intersection to solve the family. R3's Lemma 2.3 gives the *necessary and sufficient*
form: the target must be a difference `g_{C₁}(u) − g_{C₂}(u)` of graph functions. Theorem 2.2
exhibits such a difference explicitly. So the right question was never "is `G` drawable?" but "is
`F₀` a graph-difference?", and the answer is yes.

---

## 4. The `gd` atom is the whole obstruction

At `d ≠ 0` the target is
```
F_d(u) = F₀(u) − d·gd u ,        gd u = 2 arctan(e^u) − π/2 .
```
`gd` is an **integral atom**: `d(gd u)/du = sech u = 2e^u/(1+e^{2u})`, algebraic in `e^u`, so `gd`
is an abelian integral on the exp tower — the "arc-length" side of R2's dictionary, not a graph
function of a curve built without `arc_of_length`. Concretely, `gd` has infinitely many finite log
branch points, at `e^u = ±i`, i.e. `u = iπ(m+½)`; each contributes an additive monodromy `2π` to
`gd`, hence a nonzero multiple of `2πd` to `F_d`. R3's Theorem 3.4 shows that a difference of tower
graph functions has only finitely many finite log branch points, so `F_d` is not a graph difference
for any `d ≠ 0`.

At `d = 0` the atom is multiplied by zero and the decomposition of Prop. 2.1 exists. This is the
sharpest statement of the programme's boundary:

> **The `d = 0` family is an intersection-class object; the offset-inversion family is a
> new mechanism only because of the `gd` term that `d ≠ 0` adds.**

The same picture explains why the two summands have rates `+2` and `−2`: `¼ sinh 2u` is the odd part
that must be split across an exponentially growing and an exponentially decaying graph function; an
intersection can do that, and the offset-inversion mechanism at `d ≠ 0` cannot be written that way.

---

## 5. Status and consequences

| question | status |
|---|---|
| Is the `d = 0` family solved by a single intersection? | **Yes**, Theorem 2.2 [Proof] |
| Is it separated at depth ≤ 2? | **No**, Cor. 2.3 [Proof] |
| Is the graph of `F₀` a drawable curve? | **No**, Prop. 3.1 [Proof sketch] — but irrelevant |
| Why does `d ≠ 0` separate? | the `gd` atom and its infinite log monodromy, R3 Thm 3.4 [Proof] |
| Is L2 at `d = 0` still correct? | **Yes**, but subsumed by the single intersection |
| Any remaining open item for `d = 0`? | **None** mathematically (no Lean formalization attempted) |

**Implications for the notes.**

- `R3-separation.md` §3.9(4) and §5.2 item 5 are updated: the `d = 0` case is **resolved as a
  failure of separation**, not left open. The correct statement is "separation for `d ≠ 0`; at
  `d = 0` the family is in the intersection class".
- `SUMMARY.md` §3 and §7 item 1 now say the same.
- L2's `d = 0` instance (`parabola_offset_root_Pconstructible` at `d = 0`) remains a true
  P-constructibility statement; it just does not witness a new mechanism there.
- The `d ≠ 0` separation theorem is unaffected.

---

## 6. Wolfram cells

| cell | contents | precision |
|---|---|---|
| 1 | `F₀`/`g₁`/`g₂` definitions, decomposition, derivative, affine identities, early limits | 40–60 digits |
| 2 | numerical intersection vs arc-length roots; monotonicity/limits | 40–50 digits |
| 3 | intersection table at `x = 1/4, 1, 2, 10, 100`; exp-end invariant numerics | 50 digits |
| 4 | decomposition and affine-image identities re-run; `F₀' = cosh²u` | 40 digits |
| 5 | (timed out) heavy symbolic `Limit` attempt; replaced by the numeric invariant check | — |

The dead branch in cell 5 is recorded because it is the point where the first framing (prove
separation via a graph invariant) was abandoned: the graph is not drawable, but a *difference* of
two drawable graphs is enough, and that difference is the construction of §2.
