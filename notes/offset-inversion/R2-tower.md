# R2 — the offset/affine tower

**Stream:** R2 of `PLAN-offset-inversion.md`. **Deliverable:** this file. No `.lean` file was
edited and no `lake` command was run.

Sources read: `PLAN-offset-inversion.md` §0/§1/§R2/§L1/§L2;
`notes/offset-inversion-tangent-angle.md`; `R0-foundations.md` (speed identity, cusp verdict,
C² warning); `R5-named.md` (the named-problem rows are **not** repeated here);
`R1-whewell-base.md` (a skeleton at the time of reading — its table is all `TBD`, so no
elliptic row from R1 is available to import); `W0.md`; `atlas.wl`; `Pptc/Jacobi.lean`
(Outlook, lines 640–671).

Labels: **[Proof]**, **[Wolfram]**, **[Heuristic]**, **[Open]**. Every number below was
produced by **Wolfram Language** in this stream, in four single evaluator cells, at 38–45
digit working precision; residuals are quoted as `0. 10^-k`. `atlas.wl` was not `Get[]`-ed
(the sandbox has no `C:` mount, §0 of `W0.md`); instead the same conventions were written
inline — `n = (−y',x')/s`, `κ = (x'y''−y'x'')/s³`, speed `√(x'²+y'²)` — and the parabola
self-test identity `d/dw[(w√(1+w²)+asinh w)/2 − d arctan w] = √(1+w²) − d/(1+w²)` was
re-established symbolically as check `A1''` (residual exactly `0`) before any tower number
was used.

---

## 0. Verdicts

1. **The second term is an elliptic integral of the second kind, always.** For a general
   affine map with linear part `L = R(θ₂)·diag(σ₁,σ₂)·R(θ₁)`, the weighted angle integral is

   `∫ W(ψ) dψ = σ₁ [ E(ψ+θ₁ | k) − E(θ₁ | k) ],   k² = 1 − σ₂²/σ₁²`.

   `W` is constant exactly when `L` is a scalar multiple of an orthogonal matrix
   (similarity/reflection, i.e. a conformal map), and is `σ₁|cos(ψ+θ₁)|` (elementary, rank 1)
   when `σ₂ = 0`. Otherwise the term is **non-elementary, genus 1, second kind** — the
   `√Q_n/Q_k^{3/2}` of `Jacobi.lean`'s Outlook, now identified. **[Proof + Wolfram]**

2. **The plan's "two bare angle functions with independent coefficients" does not occur.**
   The tower can put **at most one bare `arctan`** in an equation. Offsets never change the
   tangent angle; only affine steps do, and they act on `tan ψ` by the projective action of
   `L`. A bare `dψ_i` survives only if every *later* affine is conformal, and a conformal
   affine sends `ψ ↦ ±ψ + α`. Hence all bare angle terms in one equation are affine
   translates of one another and merge into a single coefficient. **[Proof]**

3. **What does occur** is a strictly more interesting mixture: one bare `arctan` of a Möbius
   image, **plus** one or more *weighted* angle integrals. So the tower's genuinely new
   equation class is

   `∫W ds₀ − d₁·σ₁E(φ|k) − d₂·arctan(Möbius(tan ψ)) = x`,

   elliptic **plus** elementary-transcendental, with independent coefficients. Best candidate
   and numbers in §Q2.4. **[Proof + Wolfram]**

4. **Q3 is settled for the base catalogue and `[Open]` for the full tower.** "Same function"
   (`S ≡ cosh u`, `S ≡ const`) reduces by congruence to the catenary and the log-cosine
   **[Proof]**; whether those are in the tower is **[Open]**, and — important for R3 —
   R3's normal form *cannot* decide it, because `cosh` is already of the exp normal form.
   "Same roots uniformly" reduces to a **parallelism** condition **[Proof]**: matching the
   beam spectrum for all `x` forces `ρ = A + sec ψ`, i.e. a *parallel curve of the
   log-cosine*, and matching `tan x = λx` for all branches forces `ρ = A + B sec²ψ`, i.e. a
   *parallel curve of the catenary*. No base curve of `Defs.lean` satisfies either
   **[Wolfram]**. The full tower is **[Open]**.

5. **Genus bookkeeping (§Q4).** One weight: genus 1, second kind. `m` distinct non-conformal
   weights behind one offset: genus `m`. The `dψ` term is genus 0 and never adds elliptic
   content. Third kind enters only from the *base* curve's own `R` (incomplete Beta for
   general power laws), never from an affine step.

---

## Q1. Affine after offset

### Q1.0 The reduction

Let `γ` be a regular `C²` curve with speed `s = |γ'|`, unit tangent `T = γ'/s`, tangent angle
`ψ`, and curvature `κ` (counterclockwise positive, `ψ' = κs`). Write `P_d = γ + d·n` with
`n = (−y',x')/s` the left normal, as in `Defs.lean`. By R0 (2.1), `P_d' = (1−dκ)γ'`.

Let `A` be an affine map with linear part `L`. Then

```
(A∘P_d)' = L P_d' = (1 − dκ)·Lγ' ,
speed(A∘P_d)  = |1 − dκ|·|Lγ'| = |1 − dκ|·|L T|·s .
```

On a cusp-free window (`1 − dκ > 0`),

```
arcLength(A∘P_d; a,b)
  = ∫_a^b |Lγ'| dt − d ∫_a^b κ|Lγ'| dt
  = ∫ |Lγ'| dt − d ∫ |L T(ψ)| dψ .                                          (1.1)
```

The step from the second to the third expression uses `κ dt = dψ/s` and `|Lγ'| = |LT|·s`.
Equation (1.1) is the plan's `∫|Aγ'| − d∫(|Aγ'|/|γ'|)dψ`, and it identifies the second term:

> **`∫ W(ψ) dψ` with `W(ψ) := |L T(ψ)|`.** It is a *weighted angle integral*: the angle
> `dψ` weighted by how much the affine map stretches the unit tangent at that angle.

**[Proof]** (the algebra above, with R0's speed identity).

### Q1.1 `W` for a general affine map

Write `L = {{a,b},{c,e}}` and `w = tan ψ`, so `T = (1,w)/√(1+w²)`. Then

```
|LT|² = ((a + b w)² + (c + e w)²)/(1 + w²) = Q(w)/(1+w²),
Q(w)  := (a + b w)² + (c + e w)²   (positive definite unless L is singular),
```

and since `dψ = dw/(1+w²)`,

```
W(ψ) dψ = √Q(w) / (1+w²)^{3/2} dw .                                        (1.2)
```

This is *exactly* the shape `√Q_n / Q_k^{3/2}` that `Pptc/Jacobi.lean` (Outlook, lines
648–651) predicts for "offsets interleaved with scalings". **[Proof + Wolfram: check `1`, `2`,
`3` — `|LT|² − Q/(1+w²)` and the SVD identity both simplify to `0`. Check `2` needs
`Sec[ψ]² = 1+w²`; the two forms are identical.]

Now diagonalise. Every real `2×2` matrix is `L = R(θ₂)·diag(σ₁,σ₂)·R(θ₁)` with `σ₁ ≥ |σ₂| ≥ 0`
(the singular value decomposition; the `Defs` vocabulary `rotate · scale_x · scale_y ·
rotate` generates exactly this). Then `R(θ₁)T = (cos(ψ+θ₁), sin(ψ+θ₁))`, so

```
W(ψ) = √( σ₁² cos²(ψ+θ₁) + σ₂² sin²(ψ+θ₁) )
     = σ₁ √(1 − k² sin²φ),      φ := ψ + θ₁,   k² := 1 − σ₂²/σ₁² .          (1.3)
```

**[Proof + Wolfram: check `3`, `4` both exactly `0`; check `5` gives `|R T|² = 1` — a
rotation alone is conformal and changes nothing.]**

Hence

```
∫_{ψ₀}^{ψ₁} W dψ = σ₁ [ E(ψ₁+θ₁ | k) − E(ψ₀+θ₁ | k) ] ,                    (1.4)
```

the **incomplete elliptic integral of the second kind** (parameter `m = k²`).

> **Answer to "give `W` for a general `A`".** Up to the harmless conformal parts
> (rotation/translation/overall scale), `W(ψ) = √(σ₁²cos²φ + σ₂²sin²φ)` with `φ` the angle
> measured from the axis of the *larger* singular value, and the second term of (1.1) is
> `σ₁·E(φ|k)`. The tower therefore produces `E` for **every** non-conformal affine image of
> **every** curve — in particular for curves (parabola, Neile, `poly_graph`) whose own `R`
> is elementary.

### Q1.2 Elementary / known / new

| case of `L` | `W(ψ)` | `∫W dψ` | status |
|---|---|---|---|
| `L = σ·O(2)` (similarity or reflection, `σ₁=σ₂`) | `σ` | `σψ` | **elementary**; `k = 0`, `E(φ|0) = φ` |
| `σ₂ = 0` (rank 1) | `σ₁|cos φ|` | `σ₁|sin φ|·sgn` | **elementary**; `k = 1` |
| general `0 < σ₂ < σ₁` | `σ₁√(1−k²sin²φ)` | `σ₁E(φ|k)` | **classical non-elementary** (second-kind elliptic) |
| general, combined with a *second* modulus, or with a bare `arctan` | sum | `σ₁E(φ|k₁) + cE(·|k₂) + d·arctan` | **genuinely new**: no single classical function |

Three grades, therefore:

* **Elementary** iff `σ₁ = σ₂` (conformal) or `σ₂ = 0` (degenerate). Nothing else.
* **A combination of known functions** in the general case: `E` is a classical special
  function, so (1.4) is "closed form" in the classical sense. `E` is *already* in the tower
  for the ellipse (R1 row 5), so on its own it is not new content — it is a **new modulus for
  old content**.
* **Genuinely new** when two *different* moduli appear in one equation (ellipse case, §Q1.4),
  or when `E` appears next to a bare `arctan` (§Q2). Neither is reducible to
  `R̃(φ) − dφ = x` with a single `R̃`.

[Wolfram: `Integrate[√(1−k²Sin[x]²),x] = EllipticE[x,k²]` and
`Integrate[√(Cos[x]²+c²Sin[x]²),x] = EllipticE[x,1−c²]` (checks `D1`, `D2`): Mathematica
returns the elliptic form and nothing simpler, i.e. no elementary antiderivative is found.
This is the classical non-elementarity of `E`; I do **not** claim a proof of it here.]

### Q1.3 Worked example (a): a parabola offset, scaled non-conformally

Take `γ(w) = (w, w²/2)` (`poly_graph`, `Defs`), `d` with `d<1` (no cusp: `κ ≤ 1`), and
`L = diag(1,c)` — `scale_y` by `c`. This is the plan's example (a).

Term 1 (the affine image's own arc length — R1's catalogue):

```
∫_0^W |Lγ'| dw = ∫_0^W √(1+c²w²) dw = (W√(1+c²W²) + asinh(cW)/c)/2 =: ℓ_c(W).
```

Term 2, from (1.3) with `σ₁=1, σ₂=c, θ₁=0`:

```
∫_0^{arctan W} |LT(ψ)| dψ = ∫_0^{arctan W} √(cos²ψ + c² sin²ψ) dψ = E(arctan W | 1−c²) =: E_c(W).
```

So

```
L_{(1,c)}(W) = ℓ_c(W) − d·E_c(W) ,                                        (1.5)
```

and its derivative is `√(1+c²W²)·(1 − d/(1+W²)^{3/2})`, exactly the speed of `A(P_d)`
**[Wolfram: check `A1''` = `0`; the speed-squared identity `A1` = `0` as well.]**

Numerical confirmation against `NIntegrate` of the true speed of
`A(P_d)(w) = (w − dw/√(1+w²), c(w²/2 + d/√(1+w²)))`, at 40–45 digits:

| `c` | `d` | `W` | numeric | `ℓ_c(W) − dE_c(W)` | residual |
|---|---|---|---|---|---|
| 2 | 1/3 | 3/2 | 2.39453138930870667934394331816 | same | `0. 10^-44` |
| 2 | 1/3 | 2 | 4.14036365862534624200600749474 | same | `0. 10^-44` |
| 2 | 9/10 | 3/2 | 1.66049098924519598594948563036 | same | `0. 10^-44` |
| 2 | 9/10 | 2 | 3.27944948215244386866577377106 | same | `0. 10^-44` |
| 1/2 | 1/3 | 3/2 | 1.33905766010116757957045323468 | same | `0. 10^-45` |
| 1/2 | 1/3 | 2 | 1.97652930901384788087235324048 | same | `0. 10^-44` |
| 1/2 | 9/10 | 3/2 | 0.843355475321245438830929127146 | same | `0. 10^-44` |
| 1/2 | 9/10 | 2 | 1.43413098036990455249704706567 | same | `0. 10^-45` |

**Verdict for (a): elementary `+` elliptic.** The parabola's affine arc length is elementary
(its affine image is again a parabola), but the *offset* term is `E(arctan W|1−c²)` with
`0 < 1−c² < 1` for `0<|c|<1` (and negative parameter for `|c|>1`). So scaling a parabola
offset non-conformally produces a genuinely elliptic arc length — the first such case in the
tower, and it needs no elliptic base curve at all. **[Wolfram]**

**Degeneracy checks.** At `c = 1` the modulus is `0` and `E(arctan W|0) = arctan W`
**[Wolfram, check `10b` = `0`]**, recovering the source note's parabola formula exactly. At
`d = 0`, only `ℓ_c` survives: the scaled parabola's own arc length. And with `d₁ = 0` the
word `O A O` reduces to `ℓ_c(W) − d₂arctan(cW)`, which is the plain offset equation of the
parabola `y = cx²/2` **[Wolfram, check `D6'` = `0`]** — as it must be, since "affine then
offset" is R1's catalogue and the parabola family is closed under scaling.

### Q1.4 Worked example (b): an ellipse offset, scaled non-conformally

Take the ellipse `γ(t) = (A₀cos t, B₀sin t)`, offset by `d₁` (with `d₁ < B₀²/A₀ = 1/κ_max`, so
the window is cusp-free), then `L = diag(σ₁,σ₂)`. This is the plan's example (b); a pure
**rotation** would be conformal and do nothing (check `5`), so the informative version of
"rotate an ellipse offset" is "rotate, then stretch", i.e. `L = R(α)diag(σ₁,σ₂)`, whose `W`
is (1.3) with `θ₁ = α`. I display `θ₁ = 0`, i.e. the stretch along the ellipse's own axes; a
nonzero `θ₁` is the same computation after pre-rotating the ellipse, and it changes no
structure (only the two angles at which the moduli are read off).

Term 1: the image is the ellipse `(σ₁A₀, σ₂B₀)`, so

```
∫_0^T |Lγ'| dt = σ₁A₀ [ E(T+π/2 | m₁) − E(π/2 | m₁) ],   m₁ = 1 − (σ₂B₀/(σ₁A₀))² .
```

Term 2: `W = σ₁√(1−k²sin²ψ)` with `ψ` the **original** ellipse tangent angle
(`tan ψ = −(B₀/A₀)cot t`) and `k² = m₂ = 1 − σ₂²/σ₁²`:

```
∫ W dψ = σ₁ [ E(ψ(T)|m₂) − E(ψ(0)|m₂) ] .
```

So

```
L(W) = σ₁A₀[E(T+π/2|m₁) − E(π/2|m₁)] − d₁σ₁[E(ψ(T)|m₂) − E(ψ(0)|m₂)] .        (1.6)
```

Two things are worth recording.

* **Two different moduli in one equation.** `m₁ = 1 − (σ₂B₀/(σ₁A₀))²` and
  `m₂ = 1 − (σ₂/σ₁)²`; their difference is `(A₀²−B₀²)σ₂²/(A₀²σ₁²)` **[Wolfram, check `B4`]**,
  which is **nonzero exactly when the ellipse is not a circle**. For an ellipse, term 1 is
  already `E`; scaling adds a *second* `E` with a different modulus in a different variable.
  This sum is not a single elliptic integral.
* **Two different angle functions.** Term 1 lives in the parameter `t`, term 2 in the angle
  `ψ = ψ_orig(t)`, and `ψ` is *not* the tangent angle of the scaled curve (that is
  `ψ_A = arctan(Möbius(tanψ))`). So even "affine after offset" already mixes two angle
  variables — the phenomenon Q2 asks about, in its first form.

Numerical confirmation, at 40–45 digits:

| `(A₀,B₀,σ₁,σ₂,d₁)` | `t` | numeric | (1.6) | residual |
|---|---|---|---|---|
| (2,1,1,3,1/3) | 3/10 | 0.363216242089404737741209858508 | same | `0. 10^-45` |
| (2,1,1,3,1/3) | 7/10 | 1.12710486951095712971794558191 | same | `0. 10^-44` |
| (2,1,1,3,1/3) | 11/10 | 1.96035582199721261370249958283 | same | `0. 10^-44` |
| (5/2,1,1,1/2,1/5) | 4/5 | 0.706961706433794967234899170949 | same | `0. 10^-45` |
| (5/2,1,1,1/2,1/5) | 6/5 | 1.50805236529413291177178832413 | same | `0. 10^-44` |

with moduli `(m₁,m₂) = (−1.25,−8)` and `(0.96,0.75)` respectively **[Wolfram, checks
`B2''`, `S3`, `S5`, `B8`/`S6`]**.

**Verdict for (b): two-modulus elliptic; not elementary, not a single known function.**
Whether the sum `E(t|m₁) − dσ₁E(ψ(t)|m₂)` is ever elementary is **[Open]**; no route is
visible, and the two moduli are functionally independent.

**A cusp caution that actually fired.** A first attempt used `d₁ = 7/10` with `A₀ = 5/2`,
`B₀ = 1`; the window contained an offset cusp (`1 − d₁κ = 0` at `κ = 1/d₁ = 10/7 < κ_max =
2.5`), the numeric integral then used `|1−d₁κ|` while the formula used the signed `1−d₁κ`, and
the residual was a *constant* `0.1551274…` — exactly R0 §3.4's phenomenon, not an error in
the formula. With `d₁ = 1/5 < 2/5` the residuals vanish. **[Wolfram + R0]** This is a
practical warning for R4: any tower word must be checked for `1 − dκ > 0` on the whole window
*before* a closed form is used.

### Q1.5 Verdict

The second term is the incomplete elliptic integral of the second kind with modulus fixed by
the **condition number** `σ₁/σ₂` of the linear part, and its angle measured from the axis of
the larger singular value, offset by the initial rotation angle. It is elementary only for
conformal or rank-1 linear parts. Consequently **every** non-conformal affine image of **any**
offset carries an `E`; when the base is already elliptic (the ellipse), the tower carries two
`E`s of different moduli, and that is a new object. **[Proof + Wolfram]**

---

## Q2. Offset again: which angle functions can meet

### Q2.0 The differential of a tower word

Let a tower word be a finite sequence of steps, each `O(d_i)` (offset by `d_i`) or `A_j`
(affine with linear part `L_j`), applied left to right to a base `γ₀`. Write `γ_i`, `ψ_i`,
`s_i` for the curve, tangent angle and arc length after step `i`, and `W_j(ψ) = |L_j T(ψ)|`.

* **Offset:** `ψ_{i+1} = ψ_i` (the tangent direction is unchanged), `ds_{i+1} = ds_i − d_i dψ_i`.
* **Affine:** `ψ_{i+1} = ∠(L_j T(ψ_i))`, `ds_{i+1} = W_j(ψ_i) ds_i`.

Iterating,

```
ds_final = (Π_j W_j) ds₀ − Σ_i d_i (Π_{j>i} W_j) dψ_i .                    (2.1)
```

That is the whole structure: **offsets contribute `−d_i` times an angle differential, and
affines contribute a multiplicative algebraic weight.** Since `dψ_i` and `dψ_{i'}` differ only
by the Möbius images of the affines between them, (2.1) is the master formula. **[Proof]**

The net equation for a laid arc of length `x` from a base point is therefore

```
∫ (Π W_j) ds₀ − Σ_i d_i ∫ (Π_{j>i} W_j) dψ_i  =  x .                       (2.2)
```

### Q2.1 Composition rule for the angle functions

The action on the *slope* `w = tan ψ` of a linear part `L` is the projective action

```
w  ↦  σ(L)(w) := (L₂₁ + L₂₂ w)/(L₁₁ + L₁₂ w) ,
```

a Möbius map. Two facts:

* **Composition is matrix multiplication**: `σ(L₂L₁) = σ(L₂) ∘ σ(L₁)`. **[Proof + Wolfram:
  check `D1` = `0` identically.]**
* In SVD coordinates, `tan ψ_A = tan(θ₂ + arctan((σ₂/σ₁)·tan(ψ+θ₁)))`, i.e. a scale of the
  slope sandwiched between two rotations. **[Proof + Wolfram: check `D2'` = `0`.]**

So the *set of angle functions the tower can produce* is

```
{ ψ ↦ arctan(M·tan ψ)  :  M ∈ the semigroup generated by the linear parts L_j }
```

with the composition law being matrix multiplication in `GL(2,ℝ)/{±1}`. Because the semigroup
is closed under products and the generators are the `L_j`, **a word with `n` affine steps
produces at most the `n+1` angle functions `ψ, σ(L₁)·ψ, σ(L₂L₁)·ψ, …, σ(L_n⋯L₁)·ψ`** — exactly
the partial products (writing `σ(L)·ψ` for `arctan(σ(L)(tanψ))`). **[Proof]**

### Q2.2 Which words collapse

Write `ρ = 1/κ` for the radius of curvature, so `R'(ψ) = ρ(ψ)` and `W`-terms are
`σ₁E(φ|k)` with `k² = 1 − σ₂²/σ₁²`.

| word | equation from (2.2) | collapses? |
|---|---|---|
| `O(d)` | `R(ψ) − dψ = x` | the base family (source note) |
| `A` then `O(d)` | `R_A(ψ_A) − dψ_A = x` | R1's affine-image catalogue; no tower content |
| `O(d₁) O(d₂)` | `R − (d₁+d₂)ψ = x` | **yes**, exactly: parallel curves compose |
| `O(d₁) A O(d₂)`, `A = σ·O(2)` | `σR(ψ) − (σd₁+d₂)ψ = x + c` | **yes**: it is the *same* family as `σ`-times the base offset by `d₁ + d₂/σ`; `α` cancels |
| `O(d₁) A O(d₂)`, `A` non-conformal | `ℓ_A(ψ_A) − d₁σ₁E(φ|k) − d₂ψ_A = x` | **no** |
| `O A O A O` | `ℓ − d₁∫W₁W₂ dψ₀ − d₂∫W₂ dψ₁ − d₃ψ₂`, with `ψ₁ = σ(L₁)ψ₀`, `ψ₂ = σ(L₂L₁)ψ₀` | **no**, richer |
| anything with two adjacent `O`s | the two `d`s add | **always** |

Two exact collapse mechanisms:

1. **Adjacent offsets add.** `P_{d₂}(P_{d₁}(γ)) = P_{d₁+d₂}(γ)` on the cusp-free side. Both
   offsets have the same unit normal, so `γ + d₁n + d₂n = γ + (d₁+d₂)n`. **[Proof; Wolfram:
   check `D3'`, residuals `0. 10^-4030` on the parabola at `d₁=1/3, d₂=1/5`, `t ∈ {1/2,2}`.]**
   The caveat is sharp: at `d₁ = 3, d₂ = −1` the identity fails (residual `−0.894…`) because
   `1 − d₁κ` changes sign, the normal flips, and the second offset is measured from the
   *other* side. This is R0's cusp verdict again.
2. **A conformal affine between two offsets collapses them into the base family.** If
   `L = σ·(orthogonal)` then `W ≡ σ` and `ψ_A = ±ψ + α`, so the arc length is
   `σ(R(ψ) − d₁ψ) − d₂(ψ+α)`, which differs from `σR(ψ) − (σd₁+d₂)ψ` only by the constant
   `−d₂(ψ(a)+α)`. One bare angle function, the base `R` rescaled — no new function is created.
   In particular the rotation angle `α` **cancels from the equation**; it only shifts `x`.

### Q2.3 The exact list of angle-function combinations

**The key structural theorem.**

> **`[Proof]` At most one *bare* angle function appears in any tower equation.**
> A term `−d_i dψ_i` is bare iff every affine after step `i` is conformal (otherwise it
> carries a non-constant weight `Π_{j>i}W_j`). Conformal affines act on `ψ` by `ψ ↦ ±ψ + α`.
> So all bare terms in one equation are `c_k·d(±ψ + α_k) = ±c_k dψ`, which merge into a single
> coefficient of `dψ`. ∎

This **corrects the plan's expectation**. The plan says (§R2 Q2) that "one equation can carry
two different angle functions, `arctan(slope)` and `arctan(Möbius(slope))`". That is true only
in the weighted sense: the first one arrives with a non-constant weight. The complete list is:

| # of offsets | angle content | coefficients independent? |
|---|---|---|
| 1 | one bare `ψ`, or one bare `σ(ψ)` if an affine follows | — |
| 2, adjacent | one bare `ψ` (they merge) | no |
| 2, separated by a **conformal** affine | one bare `ψ` | no |
| 2, separated by a **non-conformal** affine | `σ₁E(ψ+θ₁|k)` **and** `arctan(σ(L)tan ψ)` | **yes** |
| `m` offsets, `m−1` non-conformal affines between them | `σ₁E(φ₁|k₁)`, …, each with its own modulus, **plus one** bare `arctan` | **yes** |

So: **exactly one bare `arctan`; arbitrarily many weighted elliptic terms; independence of the
coefficients holds only in the mixed case.** **[Proof]**

### Q2.4 The best candidate, tested

The simplest word with independent coefficients and two genuinely different functions is

```
γ = parabola  →  O(d₁)  →  A = scale_y(c)  →  O(d₂)
```

which by (2.1)–(2.2) gives

```
Φ(W) := ℓ_c(W) − d₁·E(arctan W | 1−c²) − d₂·arctan(cW) = x ,                (2.3)
```

with `ℓ_c(W) = (W√(1+c²W²) + asinh(cW)/c)/2`, `W = tan ψ` the base slope, `cW = tan ψ_A` the
scaled slope, and `cusp-free` conditions `|d₁| < 1` and `|d₂|·c < 1`.

> **Candidate N1.** `(2.3)` with `d₁, d₂ ≠ 0` and `c ≠ 1`: an equation mixing an **elementary**
> term, a **second-kind elliptic** `E`, and a **bare arctan of the Möbius image**, with two
> independent coefficients. **[Proof + Wolfram]**

Verification against `NIntegrate` of the true speed of
`A(P_{d₁}γ)(w) + d₂ n_{A(P_{d₁}γ)}(w)`, 38–40 digits:

| `(c,d₁,d₂)` | `W` | numeric | (2.3) | residual |
|---|---|---|---|---|
| (2, 1/3, 1/5) | 1/2 | 0.247562150380610559706956694186 | same | `0. 10^-40` |
| (2, 1/3, 1/5) | 3/2 | 2.14472223482905579417795990270 | same | `0. 10^-39` |
| (2, 1/3, 1/5) | 5/2 | 6.11897168410090098634473756599 | same | `0. 10^-39` |
| (3, 1/4, 1/10) | 1 | 1.461491146903760573263239266 | same | `0. 10^-37` |
| (3, 1/4, 1/10) | 2 | 5.859009748769023433415544989 | same | `0. 10^-37` |
| (3, 1/4, 1/10) | 3 | 13.32163621194870196508876071 | same | `0. 10^-36` |

**A sample root [Wolfram]:** `c = 2, d₁ = 1/3, d₂ = 1/5, x = 3/2` gives
`W = 1.260488562859158444273357516623311622991`, residual `0. 10^-39` (`FindRoot`,
40 digits). The map `Φ` is strictly increasing here (`Φ' = (1−d₁/s³)(1 − d₂c/(1+c²W²)^{3/2})
√(1+c²W²) > 0`), so the root is unique on `W > 0`.

**Why this is not reducible to one angle function.** The two ingredient functions
`F₁(W) = E(arctan W|1−c²)` and `F₂(W) = arctan(cW)` are functionally independent: their
Wronskian is nonzero,

```
F₁'F₂ − F₁F₂' |_{(W,c)=(3/2,2)}  = 0.415071909109831868330578906245 ,
F₁'F₂ − F₁F₂' |_{(W,c)=(1,1/2)}  = −0.108016852666221740799256730772 ,
```

and it vanishes identically at `c = 1` **[Wolfram, checks `D6`, `D7`]** — exactly as it must,
since `c=1` is the conformal collapse. A nonzero Wronskian rules out *any* functional relation
`G(F₁,F₂) = 0` on a neighbourhood, hence rules out writing (2.3) as `R̃(ψ_A) − dψ_A = x`.
**[Proof from the Wronskian, value from Wolfram]**

**Second best.** The ellipse version (`O A O` on the ellipse) is strictly richer: two
elliptic terms with **different moduli** plus the bare arctan. Its equation is (1.6) minus
`d₂ arctan(σ(L)tan ψ)`. No numerical verification is quoted separately because (1.6) and the
parabola case already pin down the two mechanisms; the ellipse adds a second modulus, not a
new mechanism. **[Proof; the moduli are (1.6) plus §Q1.4]**

---

## Q3. The reachable `(A, angle-combination)` family

### Q3.1 `S(u)` in the tower

In the `u` coordinate of the source note (`tan ψ = sinh u`, so `ψ = gd u`,
`du/dψ = cosh u`),

```
S(u) = ds/du = (ds/dψ)(dψ/du) = ρ(ψ)·cos ψ ,     ρ = 1/κ = R'(ψ) .          (3.1)
```

**[Proof: chain rule.]** So `S` and `R` carry the same information — as they must, since the
Whewell function determines the curve. Table (all verified symbolically **[Wolfram]**):

| curve | `ρ(ψ)` | `S(u)` | check |
|---|---|---|---|
| circle, radius `a` | `a` | `a sech u` | `S1` = 0 |
| parabola `y=x²/2` | `sec³ψ` | `cosh²u` | `S2` = 0 |
| Neile `y=x^{3/2}` | `(8/9)sec³ψ tanψ` | `(8/9)cosh²u sinh u` | `N0`,`N2` |
| `exp` (`y=eˣ`) | `sec³ψ/tanψ` | `cosh²u/sinh u` | `S4` = 0 |
| catenary | `sec²ψ` | `cosh u` | `S5` = 0 |
| log-cosine `y=ln sec x` | `secψ` | `1` | `S6` = 0 |

(N.B. `defs`-drawable are the first three; the catenary, log-cosine and `exp` in the `u`
column are for comparison with R5 and for §Q3.3.)

### Q3.2 Same function

> **`[Proof]`** `S ≡ 1` on a window ⟺ `ρ = secψ` ⟺ `R = gd⁻¹ψ + c` ⟺ the curve is the
> log-cosine. `S ≡ cosh u` ⟺ `ρ = sec²ψ` ⟺ `R = tanψ + c` ⟺ the curve is a catenary.

Proof: `S ≡ 1` gives `ρ = 1/cosψ`, so `ds = dψ/cosψ`, so `s = gd⁻¹ψ + c`; the Whewell
function determines the curve up to congruence. Symmetrically for `ρ = sec²ψ`, `s = tanψ + c`.
∎

So the first two bullets of §R2 Q3 are **equivalent to** "the tower contains a catenary /
log-cosine". That is **`[Open]`**, and it must be flagged loudly:

> **Warning for R3.** R3's tower normal form (`(αt + A₁(e^{λt}), βt + A₂(e^{λt}))` for the
> exp tower) **does not exclude the catenary**: `(t, cosh t) = (t, (eᵗ+e^{−t})/2)` is of that
> form on the nose. The normal form is a necessary condition on *coordinates*, and `cosh` is
> an exponential combination, so the catenary passes it. A sharper invariant is needed — for
> instance one in the **Whewell** coordinate (`ρ`, or the arc-length differential), not the
> coordinate one. R2 hands R3 these two facts to aim at:
> `ρ_cat = sec²ψ` and `ρ_logcos = secψ`, both with **poles at `ψ = π/2`**.

The nearest miss in the tower is instructive. The `exp` curve has `ρ = sec³ψ/tanψ`, and

```
ρ_exp − ρ_cat = (1+w²)^{3/2}/w − (1+w²)  →  1/2   as w = tanψ → ∞
```

**[Wolfram, check `X1`]**, so the exponential curve is **asymptotically a catenary shifted by
`1/2` in the radius of curvature** but is not one; correspondingly
`S_exp − cosh u = 0.483039…` at `u=1` and `0.140385…` at `u=2` **[Wolfram, check `X4`]**, never
zero. That is the closest the drawable catalogue comes to `S = cosh u`.

### Q3.3 Same family of roots

The congruence argument excludes a single *curve*. What it does **not** exclude is an equation
which is a different function with the same roots. That is the question, and the answer is
clean:

> **`[Proof]` (rigidity) Fix a curve `C` (so `R`) and let the offset distance `d` be fixed. The
> equation `R(ψ) − dψ = x` has the same solution for every `x` in an interval iff
> `R₁ − d₁ψ = R₂ − d₂ψ + c`, iff `ρ₁ − ρ₂ ≡ d₁ − d₂`, iff the two curves are **parallel**
> (one is an offset of the other).**

Proof: same solution for all `x` in an interval means the inverses of `Φ_i = R_i − d_iψ`
agree, hence `Φ₁ = Φ₂ + c`. ∎

Consequences, applying this to the two named families (without duplicating R5's rows):

* **Beam equation** (`cos x cosh x = −1`, i.e. `x + gd x = (2m+1)π`) has `Φ_beam(x) = x + gd x`.
  Identifying the two real variables (`x` of the beam with `ψ` of the tower — the only way
  "same roots as numbers" can be meant), matching **for all `x`** forces
  `R(ψ) − dψ = ψ + gd⁻¹ψ + c`, i.e.
  **`R = Aψ + gd⁻¹ψ + c`, `ρ = A + secψ`** with `A = 1 + d`.
  But `ρ = (1+d) + secψ` is exactly the radius of curvature of a **parallel curve of the
  log-cosine** (offset the log-cosine by `−(1+d)`). So: *matching the beam spectrum for all
  `x` forces the curve to be a parallel curve of the log-cosine.*
* **`tan x = λx`** (in the `(u, gd u)` form `sinh u − λ gd u = λkπ`, and `ψ = gd u`, so the
  tower's `ψ` *is* the target's `x`) forces
  `R(ψ) − dψ = sinh u − λ gd u + c = tanψ − λψ + c`, i.e.
  **`R = a tanψ + Aψ + c`, `ρ = a sec²ψ + A`** — a **parallel curve of the catenary**.

Now test the base catalogue. For each base curve of `Defs`, solve `ρ(w) = A + √(1+w²)` (the
beam family) and `ρ(w) = A + B(1+w²)` (the `tan` family) for constant `A`, `B`:

| curve | `ρ(w)` | `A(w) = ρ − √(1+w²)` | constant? |
|---|---|---|---|
| parabola `y=x²/2` | `(1+w²)^{3/2}` | `w²√(1+w²)` | no |
| Neile `y=x^{3/2}` | `(8/9)w(1+w²)^{3/2}` | `√(1+w²)·((8/9)w(1+w²) − 1)` | no |
| `exp` | `(1+w²)^{3/2}/w` | `√(1+w²)(1−w+w²)/w` | no |
| catenary | `1+w²` | `1+w²−√(1+w²)` | no |
| log-cosine | `√(1+w²)` | `0` | **yes (A=0)** |
| circle | `a` | `a−√(1+w²)` | no |

with `dA/dw ≠ 0` in every row except the log-cosine **[Wolfram, checks `F1`, `F2`, `N0`,
`R1`, `R2`]**. For the `tan` family the leading coefficient `B = lim ρ/(1+w²)` is
`∞, ∞, 1, 1, 0, 0` for parabola, Neile, `exp`, catenary, log-cosine, circle respectively, and
in the two cases where `B = 1` (`exp`, catenary) the remainder is **not** constant: `exp`'s
remainder tends to `1/2` but is not identically `1/2`, and the catenary is *itself* the missing
curve (it is not a `Defs` constructor). So `exp` is the only *drawable* near-miss and it fails.
**[Wolfram, check `F3`, `X1`]**

> **Verdict on the third bullet, for the base catalogue: settled `[Proof + Wolfram]`.** No
> base curve of `Defs.lean` is a parallel curve of the log-cosine or of the catenary, so no
> base curve reproduces the beam spectrum or `tan x = λx` uniformly in the variable. The only
> way to get either is the missing curve itself. This is a **sharper** statement than R5's
> "one missing curve each": the missing curves are exactly the *parallel classes* of the
> log-cosine and the catenary, and offsets of them are free.

### Q3.4 Same roots for P-constructible data

> **R12 update.** The case `d` allowed to depend affinely on the family parameter (B1) is now a
> **4-function span condition** on the Whewell function `R_C`; see
> `notes/reachability/R12-convention.md` §3.3. For `tan x = λx` the catenary is the solution
> `(a,b,c,e) = (1,0,kπ,0)`, the log-cosine is not, and the base catalogue is excluded by Wronskians.
> The rest of the tower is open. This is a functional equation, not a constructibility question.

This is where the argument must stop, and the reason is worth stating precisely.

Under the uniform convention, `d` and `x` may be P-constructible data not depending on the
root. For a *single* root `t*`, one equation in one unknown `d` almost always has a
P-constructible solution (continuity), so *non-uniform* coincidences carry no information —
consistent with the plan's "report numerical near-misses only as evidence". The content is in
the **uniform** case, and the uniform case splits:

* **Fixed `d`, all `x`:** rigidity above gives parallelism — settled.
* **`d` allowed to depend on the family parameter (`λ`, or the mode index `k`):** not settled.
  Formally one needs a tower curve `C`, a P-constructible function `d(λ)`, and a P-constructible
  `x(λ)` with `R_C(ψ_λ) − d(λ)ψ_λ = x(λ)` where `ψ_λ` is the target root. Solving for
  `d(λ)` gives `d(λ) = (R_C(ψ_λ) − x(λ))/ψ_λ`, which is P-constructible **only if**
  `R_C(ψ_λ)` is computable without knowing `ψ_λ`. The whole content of R5's rows 6–10 is that
  for the *right* curve this happens; for a wrong curve it does not, but "does not" is a
  constructibility statement, not an algebraic identity, and no argument here proves it.

> **`[Open]`, handed to R3/R4.** Precisely: *for a fixed tower curve `C` and a fixed `d`, no
> single-arc offset construction has the beam spectrum or the `tan x = λx` spectrum as its
> solution set* — **proved** (§Q3.3, via rigidity + the `ρ` table). *For `d` varying with the
> family parameter* — **open**; what is needed is a statement that
> `(R_C(ψ_λ) − x(λ))/ψ_λ` is not a P-constructible function of `λ`, which is a
> transcendence/independence statement about `R_C` composed with the target's inverse.

Two numerical facts for R3/R4 to use as evidence, not results:

* the `exp` curve is the unique base curve whose `ρ` has the catenary's leading behaviour
  (`ρ ~ w²`, coefficient 1) and whose `R` has the `tan`-family's leading behaviour (`R ~ w`,
  coefficient 1), differing only at the next order (`ρ_exp − ρ_cat → 1/2`; `R_exp = tanψ −
  arctanh(cosψ)` with `d/dψ[−arctanh cosψ] = cscψ ≠ 0`) **[Wolfram, `X1`–`X3`]**;
* so if any drawable curve is to reach either family *asymptotically*, it is `exp`, and the
  obstruction is exactly the `cscψ` / `1/2` correction.

### Q3.5 Verdict

* `S ≡ cosh u` and `S ≡ const`: **equivalent by congruence to the catenary and log-cosine
  [Proof]**; the tower exclusion is **`[Open]`**, and R3's coordinate normal form cannot
  supply it (the catenary satisfies it).
* Same roots *as a family*, fixed data: **settled [Proof]**, reduces to parallelism to the
  missing curve; no `Defs` base curve qualifies **[Wolfram]**.
* Same roots for P-constructible data with `d` varying: **`[Open]`**.

---

## Q4. Genus and kind

Conventions: "genus" is the genus of the algebraic curve carrying the differential; "kind" is
the classical first/second/third kind classification. `ψ` terms are genus 0 and are *never*
the source of elliptic content — they are elementary, but they make the equation
transcendental (not solvable by elliptic inversion). **[Proof]**

| # | curve / step | integral | genus | kind | elementary? |
|---|---|---|---|---|---|
| 1 | circle | `aψ` | 0 | — | yes |
| 2 | parabola `R` | `(w√(1+w²)+asinh w)/2` | 0 | — | yes |
| 3 | parabola offset `R − dψ` | `R − d arctan w` | 0 | — | yes (source note) |
| 4 | Neile `R` | `sec³ψ/3` | 0 | — | yes |
| 5 | `poly_graph` of degree `n ≤ 6` | `∫√(1+p'(t)²)dt` | `⌊(2n−3)/2⌋` (`n=2`:0, `n=3`:1, `n=6`:4) | 2 | no for `n ≥ 3` |
| 6 | power law `y=ax^p` | binomial differential; incomplete `Beta` off Chebyshev's set | 0 (Beta), resp. `⌊(2p−3)/2⌋` when `2p−2 ∈ ℤ` | 2 (+3 for Beta) | only for Chebyshev `p` |
| 7 | power law, `p = 1+1/n` or `1+1/(2k−1)` | elementary | 0 | — | yes |
| 8 | ellipse | `aE(t|m)` | 1 | 2 | no |
| 9 | cubic Bézier | `∫√(quartic)dt` (`|γ'|²` is quartic) | 1 | 2 (+3 from poles) | no |
| 10 | `exp` `y=eˣ` | `√(1+w²) − arctanh(1/√(1+w²))` | 0 | — (log-free!) | yes |
| 11 | sheared sine, `|γ'|²` quadratic in `cos t` | elliptic, quartic | 1 | 2 | no |
| 12 | **one non-conformal weight** `∫W dψ` | `σ₁E(ψ+θ₁|k)` | **1** | **2** | **no** |
| 13 | weight, conformal `L` | `σψ` | 0 | — | yes |
| 14 | weight, rank 1 `L` | `σ₁|sin φ|` | 0 | — | yes |
| 15 | **two distinct weights** (product) | `√(Π(1−k_j²sin²ψ))`, quartic | **2** | 2 | no |
| 16 | `m` distinct weights | `√(degree 2m+2)` | **m** | 2 | no |
| 17 | ellipse + one weight (**two moduli**) | `E(t|m₁) + σ₁E(ψ|m₂)` | ≥1, **not a single elliptic curve** | 2+2 | no |
| 18 | any of the above + `dψ` | shift by `dψ` | unchanged | unchanged | the shift itself is |
| 19 | elastica (R5 row 14) | `F(ψ/2|m) − dψ` | 1 | 2 (+ elementary ψ) | no |
| 20 | log-cosine (missing) | `gd⁻¹ψ − dψ` | 0 | 3 (log of algebraic) | not elementary |

Justifications:

* Rows 12/13/14: §Q1.2; `W` is `σ₁√(1−k²sin²φ)`, `σ` or `σ₁|cosφ|`. The elliptic curve is
  `y² = (1−s²)(1−k²s²)` with `s = sinψ`, a quartic, genus 1; `E` is manifestly second kind
  (no residues — its only poles are the two points at infinity, of order 1 with zero residue).
  **[Proof]**
* Row 15/16: `m` weights give the hyperelliptic curve `y² = (1−s²)Π_{j=1}^m(1−k_j²s²)`, of
  degree `2m+2`; for `m ≥ 1` with distinct moduli this is non-singular, so genus `m` by
  Riemann–Hurwitz. `m = 1` reproduces genus 1. **[Proof]**
* Row 17: the two moduli `m₁ ≠ m₂` differ by `(A₀²−B₀²)σ₂²/(A₀²σ₁²)` **[Wolfram, `B4`]**, so
  the integrand involves `√(1−m₁s²)` and `√(1−m₂s²)` in one expression; the two are not
  related by a Möbius change of variable (different `j`-invariants unless the moduli
  coincide). I state the genus as "≥ 1 and not a single elliptic curve" rather than a number;
  the exact genus of the fibre product is **[Open]** and irrelevant to R4, which only needs to
  know that it is *not* reducible to one elliptic integral.
* Row 20: `gd⁻¹ψ = ln(secψ+tanψ)` has a logarithmic singularity at `ψ = π/2`, so the
  differential is third kind; the curve is the log-cosine, genus 0 (it is not algebraic —
  the log is the obstruction).

**R1 note.** `R1-whewell-base.md` was a `TBD` skeleton when read, so rows 5–11 above are my
own recomputations from the shape of the speed, not taken from R1's filled table; they are
listed here only so R4 knows what it is combining. R4 should re-check each against the
finished R1 and replace any that R1 states differently. The three that matter for the tower
are rows 12, 15 and 17 — those are this note's own results.

---

## 5. Summary

### (i) The exact list of angle-function combinations the tower can produce

Offsets never change the tangent angle; affines apply the projective action of their linear
part, and the composition law is **matrix multiplication** (§Q2.1). Therefore:

1. **One bare `arctan` at most**, always of the form `arctan(M·tan ψ)` with `M` a partial
   product of the linear parts (§Q2.3, `[Proof]`).
2. **Any number of weighted angle integrals**, each of the form `σ₁E(φ_j|k_j)` with
   `k_j² = 1 − (σ₂/σ₁)²` for the affine that follows the `j`-th offset (§Q1), each with an
   independent modulus and coefficient.
3. **Collapses:** (a) adjacent offsets add; (b) offsets separated only by conformal affines
   merge into one bare angle term, and a *similarity* between two offsets makes the whole word
   equal to a similarity of the base offset by `d₁ + d₂/σ`; (c) the rotation angle of a
   P-constructible rotation cancels from the equation and only shifts `x`.
4. **No collapse** exactly when a non-conformal affine sits between two offsets; then the
   earlier offset's angle arrives through an elliptic weight while the later one arrives bare.

### (ii) Best candidate for a new equation family

> **N1:** `(2.3)`, the word `parabola → O(d₁) → scale_y(c) → O(d₂)`:
> `ℓ_c(W) − d₁·E(arctan W|1−c²) − d₂·arctan(cW) = x`.

* **Status:** verified to 36–40 digits against the true offset speed at two parameter sets;
  root computed to 40 digits; the two ingredient functions have nonzero Wronskian, so the
  equation is not reducible to `R̃(φ) − dφ = x`. **[Proof + Wolfram]**
* **Second best:** the ellipse version, which upgrades one of the two terms to a *second*
  modulus (§Q1.4).
* Neither is a named classical equation; they are new *forms*, and R4 is the stream that
  should look for named problems of the shape "elliptic + arctan".

### (iii) `[Open]` items handed to R3/R4

1. **R3 — the tower exclusion of the catenary and log-cosine.** R3's coordinate normal form
   *fails* here (the catenary is `(t, cosh t)`, of the exp form). R3 needs an invariant in the
   Whewell/arc-length-differential coordinate. R2 supplies the targets: `ρ_cat = sec²ψ`,
   `ρ_logcos = secψ`, and the near-miss `ρ_exp − ρ_cat → 1/2`.
2. **R3 — the `d`-varying uniformity.** Prove that
   `(R_C(ψ_λ) − x(λ))/ψ_λ` is not P-constructible in the family parameter for a tower `C`.
   The fixed-`d` case is settled by parallelism (§Q3.3).
3. **R4 — genus of the two-modulus sum.** Row 17 of §Q4 is "not one elliptic curve"; the
   exact genus of the fibre product is open and may matter if R4 wants to combine terms.
4. **R4 — cusp bookkeeping in tower words.** §Q1.4 records a case where a *constant* residual
   appeared purely from crossing an offset cusp. Every tower word needs the window check
   `1 − d_iκ_i > 0` at each stage, not just at the first.
5. **R4 — is `E(φ|k)` at a P-constructible `φ` and P-constructible `k` P-constructible?**
   `Pptc/Jacobi.lean` proves the *second-kind amplitude* is (`ellipticEAm_Pconstructible`),
   so the answer is presumably yes on the elliptic arc; R2 does not need it, but any claim that
   N1 "solves" an equation for P-constructible data will.

---

## 6. Reproducibility: what each check label establishes

Four evaluator cells; each label is the tag printed in that cell. Every residual is
`numeric − closed form`.

| label | statement checked | result |
|---|---|---|
| `1` | `|LT|² = Q(w)/(1+w²)` for `L={{a,b},{c,e}}`, `Q=(a+bw)²+(c+ew)²` | `0` |
| `2` | `|LT| = √Q/√(1+w²)` (identical after `Sec²=1+w²`) | `0` |
| `3`, `4` | SVD: `|LT|² = σ₁²cos²(ψ+θ₁)+σ₂²sin²(ψ+θ₁) = σ₁²(1−k²sin²φ)` | `0` |
| `5` | rotation alone is conformal: `|RT|² = 1` | `0` |
| `6` | `∫W dψ` vs `σ₁(E(ψ+θ|k)−E(θ|k))`, `(σ₁,σ₂,θ,P)=(2,1/2,3/10,13/10)` | `1.5676307…` vs same, resid `0. 10^-44` |
| `A1`, `A1''` | `d/dW[ℓ_c−dE_c] = (1−d/(1+W²)^{3/2})√(1+c²W²)` | `0` |
| `A2` | parabola-scale table of §Q1.3 (8 rows) | resid `0. 10^-44±1` |
| `B1`, `B2''`, `S1`–`S5` | ellipse-scale closed form (1.6), two parameter sets | resid `0. 10^-44` |
| `B4`, `B8`, `S6` | the two moduli and `m₁−m₂ = (A₀²−B₀²)σ₂²/(A₀²σ₁²)` | `(−1.25,−8)`, `(0.96,0.75)` |
| `C1` | the same, with `d₁=1/5 < 2/5` (cusp-free) | resid `0. 10^-44` |
| `D1` | slope-map composition `σ(L₂L₁)=σ(L₂)∘σ(L₁)` | `0` |
| `D2'` | `tanψ_A = tan(θ₂ + arctan((σ₂/σ₁)tan(ψ+θ₁)))` | `0` |
| `D3'` | `P_{d₂}∘P_{d₁} = P_{d₁+d₂}` on the parabola, `d₁=1/3,d₂=1/5` | `0. 10^-4030` |
| `D3''` | the same at `d₁=3,d₂=−1` (cusp crossed) | fails, `−0.894…` |
| `D4'`, `D5'`, `N1` | word `O A O` closed form (2.3), three parameter sets | resid `0. 10^-36…-40` |
| `D6`, `D7` | Wronskian of `E(arctan W|1−c²)` and `arctan(cW)`; zero at `c=1` | `0.415…`, `−0.108…`, `0` |
| `D8` | root of (2.3) at `x=3/2`, `(c,d₁,d₂)=(2,1/3,1/5)` | `W=1.2604885628…`, resid `0. 10^-39` |
| `S1`–`S6` | `S(u) = ρcosψ` table of §Q3.1 | all `0` |
| `N0`,`N2` | `ρ_Neile = (8/9)w(1+w²)^{3/2}`, `S_Neile = (8/9)cosh²u sinh u` | `ρ` as stated; `S` = `8√(4+w²…)/9` |
| `F1`,`F2`,`R1`,`R2` | `ρ − √(1+w²)` is non-constant for every base curve except the log-cosine | see §Q3.3 table |
| `F3` | `lim ρ/(1+w²)` = `∞,∞,1,0,0` (parabola, Neile, exp, logcos, circle) | as stated |
| `X1` | `ρ_exp − ρ_cat → 1/2` | `1/2` |
| `X2`,`X3` | `R_exp = tanψ − arctanh(cosψ)`, `d/dψ[−arctanh cosψ] = cscψ` | `cscψ` |
| `X4` | `S_exp − cosh u` at `u=1,2` | `0.483039`, `0.140385` |
| `Y1`–`Y4` | series at `ψ=π/2−ε` | §Q3.3 |
| `D1`,`D2` (cell 2) | `∫√(1−k²sin²x)dx = EllipticE[x,k²]`, `∫√(cos²+c²sin²)dx = EllipticE[x,1−c²]` | as stated |
| `E1`,`E2` | `∫√(1+w²)/w dw = √(1+w²) − arctanh(1/√(1+w²))` | `0` |
