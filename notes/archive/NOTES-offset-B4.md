# NOTES-offset-B4 — legality of offset extractions and the Lean infrastructure

Read `PLAN-offset-00-overview.md`, `PLAN-offset-B4-legality-formalization.md`, all of
`pptc/Pptc/Defs.lean`, all of `pptc/Pptc/Offset.lean`, `crossing_Pconstructible` and the
isolation helpers in `pptc/Pptc/Basic.lean` (l. 230–419), and `archived files/NOTES-jacobi-X4.md`.
Scratch file: `pptc/Pptc/Scratch/OffsetB4.lean` (imported by nothing; `lean-lsp` reports
`success: true`, only `sorry`/linter warnings). Script:
`archived files/offset-scripts/B4-01-parabola-offset-degree.py` (sympy, run with the workspace
Python 3.12; an independent Wolfram `Resultant` call gave the same answer). No `.lean` file other
than the scratch file was touched; no `lake build` was run.

## Summary (≤12 lines)

1. **Legality is almost never the bottleneck.** Every offset of an arc of a base curve is legal
   on some window; graph curves (`poly_graph`, `power_law`, `sine`, `exp_two`) are legal on *any*
   window because the abscissa is the parameter and `speed ≥ 1`.
2. The one real gap is **iterated offset**: `offset` requires only `hC1` of the tracing, but
   `offsetParam γ d` is `C¹` only when `γ` is `C²`. Offset-of-offset is legal for all standard
   (C^∞) parametrizations but is **not** syntactically closed. X4 missed this.
3. Chained offsets with an affine map are legal iff the affine map is invertible; `scale_x 0`
   breaks injectivity and regularity (X4 F1).
4. An `arc_of_length` output can be offset only if the supplied tracing is already regular and
   `C¹`; the constructor grants neither. On a sub-arc it is fine.
5. **Isolation-only crossing is strictly cheaper than `crossing_Pconstructible`** and is
   *proved*: `crossing_PConstructible_of_isolated` needs neither a parametrization, nor an
   implicit `F`, nor finiteness — only that the crossing is an isolated point of `S ∩ T`.
6. For **A2 and A4** the cheapest route is the polynomial/rationalization route already used in
   `Offset.lean`; for **A3** it is the isolation-only lemma plus analytic isolated-zeros.
7. The generic rationalization (norm) lemma is *proved* in under a page and needs no
   `Polynomial` API: every offset-cross equation folds to `E + w·O = 0`, `w² = S`, and then
   `E² − S·O² = 0`.
8. Recovery: `offsetParam_normal_eq_zero` already holds for every `γ`; rational curves only add
   denominator clearing. `rational_param_recovery` (proved) gives the two exact degree-`n`
   recovery equations, coefficients affine in the point; properness makes the root unique.
9. The parabola offset identity is *proved*: `offsetParam (t,t²) d t = parabolaOffsetRat d
   (2t + √(1+4t²))`, and Wolfram confirms the implicit equation has total degree **6** in `(X,Y)`
   (degree 6 in X, 4 in Y) — matches O5 `4n−2`.
10. Cusps are **produced** legally (the constructor allows non-injective/non-regular offsets) but
    generally cannot be **pinned**: no move reads a cusp parameter and `restrict` bounds must be
    constructible (X4 F4). Only a cusp that is itself an isolated crossing of constructible
    curves is reachable.
11. Three headline statement shapes are drafted and type-checked (H1 offset×conic, H2
    offset×offset isolated, H3 degree-10 family).
12. Recommended order: norm lemma → isolation crossing (both done) → parabola window bijection →
    rational recovery → conic engine → analytic finiteness → offset×offset.

---

## 1. Legality, mechanism by mechanism

The `offset` constructor (`Defs.lean:372–386`) asks for

* `hS : PConstructibleCurve S`;
* `hab : a ≤ b`, `hsub : γ '' Icc a b ⊆ S`, `hinj : Set.InjOn γ (Icc a b)`;
* `hdiff : ∀ t ∈ Icc a b, DifferentiableAt (fst ∘ γ) t ∧ DifferentiableAt (snd ∘ γ) t`;
* `hreg : ∀ t ∈ Icc a b, speed γ t ≠ 0`;
* `hC1 : ContinuousOn (deriv (fst ∘ γ)) (Icc a b) ∧ ContinuousOn (deriv (snd ∘ γ)) (Icc a b)`;
* `hd : PConstructible d`.

and returns `PConstructibleCurve (offsetParam γ d '' Icc a b)`. Two facts matter for every row:

* **No endpoint-constructibility hypothesis.** Unlike `arc_length` and `arc_of_length`,
  `offset` does *not* require `γ a` or `γ b` to be P-constructible. So one may offset an arc
  whose endpoints are unknown numbers (e.g. the output of `arc_of_length`), provided the tracing
  has the smoothness.
* `hinj`, `hreg`, `hC1` are asked of the **tracing**, not of the set `S`. A set may be legally
  offset whenever *some* window-tracing of it satisfies them.

### 1.1 Legality table

| # | mechanism | verdict | hypotheses to discharge (✓ = free) |
|---|---|---|---|
| L1 | offset of an **ellipse** arc, trig tracing `(cx+ (w/2)cos t, cy+ (h/2)sin t)` | **legal** on a window with `b−a < 2π` | `hsub` ✓, `hinj` ← `b−a<2π` (else `γ a=γ b`), `hdiff` ✓, `hreg` ← `w,h>0` (`sin,cos` never both 0), `hC1` ✓, `hd` given |
| L2 | offset of an **ellipse / hyperbola** arc, rational tracing `(cx+(w/2)(1−t²)/(1+t²), cy+(h/2)2t/(1+t²))` | **legal**, window avoiding the pole `t=∞` | `hsub` ✓, `hinj` ← injectivity of the rational circle, `hdiff` ✓ (rational), `hreg` ← speed `= C/(1+t²) ≠ 0`, `hC1` ✓. **Easier for Lean than L1** (no trig; `field_simp; ring`) |
| L3 | offset of a **polynomial graph** arc | **legal on any window** | `hinj` ← abscissa is the parameter, `hdiff` ✓ poly, `hreg` ← `speed = √(1+p'²) ≥ 1`, `hC1` ← `p'` polynomial |
| L4 | offset of a **power-law** arc `(t, a t^b)` | **legal on any window `[u,v]` with `0<u`** | `hsub` ← `t>0`, `hinj` ← abscissa, `hdiff`/`hC1` ← exp/log smooth off 0, `hreg` ← `√(1+(a b t^{b−1})²) ≥ 1` |
| L5 | offset of a **sine** arc | **legal on any window** | `hinj` ← abscissa, `hreg` ← `√(1+cos²) ≥ 1`, `hC1` ✓ |
| L6 | offset of a **`2^x`** arc | **legal on any window** | `hinj` ← abscissa, `hreg` ← `√(1+(2^t ln2)²) ≥ 1`, `hC1` ✓ |
| L7 | **offset of an offset** | **legal with sub-arc conditions**, and only for a `C²` base tracing | `hsub` ✓ (same window), `hinj` ← shorten to a window where the offset is injective, `hreg` ← avoid cusps, where `speed(offset)=|v|·|1−dκ|=0\), `hdiff` ✓ off cusps, **`hC1` ← `γ ∈ C²`, which the constructor does not provide** |
| L8 | **offset of an affine image of an offset** (chains, A4) | **legal iff the affine map is invertible** (+ L7's `C²`) | `hsub` ✓, `hinj`,`hreg` ← linear part invertible (`scale_x/scale_y` factors `≠ 0`; rotations/translations always), `hC1` ← L7. Fails if a scale factor is `0` (X4 F1) |
| L9 | **offset of an `arc_of_length` output** | **conditional**: legal only if the supplied tracing `γ₀` is regular and `C¹` on the window | `hsub` ✓, `hinj` ← inherited from `γ₀` on a sub-window, `hdiff` ← inherited, **`hreg`,`hC1` must be proved for `γ₀`; the constructor grants neither** |
| L10 | **restricted offset × restricted offset** (A3) | **legal with isolation** | each factor via L1–L6; crossing via `crossing_PConstructible_of_isolated` (needs β isolated) or `crossing_PConstructible` (needs `F`,`hfin`) |
| L11 | **two disjoint windows of the same offset** (self-crossing, A3) | **legal with isolation** | restrict to disjoint constructible windows; the crossing must be an isolated point of the two restricted arcs |
| L12 | **cusp** | produced legally; **pinned only in special configurations** | `offset` itself is fine (no injectivity/regularity of the output is required), but no move reads a cusp parameter, and `restrict` bounds must be P-constructible (X4 F4). Reachable only when the cusp is an isolated crossing of constructible curves with constructible isolating bounds |

### 1.2 Detail on the one substantive obstruction (L7)

`offsetParam γ d = γ + d·unitNormal γ` has derivative involving `unitNormal'`, which involves
`γ''` and `speed' = (γ'·γ'')/speed`. The constructor only supplies `hC1(γ)` (velocity
continuous), i.e. `γ ∈ C¹`. Hence:

* if `γ` is `C²` (true for every base parametrization chosen in L1–L6: polynomial, rational,
  trig, exp), then `offsetParam γ d` is `C¹` and offset-of-offset is immediate on a cusp-free,
  locally-injective sub-window;
* for an abstract `γ` known only to be `C¹`, the *set* `offsetParam γ d '' Icc` is still a `C¹`
  embedded arc wherever `1 − dκ ≠ 0` (its tangent direction is continuous and nonvanishing), so
  in principle an arc-length reparametrization gives a legal tracing — but this is an
  inverse-function-theorem argument, not something the constructor hands over.

Since every concrete construction in `Defs.lean` uses a smooth parametrization, L7 blocks no
*value*; it does mean `PConstructibleCurve` is not syntactically closed under `offset`, and any
formal chain theorem must carry `C²` of the chosen tracing as a hypothesis.

### 1.3 Cusps (L12)

For a cubic pair the cusp equation is `(x'y''−y'x'')² d² = (x'²+y'²)³`, degree 12 in `t`
(A3 plan). The cusp point is on the evolute, which is not a known constructible curve. The only
legal way to obtain a cusp's coordinates is to have a *second* constructible curve pass through
it with an isolated intersection and constructible (rational) isolating bounds. Absent that, the
cusp is not pin­nable; the constructor nonetheless produces the cusp-bearing offset set lawfully
(no output regularity is demanded). Recommendation for A3: state the negative verdict unless an
explicit constructible curve through a cusp is found.

---

## 2. The crossing lemma for non-polynomial curves

`crossing_Pconstructible` (`Basic.lean:345`) needs `F` vanishing on `T`, `S ⊆ range Γ`, and
`{t | F (Γ t) = 0}` **finite**. For offset × offset there is no cheap implicit `F` on the
offset side. Two alternatives were designed; the second is strictly simpler and is now *proved*.

### 2.1 (a) Analytic finiteness — **stated (sorry), easy**

A real-analytic non-identically-zero function on a compact interval has finitely many zeros.
Drafted in `OffsetB4.lean`:

```lean
-- STATED (sorry)
theorem finite_zeros_of_analyticOnNhd {f : ℝ → ℝ} {a b : ℝ}
    (hf : AnalyticOnNhd ℝ f (Set.Icc a b)) (hne : ∃ x ∈ Set.Icc a b, f x ≠ 0) :
    {t : ℝ | t ∈ Set.Icc a b ∧ f t = 0}.Finite

-- STATED (sorry)
theorem analytic_arcs_finite_meet {Γ₁ Γ₂ : ℝ → ℝ × ℝ} {a b : ℝ}
    (h₁ : AnalyticOnNhd ℝ (fun t => (Γ₁ t).1) (Set.Icc a b))
    (h₂ : AnalyticOnNhd ℝ (fun t => (Γ₁ t).2) (Set.Icc a b))
    (h₃ : AnalyticOnNhd ℝ (fun t => (Γ₂ t).1) (Set.Icc a b))
    (h₄ : AnalyticOnNhd ℝ (fun t => (Γ₂ t).2) (Set.Icc a b))
    (hne : ∃ x ∈ Set.Icc a b, Γ₁ x ≠ Γ₂ x) :
    {t : ℝ | t ∈ Set.Icc a b ∧ Γ₁ t = Γ₂ t}.Finite
```

Proof plan: an infinite zero set in the compact `Icc a b` has an accumulation point in it
(`Set.Infinite.exists_accPt_of_subset_isCompact` + `isCompact_Icc`); analytic continuation
(`AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero`, `isPreconnected_Icc`) forces
`f ≡ 0` on `Icc a b`, contradicting `hne`. For the two-arc version, apply the one-function
version to whichever coordinate difference is nonzero. Typical use: `F` polynomial in `(X,Y)`,
`Γ = offsetParam (γ) d` analytic with `speed ≠ 0` (so `√` is analytic by `Real.contDiffAt_sqrt`).

### 2.2 (b) Isolation-only crossing — **PROVED**

This is the cheapest interface. It drops `F`, `Γ`, `S ⊆ range Γ`, `hp` and `hfin` entirely:

```lean
-- PROVED (axioms: propext, Classical.choice, Quot.sound)
theorem crossing_PConstructible_of_isolated {S T : Set (ℝ × ℝ)}
    (hS : PConstructibleCurve S) (hT : PConstructibleCurve T) {x₀ y₀ : ℝ}
    (hS₀ : (x₀, y₀) ∈ S) (hT₀ : (x₀, y₀) ∈ T)
    (hiso : ∃ ε : ℝ, 0 < ε ∧ ∀ q ∈ S, q ∈ T → dist q (x₀, y₀) < ε →
      q = (x₀, y₀)) :
    PConstructible x₀ ∧ PConstructible y₀
```

The proof is a one-off version of the second half of `crossing_Pconstructible`: take rationals
strictly inside the ball of radius `ε`, `restrict` both curves to that box, and check the box
intersection is the singleton; then `PConstructible.inter_x/inter_y`.

### 2.3 Which route makes A2/A3/A4 cheapest

* **A2 (offset × conic).** `F` is a *polynomial* (conic implicit equation), so
  `F ∘ offsetParam` is a rational expression in `t` and `w = speed`; one rationalization clears
  it and `Polynomial.finite_setOfPred_isRoot` gives `hfin` — exactly the pattern already in
  `Offset.lean` (`offsetCross_finite_roots`). **Cheapest: finiteness/rationalization route**, no
  analytic machinery. Effort: 3–5 days on top of the existing engine.
* **A4 (rational offsets).** Both sides rational ⇒ the crossing is a polynomial system in the
  two parameters; finiteness is polynomial. **Cheapest: polynomial resultant route.** 3–5 days.
* **A3 (offset × offset).** No polynomial `F` on the second side without implicitization.
  **Cheapest: `crossing_PConstructible_of_isolated`** + prove the crossing isolated (analytic
  isolated-zeros, `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero`). The full analytic
  finiteness lemma is then optional. 1–2 weeks with implicitization avoided; longer if an
  implicit offset equation is wanted anyway.

**Verdict: the isolation-only lemma dominates for A3 and is free for A2/A4.**

---

## 3. Recovery lemmas

* `offsetParam_normal_eq_zero` (`Offset.lean:118`) holds for **every** `γ`, no regularity needed:
  the displacement to the offset is along the normal, hence orthogonal to the velocity. Nothing
  to generalise for *rational* curves; one just instantiates it.
* **Cleared rational normal equation — stated (sorry) in scratch** (`normalEq_rat_eq_zero`): for
  `γ t = (P t / D t, Q t / D t)`,

  ```lean
  (X D − P)(P' D − P D') + (Y D − Q)(Q' D − Q D') = 0   at t,
  ```

  obtained from `deriv (P/D) = (P'D − PD')/D²`. Degree ≤ `3n−1` for `deg ≤ n`. For a conic
  (`n=2`) that is ≤ 5 and for a cubic pair `D = 1` it is the known degree-5 (`2n−1`).
* **Degree-1 (proper) recovery — PROVED** (`rational_param_recovery`): given `X = P t/D t`,
  `Y = Q t/D t`, the parameter `t` satisfies the two *exact* equations

  ```lean
  theorem rational_param_recovery {P Q D : Polynomial ℝ} {X Y t : ℝ} (hD : D.eval t ≠ 0)
      (hX : X = P.eval t / D.eval t) (hY : Y = Q.eval t / D.eval t) :
      (Polynomial.C X * D - P).eval t = 0 ∧ (Polynomial.C Y * D - Q).eval t = 0
  ```

  Each is a polynomial in `t` of degree ≤ `deg` with coefficients **affine in `(X,Y)`**; a
  proper parametrization makes the common root unique, so `t` is found by a gcd / linear algebra
  over `K(X,Y)`, of degree 1 in the point — the A4 cheap-recovery claim. The degree bookkeeping
  is drafted as `proper_rational_recovery_degree` (**stated (sorry)**).
* **Recovery through a chain — PROVED** (`chain_recovery`): if `W` is the pullback of the
  crossing point under the last (invertible) affine map and `W = offsetParam γ d t`, then the
  base normal equation holds at `t`. The only missing input is inverting the affine map; nothing
  else grows. For a similarity this is exactly the base recovery; for a general affine map the
  normal equation is still available after the pullback.

---

## 4. Rationalization (norm) lemmas

**All PROVED** in `OffsetB4.lean`, no `Polynomial` API needed:

```lean
theorem rationalize {E O w S : ℝ} (hS : w ^ 2 = S) (h : E + w * O = 0) :
    E ^ 2 - S * O ^ 2 = 0

theorem rationalize_mul {g h d w S : ℝ} (hS : w ^ 2 = S) (hcross : g * w + d * h = 0) :
    g ^ 2 * S - d ^ 2 * h ^ 2 = 0
```

`rationalize` is the generic statement: any polynomial in `w` folds, using `w² = S`, to
`E + w·O = 0`, and then `(E + wO)(E − wO) − O²(S − w²) = E² − S O²`. `rationalize_mul` is the
`g·w = −d·h` sign pattern of `offsetCrossVal`; with `S = x'² + y'²`, `g = A x + B y − C`,
`h = B x' − A y'` it is exactly `offsetCrossPoly`. Every A2 family (conic, cubic, sine, …) is a
one-line instance after clearing denominators and folding.

The full *polynomial* form "`P.eval w = 0`, `w²=S` ⇒ norm vanishes" is **not needed**; if wanted,
it is `P.eval w · P.eval (−w) = 0` trivially, with the even/odd decomposition available via
`Polynomial.algEquivAevalNegX` / `Polynomial.aeval_neg`. Confirmed Mathlib names below.

---

## 5. Rational-offset curves (A4): the parabola

**Identity PROVED** (`offsetParam_parabola`), with helpers `speed_parabola`,
`parabola_offset_sq_sub/add`, `parabola_sqrt_pos`:

```lean
noncomputable def parabola (t : ℝ) : ℝ × ℝ := (t, t ^ 2)

noncomputable def parabolaOffsetRat (d s : ℝ) : ℝ × ℝ :=
  ((s ^ 2 - 1) / (4 * s) * (1 - 4 * d * s / (s ^ 2 + 1)),
   ((s ^ 2 - 1) / (4 * s)) ^ 2 + 2 * d * s / (s ^ 2 + 1))

-- PROVED
theorem offsetParam_parabola (d t : ℝ) :
    offsetParam parabola d t
      = parabolaOffsetRat d (2 * t + Real.sqrt (1 + 4 * t ^ 2))
```

Proof content: `γ' = (1, 2t)`, `speed = √(1+4t²)`, so
`offsetParam = (t − 2dt/w, t² + d/w)`; with `s = 2t + w` one has
`s² − 1 = 4ts` and `s² + 1 = 2sw`, giving `t = (s²−1)/(4s)` and `w = (s²+1)/(2s)`, whence the
displayed rational form. `parabola_sqrt_pos` shows `s > 0` for all `t` (indeed `s ≥ 1`).

* **Set equality / window bijection — untested** (next step): `s(t) = 2t + √(1+4t²)` is strictly
  increasing (`s'(t) = 2 + 4t/√(1+4t²) > 0`) with `s(0)=1`, so it is a bijection `ℝ → (0,∞)`.
  Then `offsetParam parabola d '' Icc a b = parabolaOffsetRat d '' Icc (s a) (s b)`. Needs
  `StrictMonoOn`/`Set.image_congr`; small.
* **Implicit degree [symbolic, exact].** Wolfram `Resultant` after clearing denominators gives,
  for the offset of `y=x²` by `d`, an implicit equation of total degree **6** in `(X,Y)`:
  6 terms of highest total degree, leading `−32 X⁶ + 72 X⁵ + …`, degree 6 in `X`, 4 in `Y`
  (the `d=0` factor `d²` splits off). This matches O5's `4n−2` and A4's claim of implicit
  degree 6. Reproduced by `B4-01-parabola-offset-degree.py`: the sympy factorization is
  `-262144 d² · (degree-6 factor)`, whose total `(X,Y)` degree is 6, degree 6 in `X`, 4 in `Y`.
  An independent Wolfram `Factor[Resultant[nX,nY,s]]` gave the same degree (6 in X, 4 in Y).

---

## 6. Statement shapes, lemma DAG and effort

All three drafts type-check in the scratch (`sorry` proofs).

### H1 — offset × conic engine (STATED, sorry)

```lean
-- H1: the conic crossing. `hnotid` excludes the degenerate case where the conic contains a
-- whole offset arc; it is what makes F ∘ Γ have finitely many zeros.
theorem offsetConic_cross_root_PConstructible {T : Set (ℝ × ℝ)}
    (hT : PConstructibleCurve T) {F : ℝ → ℝ → ℝ}
    {c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃ d β : ℝ}
    (hc₀ : PConstructible c₀) (hc₁ : PConstructible c₁) (hc₂ : PConstructible c₂)
    (hc₃ : PConstructible c₃) (he₀ : PConstructible e₀) (he₁ : PConstructible e₁)
    (he₂ : PConstructible e₂) (he₃ : PConstructible e₃) (hd : PConstructible d)
    {a b c e f g : ℝ}
    (hF : ∀ X Y, F X Y = a * X ^ 2 + b * X * Y + c * Y ^ 2 + e * X + f * Y + g)
    (hTzero : ∀ q ∈ T, F q.1 q.2 = 0)
    (hnotid : ∃ s : ℝ, F (offsetParam (cubicPairParam c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃) d s).1
        (offsetParam (cubicPairParam c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃) d s).2 ≠ 0)
    (hreg : cubicDer c₁ c₂ c₃ β ≠ 0 ∨ cubicDer e₁ e₂ e₃ β ≠ 0)
    (hβT : offsetParam (cubicPairParam c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃) d β ∈ T) :
    PConstructible β
```

### H2 — offset × offset engine (STATED = proved isolation lemma + isolatedness)

```lean
-- H2: apply the PROVED isolation lemma to two constructible curves. The only real work is the
-- `hiso` obligation, supplied for offsets by analytic isolated-zeros.
theorem offsetOffset_cross_isolated {S T : Set (ℝ × ℝ)}
    (hS : PConstructibleCurve S) (hT : PConstructibleCurve T) {x₀ y₀ : ℝ}
    (hS₀ : (x₀, y₀) ∈ S) (hT₀ : (x₀, y₀) ∈ T)
    (hiso : ∃ ε : ℝ, 0 < ε ∧ ∀ q ∈ S, q ∈ T → dist q (x₀, y₀) < ε →
      q = (x₀, y₀)) :
    PConstructible x₀ ∧ PConstructible y₀ :=
  crossing_PConstructible_of_isolated hS hT hS₀ hT₀ hiso
```

### H3 — degree-10 family covered (STATED, sorry)

```lean
-- H3: every real solution of x(β)√(x'(β)²+y'(β)²) = d·y'(β) for a cubic pair, d ∈ K, x a genuine
-- cubic. `Offset.lean` already proves this (`offsetCubicPair_axisCross_root_PConstructible`);
-- the shape is the template for a "whole degree covered" theorem.
theorem degreeTenFamily_covered {c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃ d : ℝ}
    (hc₀ : PConstructible c₀) (hc₁ : PConstructible c₁) (hc₂ : PConstructible c₂)
    (hc₃ : PConstructible c₃) (he₀ : PConstructible e₀) (he₁ : PConstructible e₁)
    (he₂ : PConstructible e₂) (he₃ : PConstructible e₃) (hd : PConstructible d)
    (hlead : c₃ ≠ 0) {β : ℝ}
    (hreg : cubicDer c₁ c₂ c₃ β ≠ 0 ∨ cubicDer e₁ e₂ e₃ β ≠ 0)
    (hcross : cubicVal c₀ c₁ c₂ c₃ β
        * Real.sqrt (cubicDer c₁ c₂ c₃ β ^ 2 + cubicDer e₁ e₂ e₃ β ^ 2)
      = d * cubicDer e₁ e₂ e₃ β) :
    PConstructible β
```

### Lemma DAG

```
rationalize ─┬─> rationalize_mul ─> offsetCross_finite_roots (exists) ─> H1
             └─> rationalize_add_mul
crossing_PConstructible_of_isolated ──────────> H2
finite_zeros_of_analyticOnNhd ─> analytic_arcs_finite_meet ─> (hiso for H2)
speed_parabola, parabola_offset_sq_add/sub ─> offsetParam_parabola ─> window/bijection ─> A4
rational_param_recovery ─> proper_rational_recovery_degree ─> A4 recovery
chain_recovery ─> A4 chain recovery
(Offset.lean) offsetCubicPair_axisCross_root_PConstructible ─> H3
```

### Effort estimates (Lean person-days) and recommended order

| step | content | estimate |
|---|---|---|
| 1 | norm/rationalization (`rationalize*`) | **0.1 (done)** |
| 2 | isolation crossing (`crossing_PConstructible_of_isolated`) | **0.2 (done)** |
| 3 | parabola identity (`offsetParam_parabola`) | **0.3 (done)**; +0.5 for the window bijection |
| 4 | recovery (`normalEq_rat_eq_zero`, degree bookkeeping, chain) | 1.5 |
| 5 | analytic finiteness (`finite_zeros_of_analyticOnNhd`, arcs) | 2–3 |
| 6 | H1 offset×conic (conic rationalization + reuse of engine) | 4–6 |
| 7 | H2 offset×offset (isolation + implicit offset equation, or isolation alone) | 8–15 |
| 8 | H3 degree-10 family (reuse `Offset.lean`) | 0.5 |

**Recommended order:** 1, 2, 3, 4, then 6 (cheap, high value, reuses `Offset.lean`), then 5,
then 7. H3 is free once `Offset.lean` is imported.

---

## Confirmed Mathlib lemma names

* `AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero` (module
  `Mathlib.Analysis.Analytic.IsolatedZeros`) — analytic continuation.
* `AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero` (module
  `Mathlib.Analysis.Analytic.Uniqueness`).
* `AnalyticOnNhd.preimage_zero_mem_codiscreteWithin` (module `Mathlib.Analysis.Analytic.Order`).
* `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero`,
  `AnalyticAt.frequently_zero_iff_eventually_zero` (isolated zeros).
* `Set.Infinite.exists_accPt_of_subset_isCompact` (module
  `Mathlib.Topology.Compactness.Compact`).
* `Real.contDiffAt_sqrt`, `ContDiffAt.sqrt`, `DifferentiableAt.sqrt`, `ContinuousWithinAt.sqrt`
  (module `Mathlib.Analysis.SpecialFunctions.Sqrt`).
* `Polynomial.finite_setOfPred_isRoot` (used in `Offset.lean`).
* `Polynomial.algEquivAevalNegX`, `Polynomial.aeval_neg` (even/odd, module
  `Mathlib.Algebra.Polynomial.AlgebraMap`).
* Project: `crossing_Pconstructible` (`Basic.lean:345`), `exists_rat_box_isolating`
  (`Basic.lean:290`), `exists_rat_btwn`, `rat_Pconstructible`, `offsetParam_normal_eq_zero`
  (`Offset.lean:118`), `offsetCross_finite_roots` (`Offset.lean:402`),
  `offsetCubicPair_cross_root_PConstructible` (`Offset.lean:595`).

Rate limits / LSP notes: `lean_loogle` is 3/30 s; the file imports `Pptc.Offset`, so a full
diagnostic pass takes ~60–120 s. `lean_verify` on the two key proved lemmas returns exactly
`propext`, `Classical.choice`, `Quot.sound`.

---

## Side discoveries

1. **`offset` needs no constructible endpoints** (contrast `arc_length`/`arc_of_length`). One can
   offset the far arc of an `arc_of_length` output and get a constructible curve without ever
   pinning the far endpoint. This is a permissiveness that helps B3 (`arc_length` on offsets) and
   any construction that crosses an offset to reach a transcendental endpoint.
2. **`crossing_PConstructible_of_isolated` is a strictly cheaper interface than
   `crossing_Pconstructible`** and is now proved. Any future task that can show an isolated
   crossing (analytic isolated-zeros, transversality, or direct computation) can skip
   implicitization and finiteness entirely. This is potentially useful far beyond offsets.
3. **The norm lemma needs no `Polynomial` API.** Every offset-cross equation folds to
   `E + w·O = 0` with `w² = S`; `rationalize` handles all of them. The "polynomial in `w`" framing
   in the plan is unnecessary machinery.
4. **Graph curves are offset-friendly by construction:** `speed ≥ 1` for every `x`-parametrized
   tracing, so `hreg` is free and `hinj` is free. All legality difficulty lives on closed/
   reparametrized curves (ellipse, offset-of-offset, chains).
5. **The parabola offset is rationally reparametrized by `s = 2t + √(1+4t²) ∈ [1,∞)`**, and
   Wolfram confirms implicit total degree 6 (6 in X, 4 in Y), consistent with O5. The identity is
   proved, so A4's rational-offset entry can be formalized immediately.
6. **`offset` does not remember its tracing.** The output is a set, so *which* smooth tracing
   produced it (and hence whether a second offset is legal) is not recoverable from the object.

---

## Leads for other tasks

* **A2**: use `rationalize`/`rationalize_mul` to clear the conic's square root, then
  `Polynomial.finite_setOfPred_isRoot` exactly as `offsetCross_finite_roots` does; no new
  analytic result is needed. `hnotid` (conic not containing an offset arc) is the only side
  condition.
* **A3**: use `crossing_PConstructible_of_isolated` for both offset × offset and self-crossings;
  the only obligation is `hiso`. For self-crossings restrict to disjoint constructible windows
  (L11); for cusps take the negative verdict unless a constructible curve through the cusp is
  exhibited (L12).
* **A4**: `rational_param_recovery`, `chain_recovery` and `offsetParam_parabola` are ready to use.
  Next Lean step is the window bijection `offsetParam parabola d '' Icc a b =
  parabolaOffsetRat d '' Icc (s a) (s b)`; `s` is strictly increasing with `s ≥ 1`.
* **B1/B2**: the offset-of-offset `C²` gap (L7) is worth stating in any chain theorem; if a chain
  uses only base curves with smooth tracings it is harmless, but a construction that relies on
  re-offsetting the *set* needs the arc-length-reparametrization (IFT) argument.
* **B3**: `speed(offset) = |v|·|1−dκ|` (O1); on a cusp-free window the arc length of an offset is
  `L − d·(θ(b)−θ(a))` (O2), and the endpoints are not required to be constructible for the arc
  to exist.
* **Z**: the isolation-only lemma may let the programme drop the analytic-finiteness development
  entirely, provided isolatedness can always be established; consider making it the canonical
  crossing interface.

---

## Defs.lean modelling issue for `offset` that X4 missed

**`offset` is not closed: it takes `C¹` but produces only a set, and a second offset needs
`C²`.** The constructor's smoothness hypothesis is `hC1 : ContinuousOn (deriv γᵢ) (Icc a b)`
(Defs.lean:382–383) plus pointwise differentiability — i.e. `γ` is `C¹`. But
`offsetParam γ d` has derivative involving `unitNormal'`, hence `γ''` and `speed'`; it is `C¹`
only when `γ` is `C²`. Since the output records only the point-set, re-offsetting the output
requires *re-supplying* a `C²` tracing that the constructor neither demands nor stores.

X4's item 5 ("`offset` needs `hreg` and `hC1`, so a corner cannot be offset") noted the
restriction on the *input*; it did not note that the operation **cannot be iterated from its own
output**. This matters for A3/A4 chains and for any formal theorem of the form
"offset of offset": such a theorem must carry `ContDiffOn ℝ 2 γ (Icc a b)`
(or prove the arc-length-reparametrization lemma via the inverse function theorem). For the six
base families the chosen tracings are `C^∞`, so no reachable value is lost, but the class is not
syntactically closed. Suggested fix: add a `C²` (or `ContDiffOn ℝ 2`) hypothesis to `offset`,
or store the generating tracing/stroke in `PConstructibleCurve`.
