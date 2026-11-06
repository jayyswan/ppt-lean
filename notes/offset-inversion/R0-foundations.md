# R0 — foundations of offset inversion against `Defs.lean`

**Stream:** R0. **Deliverable:** this file. **No `.lean` edits.**

Sources read: `PLAN-offset-inversion.md` §0/§1/§R0/L1/L2;
`notes/offset-inversion-tangent-angle.md`; `Pptc/Defs.lean` (all of it);
`Pptc/Offset.lean`; `Pptc/BoxOffset.lean`; `Pptc/Box.lean` (box and arc-endpoint
statements); `Pptc/Jacobi.lean` (Outlook); `Pptc/Basic.lean` (searched for the
lemmas L1/L2 can reuse).

Labels: **[Proof]**, **[Wolfram]**, **[Heuristic]**, **[Open]**. Wolfram numbers were
computed at 40–90 digits in one session; the residual is quoted with each identity.

---

## 0. Verdicts in one paragraph

With the definitions exactly as in `Defs.lean` — `unitNormal = (-y', x')/speed` (the
counterclockwise quarter turn, i.e. the *left* normal) and
`κ = (x'y'' − y'x'')/speed³` — the speed identity

  `speed (offsetParam γ d) t = |1 − d κ(t)| · speed γ t`

is **[Proof]** true under the hypotheses "`γ` is twice differentiable at `t` and
`speed γ t ≠ 0`" (pointwise C², not C¹).  The stronger, junk-level statement with no
nonzero-speed hypothesis is also true, but only because both sides are `0` for junk
reasons when `speed γ t = 0`; see §2.  An offset **cusp** is *not* forbidden by the
`offset` constructor (`hreg` is about `speed γ`, not about `1 − dκ`), it remains
differentiable with speed zero, and it is **injectively traced** whenever it is an
ordinary cusp (`κ' ≠ 0` at the cusp).  Hence `arc_of_length` *can* be laid across a
cusp, with length `∫|1 − dκ|·speed`; what fails is not legality but the **box readout**
(no coordinate is monotone across a cusp).  For the parabola with `d < 1` the readout
is monotone and gives the quartic

  `w⁴ − 2e w³ + (1 + e² − d²) w² − 2e w + e² = 0`

for the slope `w` in terms of the boxed endpoint abscissa `e`; for `d > 0` the valid root
is the unique one with `w > e`, for `d < 0` the unique one with `w < e`, and for `d = 0`
it is `w = e` (a double root).

---

## 1. Vocabulary and conventions used below

For `γ : ℝ → ℝ × ℝ` write `x(t) := (γ t).1`, `y(t) := (γ t).2`, and

```
s(t)   := speed γ t = √(x'(t)² + y'(t)²)                 (Defs.lean)
n(t)   := unitNormal γ t = (−y'(t)/s(t), x'(t)/s(t))      (Defs.lean)
P_d(t) := offsetParam γ d t = γ(t) + d·n(t)               (Defs.lean)
```

`n` is the velocity turned a quarter turn **counterclockwise** and normalised.  For a
counterclockwise circle `(cos t, sin t)` this is the *inward* normal; so **positive `d`
moves to the left of the direction of travel**, i.e. toward the concave side.  This is
exactly the convention in the docstring of `offsetParam`, and it is the convention that
makes the sign of `κ` below come out right.

I use `x' := deriv x`, `x'' := deriv (deriv x)`, etc., and

```
κ(t) := (x'(t)·y''(t) − y'(t)·x''(t)) / s(t)³ .
```

This is the standard **counterclockwise-positive** curvature: for the CCW unit circle
`x'y'' − y'x'' = 1`, `s = 1`, so `κ = +1`; for the clockwise circle it is `−1`.
[Proof: direct computation; also checked symbolically in Wolfram.]  Note that at
`s(t) = 0` Lean's division gives `κ(t) = 0` (junk), which is exactly what makes the
junk-level identity below true.

`ψ` always denotes a **tangent angle**, i.e. a function with `ψ' = κ·s`.  Concretely,
on a window where `x' ≠ 0`, `ψ = Real.arctan (y'/x')` has

```
ψ' = (x'y'' − y'x'')/(x'² + y'²) = κ·s .
```

[Proof: quotient rule and `x'² + y'² = s²`.]  This is the representation recommended
for L1/L2; see §6.

---

## 2. Q1 — the speed identity

### 2.1 The key derivative identity [Proof]

**Claim.**  If `x` and `y` are differentiable at `t`, `x'` and `y'` are differentiable
at `t`, and `s(t) ≠ 0`, then

```
P_d'(t) = (1 − d·κ(t))·γ'(t) ,                                                (2.1)
```

i.e. componentwise

```
d/dt [x − d·y'/s] = (1 − dκ)·x' ,      d/dt [y + d·x'/s] = (1 − dκ)·y' .
```

**Proof.**  Since `s² = x'² + y'²` and `s(t) ≠ 0`,

```
s' = (x'x'' + y'y'')/s .
```

Differentiate the first coordinate of `P_d`:

```
d/dt [x − d·y'/s]
  = x' − d·(y''s − y's')/s²
  = x' − d·y''/s + d·y'(x'x'' + y'y'')/s³ .
```

Now `(1 − dκ)x' = x' − d·x'(x'y'' − y'x'')/s³`, and the two right-hand sides agree
because

```
−d·y''/s + d·y'(x'x'' + y'y'')/s³
  = [−d·y''s² + d·x'y'x'' + d·y'²y'']/s³
  = [−d·y''x'² + d·x'y'x'']/s³
  = −d·x'(x'y'' − y'x'')/s³ .
```

The second coordinate is the same computation with `x` and `y` exchanged and one sign
flip:

```
d/dt [y + d·x'/s]
  = y' + d·x''/s − d·x'(x'x'' + y'y'')/s³
  = y' − d·y'(x'y'' − y'x'')/s³
  = (1 − dκ)·y' . ∎
```

An equivalent, more conceptual proof is `n' = −κs·T` with `T = γ'/s`: the unit tangent
`T` turns at rate `ψ' = κs` into `n`, so `n' = −ψ'T = −κsT`, and
`P_d' = γ' + d n' = sT − dκsT`.  Both are the same algebra.

### 2.2 The speed identity [Proof]

**Claim.**  Under the hypotheses of §2.1,

```
speed (offsetParam γ d) t = |1 − d·κ(t)| · speed γ t .                         (2.2)
```

**Proof.**  By (2.1) the velocity of `P_d` is `(1 − dκ)·(x', y')`.  Therefore

```
speed P_d = √(((1 − dκ)x')² + ((1 − dκ)y')²)
          = √((1 − dκ)²(x'² + y'²))
          = |1 − dκ|·√(x'² + y'²) = |1 − dκ|·s . ∎
```

The absolute value is genuinely needed: on the far side of an offset cusp the factor
`1 − dκ` is negative and the tracing runs backwards.  Without the absolute value the
identity holds exactly on the cusp-free side `1 − dκ ≥ 0`, which is the version the
arc-length formula uses.

### 2.3 Exact hypotheses

* **C² is needed, not C¹.**  (2.1) differentiates `x'` and `y'`, so it needs
  `DifferentiableAt (deriv x) t` and `DifferentiableAt (deriv y) t`, in addition to
  `x`, `y` differentiable at `t`.  Pointwise this is what I will call "C² at `t`".
  The `offset` constructor only assumes `hC1` (continuity of `x'`, `y'`); the speed
  identity is therefore **strictly stronger than the constructor's hypothesis list**.
  This mismatch is real and must be reported: L1 has to add the C² hypothesis.
* **`speed γ t ≠ 0` is needed** to differentiate `1/s` and to know `s² > 0` when
  taking the square root.  It is *not* needed for the bare truth of (2.2) (next
  paragraph), only for the honest derivation.
* **No hypothesis on `κ` is needed**; `κ` is defined by the formula and is finite
  whenever `s ≠ 0`.
* **No hypothesis that `1 − dκ ≠ 0`** is needed; the absolute value handles the sign.

### 2.4 The junk value at `speed γ t = 0` [Proof]

The identity (2.2) is in fact true at every point where `γ` is twice differentiable,
with **no** nonzero-speed hypothesis, but the reason is junk:

* At `s(t) = 0` we have `x'(t) = y'(t) = 0`, hence `κ(t) = 0/0 = 0` in Lean and the
  right side of (2.2) is `|1 − 0|·0 = 0`.
* `n(t) = (0, 0)` (Lean's `0/0`), while at every nearby point with `s ≠ 0` the vector
  `n` has length one.  So `n` is discontinuous at `t` — unless `s ≡ 0` on a
  neighbourhood of `t`, in which case `γ` is constant there and `P_d = γ` is
  differentiable with derivative `0`.
* `γ` is continuous at `t` (it is differentiable), and `d·n` is discontinuous there
  (for `d ≠ 0`), so `P_d` is discontinuous at `t`.  A discontinuous function has
  `deriv = 0` in Lean, so both coordinates of `P_d'(t)` are `0` and
  `speed P_d(t) = 0`.

Thus (2.2) holds at `s = 0`, vacuously.  **Caveat for L1:** proving this in Lean
requires a small argument that `unitNormal` is discontinuous at an isolated zero of
`speed`; it is not worth the trouble for the headline theorem, where `speed γ ≠ 0`
holds on the whole window.  I recommend L1 state (2.2) with `speed γ t ≠ 0` and record
the junk case only in a comment.  Do **not** state the identity as
`(1 − dκ)·speed γ` without the absolute value: at a cusp the two sides have opposite
signs.

### 2.5 Curvature sign check [Proof + Wolfram]

With `κ = (x'y'' − y'x'')/s³` and `n = (−y', x')/s`:

* CCW unit circle `(cos t, sin t)`: `x' = −sin t`, `y' = cos t`, `x'' = −cos t`,
  `y'' = −sin t`; numerator `= sin²t + cos²t = 1`, `s = 1`, so `κ = 1`.  The offset is
  `(1 − d)(cos t, sin t)` and has speed `|1 − d| = |1 − dκ|·1`. ✔
* CW unit circle `(cos(−t), sin(−t))`: `κ = −1`.  The offset is `(1 + d)(cos t, sin t)`
  going clockwise, speed `|1 + d| = |1 − d(−1)|·1`. ✔
* The sign is therefore the one that makes (2.2) true, and the offset of a CCW circle
  by positive `d` shrinks it, matching "positive `d` is to the left".

[Wolfram] symbolic residuals: general curve and parabola both reduce to `0`; pointwise
numeric residuals at `d ∈ {1/2, −3, 9/10}` and three parameters were `0` to 50 digits.

---

## 3. Q2 — the `arc_of_length` hypotheses, and cusps

### 3.1 The constructor, verbatim

From `Pptc/Defs.lean` (lines 382–394):

```
| arc_of_length {S : Set (ℝ × ℝ)} (hS : PConstructibleCurve S)
    (γ : ℝ → ℝ × ℝ) {a b : ℝ} (hab : a ≤ b)
    (hsub : γ '' Set.Icc a b ⊆ S)
    (hinj : Set.InjOn γ (Set.Icc a b))
    (hdiff : ∀ t ∈ Set.Icc a b,
      DifferentiableAt ℝ (fun s => (γ s).1) t ∧ DifferentiableAt ℝ (fun s => (γ s).2) t)
    (hint : IntervalIntegrable (speed γ) MeasureTheory.volume a b)
    (hx₀ : PConstructible (γ a).1) (hy₀ : PConstructible (γ a).2)
    {x : ℝ} (hx : PConstructible x) (hlen : arcLengthOf γ a b = x) :
    PConstructibleCurve (γ '' Set.Icc a b)
```

Exactly five analytic requirements: `a ≤ b`; the image lies in a constructible `S`;
the tracing is injective on `Icc a b`; each coordinate is differentiable at each point
of `Icc a b` (pointwise — **not** C¹, and the derivative need not be continuous or
nonzero); `speed γ` is interval-integrable.  Plus the two P-constructible coordinates of
the start and the P-constructible length `x` with `arcLengthOf γ a b = x`.

The `offset` constructor (Defs, after the 2026-11 soundness repair) is:

```
| offset {S} (hS : PConstructibleCurve S) (γ : ℝ → ℝ × ℝ) {a b : ℝ} (hab : a < b)
    (himg : γ '' Set.Icc a b = S) (hinj : Set.InjOn γ (Set.Ico a b))
    (hseam : γ b = γ a → unitNormal γ b = unitNormal γ a)
    (hdiff : ∀ t ∈ Set.Icc a b, DifferentiableAt ... ∧ DifferentiableAt ...)
    (hreg : ∀ t ∈ Set.Icc a b, speed γ t ≠ 0)
    (hC1 : ContinuousOn (deriv (fun s => (γ s).1)) (Set.Icc a b) ∧
      ContinuousOn (deriv (fun s => (γ s).2)) (Set.Icc a b))
    {d : ℝ} (hd : PConstructible d) :
    PConstructibleCurve (offsetParam γ d '' Set.Icc a b)
```

Two points of this signature govern everything below. First, `himg` is an **equality**:
`offset` acts on the whole drawn curve, not on a sub-arc. A sub-arc must first be made a
curve of its own (`restrict`, `arc_of_length`, ...), and then that whole curve may be
offset. Second, `a < b` is strict, so a singleton window cannot be offset; the endpoint
normal is the one-sided normal from inside the window. Closed curves are still allowed
because `hinj` is only on `Ico a b`, with `hseam` supplying the matching normal at the
join. `Pptc/Offset.lean`'s `offset_open` discharges `hseam` for an open arc injective on
`Icc a b`.

**Critical distinction.**  `hreg` says `speed γ ≠ 0` — the *base* curve is regular.
It says nothing about `1 − dκ`.  The docstring says so explicitly: "No injectivity is
claimed of the offset itself, and it can genuinely fail: pushed further than the radius
of curvature a parallel copy folds over and acquires cusps and self-crossings.  That is
what the operation draws, so it is not excluded."  So the `offset` constructor
**does not forbid** an offset cusp; it only forbids a cusp of the *base*.

### 3.2 Which offset arcs satisfy `arc_of_length`

Take a base **curve** already presented as a whole tracing `γ` on `[A,B]` and satisfying
`offset`'s hypotheses there (`himg : γ '' Icc A B = S`, `A < B`, `hinj` on `Ico A B`,
`hseam`, and the regularity conditions), with `C²` (so that `P_d` is C¹).  Offset the
whole base curve: let `S := offsetParam γ d '' Icc A B`, a `PConstructibleCurve` by
`offset`.  Only then let `[a,b] ⊆ [A,B]` and apply `arc_of_length` to `S`.

* `hsub` holds with `S` as above (indeed `P_d '' Icc a b ⊆ P_d '' Icc A B`).  This is
  the whole-arc route: the sub-arc is not offset directly; it is carved out of an
  already-offset whole curve.
* `hdiff` for `P_d` holds: `unitNormal` is C¹ wherever `s ≠ 0` and `x',y'` are C¹
  (quotient of C¹ functions with nonvanishing denominator).  Note this needs **C² on
  the base**, not merely the `hC1` of `offset`; the `offset` constructor is happy with
  a C¹ base because it only needs `P_d` *continuous*, but `arc_of_length` needs `P_d`
  *differentiable*.
* `hint` holds because `speed P_d = |1 − dκ|·s` is continuous on `[a,b]` when `κ` and
  `s` are (C² base).
* `hx₀, hy₀` are the coordinates of the offset start; these are P-constructible when
  the base point and the tangent angle there are (see §4).
* `hinj` is the only real question, and it is a question about `P_d`, not about `γ`.

So a **regular** base arc gives an offset arc that satisfies every hypothesis of
`arc_of_length` except possibly `hinj`; `hinj` holds on windows where `P_d` does not
self-intersect (e.g. any window on which one coordinate is strictly monotone).

### 3.3 What happens at an offset cusp [Proof]

Let `t₀` be a point with `1 − dκ(t₀) = 0`, the base regular (`s(t₀) ≠ 0`), the base C²,
`d ≠ 0`, and `κ'(t₀) ≠ 0` (an *ordinary* cusp).  Write `λ(t) := 1 − dκ(t)`, so
`P_d' = λ·s·T`, `λ(t₀) = 0` and `λ'(t₀) = −dκ'(t₀) ≠ 0`.

**(a) Differentiability.**  `P_d` is differentiable at `t₀` (indeed C¹ near it), because
it is built from `γ` and the C¹ function `n`.  Its derivative there is `0`.  So the
tracing does **not** stop being differentiable at a cusp; it merely stops moving.

**(b) Speed.**  `speed (offsetParam γ d) t₀ = |1 − dκ(t₀)|·s(t₀) = 0`.  The cusp is a
zero of the offset speed.  This is allowed by `arc_of_length`: its `hdiff` is pointwise
differentiability, and the docstring of `arc_length` says a curve may "stop dead in
`arc_of_length`, where it merely contributes no length".

**(c) Injectivity.**  Taylor expand about `t₀`.  Since `P_d' = λsT` and `λ(t₀)=0`,

```
P_d(t) − P_d(t₀) = ½·λ'(t₀)s(t₀)T(t₀)·(t − t₀)² + O((t − t₀)³) ,
```

so both halves leave `P_d(t₀)` in the **same** direction `±T(t₀)`.  Comparing the two
halves,

```
P_d(t₀+u) − P_d(t₀−u) = (1/3)·P_d'''(t₀)·u³ + O(u⁵) ,
```

and

```
P_d'''(t₀) = λ''(t₀)sT + 2λ'(t₀)(sT)'(t₀)
          = λ''(t₀)sT + 2λ'(t₀)κ(t₀)s(t₀)²·n(t₀) ,
```

whose second summand is nonzero because `λ'(t₀) ≠ 0`, `κ(t₀) ≠ 0`, `s(t₀) ≠ 0`, `n ≠ 0`.
So the two halves are **distinct** analytic branches meeting cubically at the cusp: in the
orthonormal frame `(T(t₀), n(t₀))` they are graphs `N = a_±·T^{3/2}` with
`a_+ ≠ a_-`, which meet only at `T = 0`.  Hence `P_d` is injective on a sufficiently
small neighbourhood of `t₀` (and on any larger window that has no other
self-intersection).  [Wolfram: for the parabola at `d = 2`,
`w₀ = √(2^{2/3}−1)`, `κ'(w₀) = −0.7242…`, and the `u³` coefficient of the branch
separation is `(−8·2^{1/3} + 5·2^{2/3})/4 ≈ −0.535 ≠ 0`.]

**(d) When injectivity fails.**  If `κ'(t₀) = 0` (the cusp is degenerate / higher-order
contact) the two branches may agree to higher order and the tracing may retrace; if
`1 − dκ` vanishes to even order without changing sign there is a fold rather than a
cusp.  And if the offset degenerates to a point (`d = 1` on the unit circle) the tracing
is constant and `hinj` fails outright.  These are genuine but non-generic.

**Verdict.**  At an ordinary offset cusp the traced arc **is** injective and the tracing
**is** differentiable; `speed` is zero there.  So a cusp is not an obstruction to
`arc_of_length`.

### 3.4 Can an arc be laid *across* a cusp with length `∫|1 − dκ|`? [Proof]

**Yes, literally**, whenever the offset tracing is injective across the cusp (which
§3.3(c) gives for an ordinary cusp, on a window with no other self-intersection).
Indeed, with `a < t₀ < b`:

* `hsub` holds for `S = offsetParam γ d '' Icc A B` with `A ≤ a < b ≤ B`, where `S` is
  the **whole** offset curve produced by one application of `offset` on `γ` over
  `[A,B]` (not by offsetting `[a,b]` directly);
* `hdiff` holds (C² base, `s ≠ 0` on the base window);
* `hint` holds (`speed P_d = |1−dκ|s` is continuous);
* `hinj` holds by §3.3(c);
* `arcLengthOf (offsetParam γ d) a b = ∫_a^b |1 − dκ|·s` by (2.2), which is exactly the
  length the constructor integrates.

So crossing a cusp is **legal**.  The `hreg` hypothesis does **not** forbid it (it is
about the base), and `arc_of_length` does **not** require `1 − dκ ≠ 0`.

**But the readout fails.**  At a cusp `X' = (1 − dκ)x'` and `Y' = (1 − dκ)y'` both change
sign at `t₀`, so **neither coordinate is monotone across the cusp**.  `box_xmax` on the
full arc therefore returns a critical value (the cusp abscissa, as in
`BoxOffset.offsetCuspAbscissa`), not the far endpoint.  To read the far endpoint one
must either

* start the `arc_of_length` **at the cusp** (then the monotone branch from the cusp to
  the endpoint is boxable), or
* `restrict` to a sub-window on one side of the cusp, or
* intersect with a second constructible curve.

**What the cusp does to the equation.**  On a window where the base is parametrized by
its tangent angle (`κ ≠ 0`), put `Φ(t) := R(ψ(t)) − d·ψ(t)` with `R` the Whewell
function, so `Φ' = (1 − dκ)s = λs`.  If `λ < 0` on `[a,t₀)` and `λ > 0` on `(t₀,b]`,
then

```
arcLengthOf (offsetParam γ d) a b
  = −(Φ(t₀) − Φ(a)) + (Φ(b) − Φ(t₀))
  = Φ(a) + Φ(b) − 2Φ(t₀) ,                                                   (3.1)
```

so the endpoint satisfies

```
Φ(b) = x − Φ(a) + 2Φ(t₀) .                                                  (3.2)
```

This is the **same** functional form `R(ψ) − dψ`, with the right-hand side shifted by
the P-constructible constant `2Φ(t₀) − Φ(a)`.  It therefore does **not** add a new
equation family; what it adds is (i) access to the far branch when `d > 1`, and (ii) the
possibility of starting at the cusp.  [Wolfram: parabola, `d = 2`, `a = 0`, `b = 5/2`;
`∫_0^{5/2}|s − 2/(1+w²)|dw = 2.7526133868…`, matching (3.1) to residual `1e−78`.]

So the source note's phrase "that doubles the reachable equation family to
`R(ψ) − dψ` on each side" should be read as *the same family reached from a different
base point*, not as a second independent family.  [This is a correction of the note's
phrasing; the formula (3.2) is [Proof].]

---

## 4. Q3 — the starting point

`arc_of_length` requires `PConstructible (γ a).1` and `PConstructible (γ a).2` for the
**tracing** — here `γ` is `offsetParam γ₀ d`.  It does **not** require the base point
`γ₀(a)` or `ψ(a)` to be P-constructible, but the *equation* `R(ψ) − dψ = x` is only a
P-constructible statement when `ψ(a)` is.

**Sufficient condition [Proof].**  If `γ₀(a)` is a P-constructible point and `ψ(a)` is
P-constructible, then

```
offsetParam γ₀ d a = γ₀(a) + d·(−sin ψ(a), cos ψ(a))
```

has P-constructible coordinates, because `Real.cos` and `Real.sin` of a
P-constructible number are P-constructible (`cos_sin_Pconstructible`,
`cos_Pconstructible`, `sin_Pconstructible` in `Pptc/Basic.lean`), and `d` is
P-constructible.  So this is the clean sufficient criterion.

**Which points qualify.**

* **Vertices.**  The parabola vertex `(0,0)` has both coordinates P-constructible
  (`zero_Pconstructible`), and `ψ = 0` there (`Real.arctan 0 = 0`).  Its offset image is
  `(0,d)`, P-constructible since `d` is.  So `(0,d)` is a legal start, with
  `R(0) − d·0 = 0`.  This is the start used by L2.
* **Points at a P-constructible parameter**, for a curve presented as a polynomial graph
  (or an affine image of one): if `t₀` is P-constructible, then `(t₀, p(t₀))` has
  P-constructible coordinates (`eval_Pconstructible` / `pconstructible`), and the slope
  `p'(t₀)` is P-constructible, so `ψ = arctan (slope)` is P-constructible
  (`arctan_Pconstructible`).  The same holds after `translate_*` / `scale_*`, since those
  only apply P-constructible affine data.
* **Cusps.**  At an offset cusp `1 − dκ(t₀) = 0`, i.e. `κ(t₀) = 1/d`.  Whether the cusp
  point is P-constructible is curve-dependent, but for the **parabola** it is: with
  `s² = 1 + w²` and `κ = 1/s³`, the cusp slope `w₀` satisfies `(1 + w₀²)³ = d²`, a
  degree-6 polynomial with P-constructible coefficients `1` and `−d²`, so
  `w₀` is P-constructible by `root_Pconstructible_le_six_coeffs`; then
  `ψ(t₀) = arctan w₀` is P-constructible and the cusp point
  `(w₀(1 − d^{2/3}), w₀²/2 + d^{2/3})` is P-constructible (since `d^{2/3} = d/√(1+w₀²)`
  and `√(1+w₀²)` is P-constructible).  [Proof; degree exactly 6,
  which is the constructor's limit.]  For a general curve this is [Open]: it asks that
  `κ(t) = 1/d` have a P-constructible solution `t₀` with `ψ(t₀)` P-constructible, and
  `κ` is not in general an algebraic function of a P-constructible parameter (it involves
  `speed³`).
* **Not sufficient:** a point whose coordinates happen to be P-constructible but whose
  `ψ` is transcendental.  The arc can still be laid (the endpoint coordinate is
  P-constructible by the box), but the displayed equation has a non-P-constructible
  constant.

---

## 5. Q4 — the readout

### 5.1 When the box returns the endpoint [Proof]

From (2.1),

```
dX/dt = (1 − dκ)·x' ,        dY/dt = (1 − dκ)·y' .                          (5.1)
```

So on a window where `1 − dκ > 0`:

* if `x' ≥ 0` on `[a,b]`, then `X` is nondecreasing, so the abscissa is largest at the
  right endpoint and `box_xmax` on the laid arc returns `X(b)`.  This is exactly
  `Box.arc_xendpoint_Pconstructible` (requires `PConstructibleCurve (P_d '' Icc a b)`,
  `a ≤ b`, `ContinuousOn P_d`, `MonotoneOn (fun t => (P_d t).1)`), or
  `BoxOffset.offsetArc_box_xmax_Pconstructible` / `offsetArc_box_xmax_of_offsetHyp` for
  the offset-specific packaging.  If `x' ≤ 0`, use the antitone version
  `arc_xendpoint_antitone_Pconstructible` (box gives the endpoint as a *minimum*, which
  is still the endpoint).
* The same with `y` and `box_ymax` / `box_ymin`.
* If `1 − dκ < 0` the signs reverse: `X` is monotone in the opposite direction, and one
  uses the antitone/`box_xmin` variant.  The hypotheses are symmetric because `−d` is
  P-constructible whenever `d` is (as the `offset` docstring notes).

For the parabola with `x' = 1` and `d < 1`: `1 − dκ = 1 − d/s³ ≥ 1 − d > 0`, so `X` is
**strictly** increasing on all of `[0,b]` and `box_xmax` returns `X(b)` with no
restriction.  [Proof: `s ≥ 1`, `κ ≤ 1`, so `dκ ≤ d < 1`.]

### 5.2 When it does not [Proof/Heuristic]

If `1 − dκ` changes sign (a cusp lies inside the arc), no coordinate is monotone across
the cusp by (5.1), and `box_xmax` returns a critical value (the cusp abscissa), not the
endpoint.  Three remedies:

1. **Start at the cusp.**  If the cusp point is P-constructible (§4), lay an arc of the
   **residual** length `x − |Φ(c) − Φ(a)|` (P-constructible when the cusp is) from it
   along the monotone branch; then the box returns the endpoint.  This is the cleanest
   remedy for `d > 1`.  [Proof, given the cusp is P-constructible.]
2. **`restrict`.**  If `[c,b]` is a sub-window on which the relevant coordinate is
   monotone and the window bounds are P-constructible, `restrict` cuts the laid arc to
   that sub-arc and the box reads its endpoint.  The cut values `X(c)`, `Y(c)` must be
   P-constructible; this is automatic if `c` is a P-constructible parameter (or the
   cusp).  The upper bound can always be made P-constructible: the endpoint is at
   distance at most `x` from the start, so `X(b) ≤ X(a) + x` and
   `|Y(b) − Y(a)| ≤ x`, and `X(a)`, `Y(a)`, `x` are all P-constructible.  [Proof.]
3. **Intersection.**  Intersect the laid arc with a second constructible curve meeting
   it in exactly one point at the endpoint.  This is legal in principle
   (`PConstructible.inter_x`), but constructing the second curve requires knowing the
   endpoint, so it is not a uniform route; it is only useful when the second curve is
   independently available (as in the circle/ellipse arguments of `Pptc.Basic`).  I know
   of no uniform choice for offsets.  [Heuristic — no impossibility proof.]

### 5.3 The parabola readout and the quartic [Proof + Wolfram]

Parametrize the parabola as `γ(w) = (w, w²/2)`, so

```
s = √(1 + w²) ,     κ = 1/s³ ,     ψ = arctan w ,
R(w) = ∫_0^w √(1+u²) du = (w√(1+w²) + arsinh w)/2 ,
```

and the offset is

```
X(w) = w − d·w/s = w(1 − d/√(1+w²)) ,      Y(w) = w²/2 + d/s .
```

[The parabola `y = x²/2` is a `poly_graph` with rational coefficients:
`Polynomial.C (1/2) * X^2`, so it is a `PConstructibleCurve` without any scaling step.
The `R` above is **not** `Basic.parabolaAntideriv`, which is for `y = x²`; L2 must add
it.]

The endpoint abscissa is

```
e = X(w) = w(1 − d/√(1+w²)) .                                              (5.2)
```

**The quartic.**  From (5.2),

```
e = w − wd/s   ⇔   s(w − e) = wd   (for s > 0) ,
```

and squaring is legitimate as an **implication** in every sign case: for `d > 0` both
sides of `s(w − e) = wd` are nonnegative, for `d < 0` both are nonpositive, and for
`d = 0` both are zero.  (We only use "original equation ⟹ quartic"; the converse fails
by the extraneous roots discussed below.)  This gives

```
(1 + w²)(w − e)² = w²d² ,
```

i.e.

```
w⁴ − 2e w³ + (1 + e² − d²) w² − 2e w + e² = 0 .                            (5.3)
```

[Wolfram: the residual of (5.3) on substituting `e = w(1 − d/√(1+w²))` is exactly `0`;
numeric checks at `d = 1/2, e = 1` give roots `{−0.0590…, 0.7104…, 1.4076…}` with the
valid one `1.4076…`.]

**Which root.**  For `d < 1` and `w ≥ 0`, `e(w) = w(1 − d/s)` is strictly increasing,
because

```
e'(w) = 1 − d/s³ ≥ 1 − d > 0 ,
```

so (5.2) has at most one solution `w ≥ 0` for each `e ≥ 0`, and it has one for every
`e ≥ 0` (as `w → ∞`, `e → ∞`).  The sign of `e − w` is the sign of `−d` (since
`e − w = −wd/s`), so:

* `d > 0`: the valid root has `0 ≤ e < w`;
* `d < 0`: the valid root has `0 ≤ w < e`;
* `d = 0`: `w = e` (and (5.3) becomes `(1+w²)(w−e)² = 0`).

Squaring introduced the roots on the **other** side of `e`, satisfying `s(e − w) = wd`;
they are extraneous.  Hence the valid root is the unique root of (5.3) on the side of
`e` determined by `sign(d)`: for `d > 0` the unique root in `(e, ∞)`, for `d < 0` the
unique root in `[0, e)`, and for `d = 0` the double root `w = e`.
[Proof of uniqueness from strict monotonicity of `e(w)`; the root-selection statement is
not needed for P-constructibility, only for identifying the root.]

**Why a quartic is enough for L2.**  `box_xmax` gives `e` directly, hence `e` is
P-constructible.  The coefficients `1`, `−2e`, `1 + e² − d²`, `−2e`, `e²` of (5.3) are
then P-constructible (`pconstructible`), the leading coefficient is `1 ≠ 0`, and the
degree is `4 ≤ 6`.  So `root_Pconstructible_le_six_coeffs` gives `w`
P-constructible.  This is the entire algebraic content of the headline theorem.

**The equation in `w`.**  Also, with `Φ(w) = R(w) − d·arctan w`,

```
Φ'(w) = √(1+w²) − d/(1+w²) = (s³ − d)/s² ,
```

which is `> 0` for `d < 1` (since `s ≥ 1 > d`).  So `Φ` is a strictly increasing
bijection `[0,∞) → [0,∞)`, and the given `x ≥ 0` determines `w` uniquely by
`Φ(w) = x`.  [Proof; this is the uniqueness half of the headline.]

[Wolfram: `∫_0^w (√(1+u²) − d/(1+u²))du = R(w) − d·arctan w` at 50-digit working
precision, residual `0` to 40–50 digits for `(d,w) = (1/2,7/10), (−3,3), (9/10,2)`.]

---

## 6. Q5 — the statement for L1/L2

### 6.1 `ψ`: `Real.arctan` versus `Complex.arg`

Choose **`ψ = Real.arctan (y'/x')`** on a window with `x' ≠ 0` (constant sign).  Then

```
ψ' = (x'y'' − y'x'')/(x'² + y'²) = κ·s
```

by the quotient rule, `Real.arctan` has no branch cut, and on the parabola `x' = 1`
so `ψ = Real.arctan w` globally on `[0,∞)`.  This is the choice I recommend for L1/L2.
`Complex.arg` is needed only if the window crosses a vertical tangent (`x' = 0`), where
`arctan (y'/x')` blows up; for the parabola and for any window with `x' > 0` it is
unnecessary.  If a general statement is wanted, use `Complex.arg ∘ γ'` with a
continuity/branch hypothesis on the window; that is more work for no gain in the
parabola case.  **[Proof that arctan works on `x' ≠ 0`; the `Complex.arg` alternative is
[Open] as a formalization cost, not as mathematics.]**

### 6.2 L1's speed and arc-length lemmas

```lean
namespace Pconstructible

/-- The signed curvature `κ = (x'y'' − y'x'') / speed³`, counterclockwise positive. -/
noncomputable def curvature (γ : ℝ → ℝ × ℝ) (t : ℝ) : ℝ :=
  (deriv (fun s => (γ s).1) t * deriv (deriv (fun s => (γ s).2)) t
    - deriv (fun s => (γ s).2) t * deriv (deriv (fun s => (γ s).1)) t) / speed γ t ^ 3

-- Theorem: the offset velocity is `(1 - d κ)` times the base velocity.
theorem deriv_offsetParam {γ : ℝ → ℝ × ℝ} {d t : ℝ}
    (hx : DifferentiableAt ℝ (fun s => (γ s).1) t)
    (hy : DifferentiableAt ℝ (fun s => (γ s).2) t)
    (hx' : DifferentiableAt ℝ (deriv (fun s => (γ s).1)) t)
    (hy' : DifferentiableAt ℝ (deriv (fun s => (γ s).2)) t)
    (hreg : speed γ t ≠ 0) :
    deriv (fun s => (offsetParam γ d s).1) t
        = (1 - d * curvature γ t) * deriv (fun s => (γ s).1) t ∧
      deriv (fun s => (offsetParam γ d s).2) t
        = (1 - d * curvature γ t) * deriv (fun s => (γ s).2) t

-- Theorem: the speed identity for the offset.
theorem speed_offsetParam {γ : ℝ → ℝ × ℝ} {d t : ℝ}
    (hx : DifferentiableAt ℝ (fun s => (γ s).1) t)
    (hy : DifferentiableAt ℝ (fun s => (γ s).2) t)
    (hx' : DifferentiableAt ℝ (deriv (fun s => (γ s).1)) t)
    (hy' : DifferentiableAt ℝ (deriv (fun s => (γ s).2)) t)
    (hreg : speed γ t ≠ 0) :
    speed (offsetParam γ d) t = |1 - d * curvature γ t| * speed γ t

-- Theorem: on a cusp-free window the offset arc length is `Δs - d Δψ`.
theorem arcLengthOf_offsetParam {γ : ℝ → ℝ × ℝ} {ψ : ℝ → ℝ} {a b d : ℝ}
    (hab : a ≤ b)
    (hdiff : ∀ t ∈ Set.Icc a b,
      DifferentiableAt ℝ (fun s => (γ s).1) t ∧
      DifferentiableAt ℝ (fun s => (γ s).2) t)
    (hreg : ∀ t ∈ Set.Icc a b, speed γ t ≠ 0)
    (hC2 : ∀ t ∈ Set.Icc a b,
      DifferentiableAt ℝ (deriv (fun s => (γ s).1)) t ∧
      DifferentiableAt ℝ (deriv (fun s => (γ s).2)) t)
    (hpos : ∀ t ∈ Set.Icc a b, 0 < 1 - d * curvature γ t)
    (hψ : ∀ t ∈ Set.Icc a b, HasDerivAt ψ (curvature γ t * speed γ t) t)
    (hint : IntervalIntegrable (speed γ) MeasureTheory.volume a b)
    (hintψ : IntervalIntegrable (fun t => curvature γ t * speed γ t)
      MeasureTheory.volume a b) :
    arcLengthOf (offsetParam γ d) a b = arcLengthOf γ a b - d * (ψ b - ψ a)

end Pconstructible
```

### 6.3 The general offset-inversion theorem

This is the theorem schema R0 hands to L1/L2.  It is deliberately in `Defs` vocabulary:
the hypotheses are exactly the `offset` constructor's plus the C²/tangent-angle data
needed for the speed identity, plus `hinj`/`hlen` for `arc_of_length`, plus the
monotonicity needed by the box.

```lean
-- Theorem: (offset inversion, general form) Let `γ` trace a regular C² arc of a
-- P-constructible curve over `[a,b]`, with `ψ` a tangent angle (`ψ' = κ · speed γ`).
-- Suppose `1 - d κ > 0` on the window, the offset tracing is injective there, and the
-- arc laid along the offset from `a` has P-constructible length `x`.  Then
--   1. the offset arc length is `∫ speed γ - d (ψ b - ψ a)`, and
--   2. whenever the offset's abscissa is monotone on `[a,b]`, the far endpoint's
--      abscissa is P-constructible (and similarly for the ordinate).
theorem offsetArc_endpoint_Pconstructible
    {S : Set (ℝ × ℝ)} (hS : PConstructibleCurve S)
    (γ : ℝ → ℝ × ℝ) (ψ : ℝ → ℝ) {a b d x : ℝ}
    (hab : a < b) (hd : PConstructible d) (hx : PConstructible x)
    -- the tracing is the whole base curve, not a sub-arc
    (himg : γ '' Set.Icc a b = S)
    (hinj : Set.InjOn γ (Set.Ico a b))
    (hseam : γ b = γ a → unitNormal γ b = unitNormal γ a)
    (hdiff : ∀ t ∈ Set.Icc a b,
      DifferentiableAt ℝ (fun s => (γ s).1) t ∧
      DifferentiableAt ℝ (fun s => (γ s).2) t)
    (hreg : ∀ t ∈ Set.Icc a b, speed γ t ≠ 0)
    (hC1 : ContinuousOn (deriv (fun s => (γ s).1)) (Set.Icc a b) ∧
      ContinuousOn (deriv (fun s => (γ s).2)) (Set.Icc a b))
    (hC2 : ∀ t ∈ Set.Icc a b,
      DifferentiableAt ℝ (deriv (fun s => (γ s).1)) t ∧
      DifferentiableAt ℝ (deriv (fun s => (γ s).2)) t)
    (hpos : ∀ t ∈ Set.Icc a b, 0 < 1 - d * curvature γ t)
    (hψ : ∀ t ∈ Set.Icc a b, HasDerivAt ψ (curvature γ t * speed γ t) t)
    (hinj_off : Set.InjOn (offsetParam γ d) (Set.Icc a b))
    (hint_off : IntervalIntegrable (speed (offsetParam γ d))
      MeasureTheory.volume a b)
    (hx₀ : PConstructible (offsetParam γ d a).1)
    (hy₀ : PConstructible (offsetParam γ d a).2)
    (hlen : arcLengthOf (offsetParam γ d) a b = x)
    (hmono : MonotoneOn (fun t => (offsetParam γ d t).1) (Set.Icc a b) ∨
      AntitoneOn (fun t => (offsetParam γ d t).1) (Set.Icc a b)) :
    PConstructible (offsetParam γ d b).1 := by
  -- 1. `PConstructibleCurve.offset` on the whole base curve (`himg`) gives
  --    `hP : PConstructibleCurve (P_d '' Icc a b)`. This is the only legal order: the
  --    base curve is offset whole, then the arc is laid on the offset curve.
  -- 2. `PConstructibleCurve.arc_of_length` with `S := P_d '' Icc a b`, `hsub := subset_rfl`,
  --    `hinj := hinj_off`, `hdiff := differentiableAt_offsetParam`, etc., gives the same set.
  -- 3. `Box.arc_xendpoint_Pconstructible` with `continuousOn_offsetParam` and `hmono`
  --    returns the endpoint's abscissa.
  sorry
```

The `sorry` is a placeholder for the proof, not for the note; the note's job is the
statement and the lemma list.  The corresponding `..._y` version replaces `Prod.fst` by
`Prod.snd` and `box_xmax` by `box_ymax`.

**Equation form.**  Combining `arcLengthOf_offsetParam` with `hlen` gives the
always-meaningful statement

```
arcLengthOf γ a b − d·(ψ b − ψ a) = x .                                    (6.1)
```

If the base is parametrized by its tangent angle on the window (i.e. `ψ` is injective,
e.g. `κ ≠ 0` throughout), write `R(ψ) := ∫ s` for the Whewell function; then
`arcLengthOf γ a b = R(ψ b) − R(ψ a)` and (6.1) becomes

```
R(ψ b) − d·ψ b = x + (R(ψ a) − d·ψ a) .                                    (6.2)
```

If the start is chosen so that `R(ψ a) − d·ψ a = 0` (the parabola vertex does this),
(6.2) is exactly the source note's `R(ψ) − dψ = x`.  When `κ` changes sign on the window
`R` is not a single-valued function of `ψ`; use the `arcLengthOf` form (6.1) there.

### 6.4 L2's parabola specialization

```lean
-- Theorem: (parabola offset inversion) For P-constructible `d < 1`, `x ≥ 0`, the
-- parameter `w ≥ 0` of the offset of `y = x^2 / 2` whose arc length from the vertex
-- image `(0,d)` is `x` is P-constructible.
theorem parabola_offset_root_Pconstructible {d x w : ℝ}
    (hd : PConstructible d) (hx : PConstructible x) (hd1 : d < 1)
    (hw : 0 ≤ w)
    (hweq : (w * Real.sqrt (1 + w ^ 2) + Real.arsinh w) / 2
      - d * Real.arctan w = x) :
    PConstructible w := by
  sorry
```

Sketch of the Lean route (the one L2 should follow):

1. `hpar : PConstructibleCurve {p | p.2 = (1/2) * p.1 ^ 2}` by `poly_graph` with
   `p = Polynomial.C (1/2) * X^2`.
2. On `[0,w]`, `γ(t) = (t, t²/2)` is injective (`x' = 1`), regular (`s ≥ 1`), C².
3. `hP : PConstructibleCurve (offsetParam γ d '' Icc 0 w)` by
   `PConstructibleCurve.offset` (or the pattern of
   `offsetCubicPairArc_PConstructibleCurve`).
4. `A : PConstructibleCurve (offsetParam γ d '' Icc 0 w)` by `arc_of_length` with
   `hinj_off` from `X' = 1 − d/s³ > 0`, `hlen` from `hweq` and the closed-form arc
   length, `hx₀,hy₀` from `(0,d)`.
5. `e : PConstructible (offsetParam γ d w).1` by
   `Box.arc_xendpoint_Pconstructible` (monotone `X`).
6. `hq : e = w(1 − d/√(1+w²))` and hence the quartic (5.3) with `e` in place of the
   variable.  Coefficients are `pconstructible`; apply
   `root_Pconstructible_le_six_coeffs`.
7. Conclude `PConstructible w`.

The uniqueness half of the headline ("the unique `w`") is `Φ` strictly increasing
(§5.3), and can be a separate corollary if not needed for the P-constructibility.

---

## 7. Consequences for L1/L2

### 7.1 Already formalized (reuse directly)

| Lemma | File / line | What it gives |
|---|---|---|
| `continuousOn_offsetParam` | `BoxOffset.lean:69` | `ContinuousOn (offsetParam γ d) (Icc u v)` from `hdiff`, `hreg`, `hC1` (C¹ is enough) |
| `offsetArc_box_xmax_Pconstructible` | `BoxOffset.lean:96` | box right edge of an offset arc, given `PConstructibleCurve` + `ContinuousOn` |
| `offsetArc_box_xmin/ymax/ymin_Pconstructible` | `BoxOffset.lean:106,115,125` | the other three edges |
| `offsetArc_box_xmax_of_offsetHyp` | `BoxOffset.lean:143` | the right edge straight from `offset`'s hypothesis list |
| `isCompact_traced_arc` | `Box.lean:188` | `IsCompact (γ '' Icc a b)` from pointwise `hdiff` |
| `nonempty_traced_arc` | `Box.lean:202` | `Nonempty (γ '' Icc a b)` from `a ≤ b` |
| `arc_xendpoint_Pconstructible` / `arc_xendpoint_antitone_Pconstructible` | `Box.lean:325,362` | monotone/antitone coordinate ⟹ endpoint coordinate P-constructible |
| `arc_yendpoint_Pconstructible` / `..._antitone` | `Box.lean:344,381` | the ordinate versions |
| `arcLength_inverse_Pconstructible` | `Box.lean:452` | both endpoint coordinates from a laid arc + monotonicity |
| `arcLength_xendpoint_Pconstructible` / `..._yendpoint` | `Box.lean:477,495` | single-coordinate versions, hypotheses exactly `arc_of_length`'s |
| `isCompact_restrict_of_isClosed` + `isClosed_poly_graph` | `Box.lean:235,248` | compactness for a `restrict`ed polynomial graph |
| `speed_parabolaParam`, `arcLengthOf_parabolaParam` | `Basic.lean:1788,1832` | parabola `y = x²` speed and arc length (**not** `y = x²/2`) |
| `parabolaAntideriv`, `parabolaAntideriv_Pconstructible` | `Basic.lean:1801,1870` | antiderivative `∫√(1+4t²)` and its P-constructibility |
| `parabola_PConstructibleCurve`, `parabolaArc_Pconstructible` | `Basic.lean:1842,1847` | parabola as a constructible curve and arc length |
| `sqrt_Pconstructible` | `Basic.lean:215` | `√x` P-constructible for P-constructible `x`, no sign hypothesis |
| `arctan_Pconstructible`, `arcsin_Pconstructible`, `arccos_Pconstructible` | `Basic.lean:2850,2839,2824` | the inverse trig values |
| `cos_sin_Pconstructible`, `cos_Pconstructible`, `sin_Pconstructible` | `Basic.lean:2633,2652,2657` | trig of P-constructible angles |
| `root_Pconstructible_le_six_coeffs` | `Basic.lean:1375` | any real root of a degree-≤6 polynomial with P-constructible coefficients |
| `pconstructible` tactic | `Tactic.lean:122` | discharges arithmetic P-constructibility goals |
| `offsetParam_zero`, `unitNormal_orthogonal`, `offsetParam_normal_eq_zero`, `offsetParam_dist_sq` | `Offset.lean:102,108,118,127` | the generic offset identities (no differentiability hypotheses) |
| `offsetCubicPairArc_PConstructibleCurve` | `Offset.lean:275` | a worked example of discharging every `offset` hypothesis |

### 7.2 Missing (L1 must add)

1. **`curvature`** — there is no curvature definition anywhere in the project.
2. **`deriv_speed`** — `s' = (x'x'' + y'y'')/s` for `s ≠ 0`.
3. **`deriv_unitNormal`** — `n' = −κs·T`, or directly the component formula.
4. **`deriv_offsetParam`** — the component identity (2.1).
5. **`speed_offsetParam`** — the identity (2.2), with `|·|`.
6. **`differentiableAt_offsetParam`** — `P_d` differentiable at `t` from `hreg` and C²
   at `t` (needed because `arc_of_length`'s `hdiff` is about `P_d`, and `offset`'s
   `hC1` only gives continuity of `P_d`, not differentiability).
7. **`continuousOn_speed_offsetParam`** (or at least interval integrability of
   `speed (offsetParam γ d)`) from continuous second derivatives.
8. **`arcLengthOf_offsetParam`** — the formula with `ψ b − ψ a`.
9. **`hasDerivAt_arctan_slope`** — `ψ = arctan (y'/x')` has `ψ' = κs` on `x' ≠ 0`.
10. **Monotonicity lemmas** — `MonotoneOn (fun t => (P_d t).1)` from
    `0 ≤ (1 − dκ)·x'` on the window (and the `y`/antitone variants).
11. For L2 only: the parabola-`y=x²/2` speed/antiderivative (`s = √(1+w²)`,
    `R = (w√(1+w²)+arsinh w)/2`), and the quartic coefficient computation.

### 7.3 Smallest set L1 must prove before R0's conclusion is statable

In dependency order:

1. `curvature` (definition only).
2. `deriv_speed` and `deriv_unitNormal` (or `deriv_offsetParam` directly).
3. `speed_offsetParam` (from 2).
4. `differentiableAt_offsetParam` and `continuousOn_speed_offsetParam` (from 2 + C²).
5. `arcLengthOf_offsetParam` (from 3, 4, `ψ' = κs`, FTC and interval-integral
   linearity).

With those five, L2 can state step 4 of its route (`arc_of_length` on the offset arc
with `hlen`) and step 5 (`box_xmax`), and the quartic in step 6 is pure algebra on top
of `root_Pconstructible_le_six_coeffs`.

### 7.4 Hypothesis mismatch to report to the orchestrator

`offset` needs only **C¹** (`hC1` continuity of velocity), while the speed identity and
`arcLengthOf_offsetParam` need **C²** (pointwise differentiability of the velocity, and
continuity of the second derivative for integrability).  The constructible-curve side of
the argument therefore remains C¹, but L1's analytic lemmas must carry the extra C²
hypothesis.  This is not a defect in `Defs.lean`; it is the price of differentiating
`unitNormal`, and it should be stated explicitly rather than hidden.

---

## 8. Open items

* **[Open] Junk case in Lean.**  The pointwise identity at `speed γ t = 0` (§2.4) is
  true but needs a proof that `unitNormal` is discontinuous at an isolated zero of
  `speed`.  Not needed for L1/L2; recommended to omit.
* **[Open] Cusp P-constructibility for general curves.**  §4 shows it for the parabola
  (degree 6).  For a general `poly_graph` curve, `κ(t) = 1/d` is a polynomial equation
  in `t` only after clearing `speed³`; its degree can exceed 6, and `ψ(t₀)` must also be
  P-constructible.  Curve-by-curve.
* **[Open] Uniform intersection route.**  §5.2(3) is only a heuristic; no uniform second
  curve is known for isolating an offset endpoint when the arc is not monotone.
* **[Open] `Complex.arg` formulation.**  Needed only for windows crossing a vertical
  tangent; not for the parabola.  The branch-cut bookkeeping is a formalization cost,
  not a mathematical obstruction.
* **[Open] The "doubling" claim.**  §3.4 shows crossing a cusp keeps the same equation
  family with a shifted RHS.  Whether some *other* use of the cusp doubles the family
  (e.g. laying from the cusp in both directions and combining the two lengths to
  eliminate `R(ψ_c)`) is not settled here; the algebra of (3.2) suggests the cusp
  constant is fixed, so I expect **no** new family, but that is [Heuristic].
