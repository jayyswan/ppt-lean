# M: which curves would the PowerPoint UI have to draw, and what does each unlock?

Stream M of `pptc/PLAN-ppt-tan-curves.md`. Pure mathematics, no PowerPoint. No Lean edits, no
`Defs.lean` change. Every identity and number below was computed with the **Wolfram Language**
evaluator (45-digit working precision unless stated); Python was not used. Labels: **[Proof]**
(argument written out here), **[Wolfram]** (checked to >= 30 digits or exactly), **[Heuristic]**,
**[Open]**.

> **Lean reachability caveat (2026-11-03).** The offset-inversion rows below are geometric
> statements. In Lean they are reachable only by the **whole-arc route**: first apply
> `offset` to the whole drawn curve (nondegenerate window, smooth seam if closed), then
> lay the arc of known length on the resulting offset curve with `arc_of_length`, then
> read its endpoint with `box_xmax` / `box_ymax`. Offsetting a sub-arc directly, or
> offsetting a singleton window (`a = b`), is not allowed. The old L2 parabola proof used
> a sub-arc and was vacuous; it has been replaced by the whole-arc proof. See
> `notes/offset-inversion/DEFECT-defs-soundness.md`.

## Findings summary

1. **All eight wishlist rows survive**, with three sharpenings. The spiral correction stands:
   the spiral box gives `θ tan(θ − β) = 1`, never `tan x = x`. Exactly, it gives the families
   `tan y + y = k` (every P-constructible `k`) and `(x + β) tan x = 1` (every `β`), so it
   includes `tan x = −x` and `x tan x = 1`.
2. **New structural fact [Proof + Wolfram]: the quartic `y = x/√(1+x²)` is stronger than the
   wishlist says.** Meeting the sine *and the cosine* with its affine images gives
   `tan x = λx + μ` **and** `(λx + μ) tan x = 1` for all P-constructible `λ, μ`. That covers
   `tan x = λx`, the gear involute `tan α − α = k`, **and every Robin/Biot eigenvalue
   `x tan x = Bi`** (slab, and sphere via `1 − x cot x = Bi`). It is the single best curve for
   the "tan family"; it does not reach the beams or the goat.
3. **`tanh`/logistic does more than the cantilever [Proof + Wolfram].** Because
   `sin(λu+μ) = tanh u ⇔ λu + μ = ± gd u (+ multiples of π)`, one intersection with a *free*
   sine gives the whole log-cosine offset-inversion class `λu − gd u = c` for all `λ, c`:
   both beam families, the rhumb line, the separatrix. No offset inversion is needed.
4. **Tangent-from-a-point is the hidden mechanism [Proof + Wolfram].** The box of a
   *projective* image of a curve is a tangent line from a fixed point to the original curve.
   For the sine, the tangent-from-`(p,q)` equation is `sin y − (y+φ) cos y = c`. This is the
   same two-parameter family as the circle involute's intersections with lines; it contains
   `tan x = x + μ` and the **goat problem** (`c = π/2`). So the involute and "box of a
   perspective image of the sine" are one route. It is the *only* route to the goat that
   needs no pole-crossing offset inversion.
5. **Correction to R5 [Wolfram].** Row 15 (finite spherical well, `l = 0`) is **reachable
   now**: `tan x = −x/√(R²−x²)` is `sin x = x/R` in a window where `cos x < 0` (line meets
   sine). Row 16 (`x tan x = Bi`) is reachable via the quartic (finding 2), not "outside".
6. **Cycloids/trochoids and the logarithmic spiral give no new numbers** with the current
   constructors: their line intersections and offset inversions fall back into Kepler and
   exp-meets-sine classes. A Gröbner computation shows `tan t = t` is *not* a conic section of
   any affine trochoid image. Chart curves `p(2^x)`, `a·exp(k·2^x)` reduce, for lines, to
   poly-meets-log and log-meets-exp; nothing named.
7. **Feasibility versus payoff are inversely ordered.** The Archimedean spiral is the only
   curve with a plausible UI route (text warp, P1/P2) but unlocks the smallest family. The
   quartic and catenary have no known route. Perspective/projective images of curves
   (3-D, shadows) would unlock the tangent-from-a-point family but are currently raster-only.

### Ranked table

| rank | curve | unlocks (new, beyond current constructors) | needs | exactness |
|---|---|---|---|---|
| 1 | quartic `y = x/√(1+x²)` (any affine image, either sign) | `tan x = λx+μ`; `(λx+μ)tan x = 1`; so j₁ zeros, single-slit maxima, clamped-hinged beam, gear `inv α = k`, **all `x tan x = Bi`**, `tan y + y = k` | no known route (P5 only; P3 unlikely) | (a) |
| 2 | `tanh` / logistic | `sin(λu+μ) = tanh u`: cantilever + clamped–clamped beams, rhumb, whole `λu − gd u = c` | P3 (no trendline gives it) | (a) |
| 3 | catenary | `tan x = λx+μ` (via offset inversion), catenary span/sag; not `x tan x = Bi` | P3/P4 (none known) | (a) |
| 4 | circle involute **or** perspective image of sine (box) | `sin y − (y+φ)cos y = c`: `tan x = x+μ`, gear `inv`, **goat**, single-slit maxima; not `λ ≠ 1` | P5 (3-D/shadow vector read-out); involute: none | (a) |
| 5 | `ln sec x` | beam/rhumb class via offset inversion only (weaker than rank 2) | P3 (none known) | (a) |
| 6 | **Archimedean spiral** | `tan y + y = k`, `(x+β)tan x = 1`: `tan x = −x`, slab `x tan x = 1` | **P1 + P2 (text warp)** | (a) for warp+read-out; (b) only if user accepts |
| 7 | power spirals `r = θ^b` (`b ∈ ℚ`) | `x tan x = b`, `θ tan(θ−β) = b` | glyph curve, P1 (not exact for glyph Béziers) | (a) |
| 8 | trochoid / cycloid | Kepler class only; no new named numbers | P4 | (a) |
| 9 | logarithmic spiral | nothing (reducible) | P1 on `exp` curve | – |
| 10 | chart `p(2^x)`, `a·exp(k·2^x)` | double exponential; nothing named | P3 | (a) |

Rows 3 and 5 use offset inversion, as do the offset-inversion entries in §3. In Lean they
are reachable only by the whole-arc route stated above; the older sub-arc formalisation
route is closed.

## 1. Wishlist rows, confirmed or corrected

Throughout, "P-constructible `k`" uses `sin_Pconstructible`, `cos_Pconstructible`,
`tan_Pconstructible`, `log_Pconstructible` (all in `Basic.lean`); `restrict` windows isolate one
root so `inter_x` sees a single point.

| Curve | Verdict | Evidence |
|---|---|---|
| Archimedean spiral | **confirmed, with the exact family stated** | below |
| circle involute | confirmed | below |
| catenary | confirmed | below |
| `tanh`/logistic | confirmed, enlarged | below |
| `ln sec x` | confirmed | below |
| quartic | confirmed, **enlarged** | below |
| cycloid / trochoid | **[Open] settled to "Kepler class only" for lines; conics partly** | §3.7 |
| logarithmic spiral | **settled: nothing new** | §3.8 |

### 1.1 Archimedean spiral `r = aθ`

`ℓ·γ(θ) = aθ cos(θ−β)` for a box direction `ℓ = (cos β, sin β)` (any affine image of the
spiral only changes `ℓ`, since `ℓ·(Mγ) = (Mᵀℓ)·γ`). Stationary: `cos(θ−β) − θ sin(θ−β) = 0`,
that is **`θ tan(θ − β) = 1`** [Proof]. Value at the maximum: `aθ²/√(1+θ²)`, so `θ` is recovered
algebraically from the box value `V` (`θ⁴ − V²θ² − V² = 0`, `a = 1`).

[Wolfram, 45 digits]
- `β = π/2`: `tan x = −x`, root `2.02875783811043422357697112473471437610838` (the spiral stationary
  point agrees to 44 digits). Here the stationary angle is `θ = x` itself, not `x + π/2`. The
  roots `2.0288, 4.9132, 7.9787, 11.0855` all lie below `4π` (correction from
  `notes/spiral/F2.md` §7).
- **Box condition** (`notes/spiral/F2.md` §6): the stationary `θ` must be the *global* extremum
  of the drawn arc in direction `ℓ`, so the arc's window has to end early enough. For example,
  the full `◢` window `[2π, 4π]` serves only `θ ≥ 7.3688`.
- `β = 0`: `x tan x = 1`, root `0.86033358901937976248389342413766233341188`.
- `tan y + y = 3`: `y = 1.08874792349856086933952529998718230126358`, with `β = k − π/2`,
  `θ = k − y = tan y`; `NMaximize` of `θ cos(θ−β)` agrees with the closed form
  `θ²/√(1+θ²) = 1.69345946020889479055425186098` to 14 digits (30-digit optimizer), and the
  closed form agrees with the point value to 44 digits.

**Exact statement of the plan's second claim.** With `x = θ − β`: `(x + β) tan x = 1`, i.e.
`cot x = x + β`. Setting `x = π/2 − y` and `k = β + π/2`: **`tan y + y = k`**. The direction
`ℓ` needs `tan β = −cot k`, P-constructible, so the family is uniform in `k`.
`tan x = x` is **not** in the family (it would need `β` to depend on the root). [Proof]

Box of the *offset* spiral adds nothing: `P_d' = (1 − dκ)γ'`, so stationary points are the same
`θ` or the algebraic cusp roots `κ = 1/d`, `κ = (θ²+2)/(1+θ²)^{3/2}`. [Proof]

### 1.2 Circle involute `I(θ) = (cos θ + θ sin θ, sin θ − θ cos θ)`

`I = e^{iθ}(1 − iθ)`: radius `√(1+θ²)`, argument `θ − arctan θ`. [Wolfram, residual 0]
- crosses `y = 0` at `tan θ = θ`: `4.49340945790906417530788092728032208`;
- crosses `y = π/2` at the goat: `β = 1.90569572930988389488266643716`;
- crosses the line through the origin of angle `k` where `θ − arctan θ = k`; with
  `θ = tan α` this is `tan α − α = k`: `k = 3/10` gives `α = 0.858844142240183196758295238687`
  rad `= 49.2081446098958471330129514194°`. **So the involute also gives the gear involute
  function by a line through the origin**, a use not in the wishlist.
- general line `ℓ·I = c`, `ℓ = (cos p, sin p)`: `cos(θ−p) + θ sin(θ−p) = c`
  [Wolfram, symbolic 0]. This is `sin y − (y + φ)cos y = c`: the **family E**.

Arc length of the involute is `θ²/2` (polynomial); its offsets are *rotations* of itself,
`I + dν = e^{id} I(θ − d)` [Proof], so offset inversion collapses to a quadratic.

### 1.3 Catenary
Offset arc `= tan ψ − dψ`. [Wolfram, `y = cosh x`, `d = 2/5`, `x ∈ [0, 11/10]`, numerical
`∫|1 − dκ|·speed` versus formula: residual `0` to 40 digits.] Hence `tan ψ = dψ + x`: all
`tan x = λx + μ`.

### 1.4 `tanh` / logistic
[Wolfram, 40 digits] `sin x = tanh x` has `1.87510406871196116644530824108`,
`7.85320462409583755647706668725`, `14.1371654912574641771059178551`; `sin x = −tanh x` has
`4.69409113297417457643639177802`, `10.9956078380016709066690325191`. These are the beam roots,
because `cos²x cosh²x = 1 ⇔ sin²x = tanh²x`: the union of the cantilever
(`cos x cosh x = −1`: `1.8751, 4.6941, 7.8548, 10.9955`) and clamped–clamped
(`= +1`: `4.7300, 7.8532, 10.9956`) spectra. Windows and the sign of `scale_y` select the
branch. **Enlargement:** `sin(λu + μ) = tanh u ⇔ λu + μ = gd u + 2πm` or `π − gd u + 2πm`
[Proof], so with a free sine (frequency, phase) *every* `λu − gd u = c` and `λu + gd u = c`.
Example [Wolfram]: rhumb `u − 2 gd u = 0`: `sin(u/2) = tanh u` has `u = 2.92772127705614224296270`,
`gd u = 1.46386063852807112148135004`, the R5 rhumb angle `83.873…°`.

### 1.5 `ln sec x`
Offset arc `= gd⁻¹ψ − dψ` (R5, re-verified: `∫|1 − d cos x| sec x` equals
`asinh(tan X) − dX`, `d = −3/5`, residual 0 to 39 digits). Also meets lines in a reachable
way: `−ln cos t = αt + β ⇔ cos t = 2^{…}`, sine meets `exp_two`.

### 1.6 Quartic `Q: y = x/√(1+x²)`
Write `w = λt + μ`. `sin t = ε w/√(1+w²)` gives `w = ± tan t` (sign of `cos t`), so
**`tan t = λt + μ`** for all constructible `λ, μ` (`ε = sign cos t` chosen by window and
`scale_y(−1)`). [Wolfram, 45 digits: `(λ, μ) = (1,0), (1/2,0), (1,−1/3), (3,2/7), (−2,1)`;
residuals ≤ 1e−43, with the sign `ε = −1` needed where `cos t < 0`.]

**Cosine version (new):** `cos t = ε w/√(1+w²)` gives `cot t = ± w`, i.e.
**`(λt + μ) tan t = 1`**. With `λ = 1/Bi, μ = 0`: **`x tan x = Bi`** for every `Bi`.
[Wolfram: `x tan x = 2`, `x = 1.07687398631180365860859767305`, `cos x − x/√(x²+4) = 0` to 44
digits; `tan y + y = 3` as `sin y = w/√(1+w²)`, `w = 3 − y`, residual 0;
`(3t/2 − 1/5) tan t = 1`, `t = 0.791678444356156367037402307217`, residual 0.]

The spiral families are subfamilies (`λ = 1`, `μ = β` for `(x+β)tan x = 1`; `λ = −1` for
`tan y + y = k`). Q also reaches `tan x = x` itself.

## 2. Equation-class dictionary

| id | family | named problems |
|---|---|---|
| T1 | `tan x = λx + μ` | j₁ zeros, single-slit maxima (`4.4934, 7.7253, …`), clamped–hinged beam, gear `inv α = k`, spherical well `l = 1` |
| T2 | `(λx+μ) tan x = 1` | Robin slab `x tan x = Bi`, sphere `1 − x cot x = Bi` |
| T3 | `tan y + y = k` | `tan x = −x`, extremum of `x sin x` |
| T4 | `sin x = ±tanh x`, `λu ∓ gd u = c` | cantilever, clamped–clamped beams, rhumb line, pendulum separatrix |
| T5 | `sin y − (y+φ)cos y = c` | goat, sinc maxima, `tan x = x + μ`, gear `inv` (c = 0) |
| T6 | `θ tan(θ−β) = b`, `b ∈ ℚ` | `x tan x = b` (power spirals) |

## 3. Everything each curve unlocks (against every base operation)

Legend: **R** = already reachable class; **N** = new class, named problem listed; **E** =
elementary/algebraic (adds nothing transcendental); **?** = new class, unnamed.

### 3.1 Archimedean spiral `γ = θ e^{iθ}`
| operation | result |
|---|---|
| line | `θ sin(θ−β) = c` : hyperbola `xy = c` meets shifted sine, **R** |
| circle/ellipse centred anywhere | conic in `(θ, cos(θ−β))` for a circle; general conic mixes harmonics 1 and 2 with `θ²`: **?** [Heuristic] |
| poly graph, power law, Bézier | `P(θ cos θ, θ sin θ) = 0`: polynomial in `θ, cos θ, sin θ`: **?** (two trig functions at once, outside `sheared-sine-intersections.md` §1) |
| `exp_two`, `sine` | **?** |
| box | T3 / T2-subfamily (**N**) |
| arc length | `½(θ√(1+θ²) + asinh θ)` = parabola arc length: **R** (`log_Pconstructible`) |
| `arc_of_length` + `box` | `θ` equals the parabola slope `w(L)`, already constructible; trig of it is reachable: **R** |
| offset | stationary points unchanged (§1.1): **E** |
| offset inversion | `R − dψ = x` with `R = ½(θ√(1+θ²)+asinh θ)`, `ψ = θ + arctan θ`, i.e. `θ = sinh u`: `½(sinh u cosh u + u) − d(sinh u + gd u) = x`. [Wolfram: formula vs numerical integral of `|1−dκ|` speed, `d = 1/5`, residual 0, 40 digits.] An `u` + `gd u` class with a `sinh u` term; **?**, unnamed |

### 3.2 Circle involute
Intersections with lines: T5 (**N**). Box: `x' = θ cos θ`, trivial `θ = π/2 + kπ − β` (**E**).
Arc length `θ²/2`: so `arc_of_length` from a point lays `θ = √(θ₀² + 2x)` (**E**). Offset:
rotation (**E**). Meeting a circle: `θ` algebraic (**E**). Meeting `sine`, `exp_two`, poly:
`sin θ − θ cos θ`-type with mixed `θ`: **?**.

### 3.3 Catenary `(t, cosh t)`
| operation | result |
|---|---|
| line | `cosh t = αt + β`: the **catenary of given span and sag** (`cosh s − 1 = (h/b)s`, `s = b/a`) **N**; classical, previously not in R5 |
| `exp_two` | polynomial in `e^{t}, e^{−t}`: **E**/**?** |
| `sine` | `cosh t = sin(…)`: **?** |
| box | `ℓ₁ + ℓ₂ sinh t = 0`: **E** |
| arc length | `sinh`: **E** |
| offset inversion | `tan ψ − dψ = x`: T1 (**N**) |

### 3.4 `tanh`/logistic
| operation | result |
|---|---|
| line | `tanh t = αt + β` ⇔ with `z = e^{2t}`: `1 − 2/(1+z) = (α/2)ln z + β`: hyperbola (`power_law`, `b = −1`, translated) meets log graph: **R** |
| sine | T4 (**N**); `sin/cos(αt+β)` both allowed |
| box | trivial; sup is an asymptote, so use `restrict` |
| arc length, offset inversion | `∫√(1+sech⁴)`: elliptic, **?** [Open] |

### 3.5 `ln sec x`
Offset inversion: `gd⁻¹ψ − dψ = x` (the T4 class `u ∓ d·gd u = c`, `d` free). Line: **R**. Arc
length `asinh(tan x)`: **E**. Box: `tan` trivial. Weaker than 3.4 (needs the unproved/unbuilt
offset-inversion machinery; 3.4 uses one intersection).

### 3.6 Quartic `Q`
| operation | result |
|---|---|
| line, ellipse, poly, power, Bézier | algebraic, **E** |
| `sine`/`cosine` | T1 + T2 (**N**) |
| `exp_two` | `2^t = affine(Q)`: **?** (new: exponential against an algebraic-with-radical) |
| box | trivial (asymptotes ±1, `restrict` first) |
| arc length / offset inversion | `∫√(1 + (1+x²)^{−3})`: elliptic type, **?** [Open] |

### 3.7 Cycloid and trochoids `(t − a sin t, 1 − a cos t)`, affine images
Coordinates are affine in `{1, t, sin t, cos t}`, so *both* trig functions appear, which no
sheared sine has.
- **Line meets trochoid:** `αt + β sin(t + φ) = γ`: Kepler class, **R** [Proof].
- **Offset inversion of the cycloid:** Whewell `s = 4a sin ψ`, so `4a sin ψ − dψ = x`: Kepler
  again, **R** [Proof, from the classical Whewell equation].
- **Box:** trigonometric only, **E**. Arc length `4a(1 − cos(t/2))`: **E**.
- **Conic meets trochoid:** the equation `Q(X(t), Y(t)) = 0` lies in the span of
  `{t², ts, tc, t, s², sc, c², s, c, 1}` modulo `s² + c² = 1`.
  [Wolfram, Gröbner basis over ℂ of the system "`Q(X,Y) ≡ λ(sin t − t cos t)` for some affine
  `(X,Y)` in `span{1,t,s,c}` and conic `Q`, `λ ≠ 0`": basis `= {1}`, **infeasible**.] So
  `tan t = t` is *not* a single conic section of any affine trochoid image. Other conic
  equations remain **?** [Open].

### 3.8 Logarithmic spiral `r = e^{kθ}`
- Line: `e^{kθ} cos(θ−β) = c ⇔ cos(θ−β) = c e^{−kθ}`: sine meets `exp_two` (`ln 2` is
  constructible), **R** [Proof].
- Offset inversion: `e^{kθ}√(1+k²)/k − dθ = x`, i.e. `e^{kθ} − (dk/√(1+k²))θ = c`: `exp_two`
  meets a line (Lambert-type), **R** [Proof].
- Box: `tan(θ−β) = k`, **E**. Arc length `√(1+k²)e^{kθ}/k`: **E**.
- Circle/ellipse/conic: mixes `e^{2kθ}` with two harmonics: **?**.

## 4. New rows

### 4.1 Polar-map images (P1 text-warp hypothesis)
Map `Φ(u,v) = (r₀ + c v)(cos(κu+θ₀), sin(κu+θ₀))`. [Proof, direct substitution]
- `v = const` → circle arc; `u = const` → ray; **`v = m u + b` (slanted line) → Archimedean
  spiral** `r = A + Bθ`. Since `A/B` is a ratio of P-constructible lengths and `κ = π/width`-type,
  the spiral's zero-radius angle is P-constructible; the unknown rotation is harmless.
- graph `v = a u^b` (`b ∈ ℚ`) → power spiral `r = Aθ^b` (Fermat `b = ½`, hyperbolic `−1`,
  lituus `−½`). Box: `tan(θ−β) = r'/r = b/θ`, i.e. **`θ tan(θ−β) = b`** (T6).
  [Wolfram: `b = 1/2, β = 1/5`: root `0.7737196282077538897459257387`, `NMaximize` of
  `√t cos(t−β)` agrees to 13 digits.]
- graph of a polynomial `p`: `r = p(θ)`, box `p(θ) tan(θ−β) = p'(θ)`, a rational right side
  `Σ mᵢ/(θ−αᵢ)`. For TrueType quadratic strokes (`deg 2`) this is T6-like.
- graph of `2^u` → logarithmic spiral (§3.8, nothing new).
- circles/ellipses (glyph `O`) → `r = A + B cos(μθ)`: algebraic in `e^{iθ/N}` for rational
  `μ`, **E** [Heuristic].
- **A glyph Bézier stroke** (cubic) → `(r₀ + c v(t))e^{iκu(t)}`, trig of a cubic: no named
  problem; and the warp of a *curved* glyph is not exact for P2 anyway.
- General principle: box of `r = F(θ)` solves `tan(θ − β) = F'/F` (log-derivative);
  `tan x = x` would need `F = e^{θ²/2}`, not drawable. `tan x = k − x` needs
  `F'/F = −cot-type`, which only the linear `F` supplies.

### 4.2 Linearly varying offsets `C(u) = B(u) + (au + b)ν(u)` (`u` = arc length of `B`)
`C' = (1 − (au+b)κ)T + aν`, so the box in direction `e_x` is stationary where
**`R'(ψ)(1 − a tan ψ) = aR(ψ) + b`** with `s = R(ψ)` the Whewell function of `B`. [Wolfram:
parabola (`a = 3/10, b = 1/7`) residual 0 to 38 digits; circle `R = ρψ` residual 0 to 39.]
- `B` = circle, radius `ρ`: `tan ψ + ψ = (ρ − b)/(aρ)`, **T3 with `k = (ρ−b)/(aρ)` arbitrary**
  (the spiral again, now with `k` read off *geometry* instead of a box direction).
- `B` = straight line: a shear, nothing.
- `B` = parabola (not a preset): `sec³ψ(1 − a tan ψ) − (a/2)(tan ψ sec ψ + gd⁻¹ψ) = b`, a
  Laurent polynomial in `e^{u}` plus `u`: of exp type, reachable as poly-meets-log when the
  degree is `≤ 6` (here 8): **?**.
- `B` with Bézier presets (Wave, etc.): `u` is not an arc length of a closed form; no exact
  statement. P1 must say whether the warp is arc-length based.

### 4.3 Tangent from a point / projective images [Proof + Wolfram]
Let `H` be a homography. Lines `x = const` in the image are the pencil through the vanishing
point `V`; their preimages are lines through `P = H⁻¹(V)`. So **`xmax(H(S))` is attained where
a line through `P` is tangent to `S`**. [Wolfram: random-ish `H` (entries `1.3, 0.2, 0.4, 0.08,
0.05`), sine curve; stationary point of `X(t)` satisfies
`sin t − P_y − cos t (t − P_x) = 0` to 36 digits.]
- Sine: `sin t − q = (t − p) cos t`, i.e. family E with `c = q`, `φ = −p`.
  `q = 0`: `tan t = t − p`, all `tan x = x + μ` (and gear `inv`); `p = 0, q = π/2`: **goat**.
  Geometric reading: the goat equation says the tangent to `sin` at `β` has `y`-intercept `π/2`.
- Affine images of the sine keep `λ = 1` (A cancels), so *no* `tan x = λx` with `λ ≠ 1`.
- Exp curve: `2^t − q = ln2·2^t(t − p)`: Lambert-type, already reachable.
- Relevance: 3-D perspective is an exact homography (`notes/3d/M2.md`), and the *rendered
  bounding rectangle's* far edge would be this box if a vector or sub-pixel read-out of a
  rotated sine were available. Today it is raster only (`3d-rotation-C-baking.md`), so this is
  **not usable**; it is the single most valuable thing P5 could find for rank 4.
- The PowerPoint *shadow* (perspective shadow) is a homography of the shape; whether it is
  vector is a P5 question.

### 4.4 Other warp classes (P1 follow-up, speculative)
- *Fade/trapezoid-type* warps `(u,v) ↦ (u(1 + a v), v)`: graph `f` becomes `(t(1 + a f(t)), f(t))`.
  Line → parabola. Sine → `x = t − a t sin t`: line meets it reachable (hyperbola meets sheared
  sine), but its box `1 = a(sin t + t cos t)` is a new family containing
  `tan t = −t` as `a → ∞`: **?** [Heuristic].
- *Wave* warps `v' = v + g(u)`: sums of curves `f + g`. If `g` is sine and `f` a polynomial or
  `2^x`, new but unnamed.
- A warp that multiplies, `v' = v·u`, would turn `sin x` into `x sin x` and give `sin x − x cos x`
  from boxes of `sinc`; no preset does this.

### 4.5 Chart-derived curves (log-x axis; memory note)
- `y = p(2^t)` (`p ∈ ℚ[z]`, `deg ≤ 6`): line meets it ⇔ `p(z) = α log₂ z + β`, a polynomial graph
  meeting a log graph: **R**. `sin t = p(2^t)`: polynomial meets `sin(log₂ z)` on a log axis:
  **?**, no named problem.
- `y = a·exp(k·2^t)` (Gompertz-shaped): meets a line ⇔ `ln(line) = k 2^t + const`: log graph meets
  `exp_two`: **R**. Meets `exp_two`: `z = a e^{kz}`, Lambert `W`: **R** (hyperbola meets
  `exp_two` already gives `W`). Meets sine/poly(`deg ≥ 2`): **?**.
- Hyperbolic functions are **not** reachable: `cosh t = (z + 1/z)/2` needs a negative power of
  `z`; `tanh t = 1 − 2/(1+z)` needs a *shifted* reciprocal; neither is a polynomial in
  `z = 2^t`. A power trendline `y = ax^b` on a log axis shows as an exponential in `t`.
- Sums/products: a stacked chart or a trendline on stacked data fits sums of *data*, and
  fill-handle data are arithmetic or geometric progressions. A degree-`≤6` polynomial through
  sums of polynomial data is a polynomial. **No chart route to `f + g` or `f·g` of curves**
  [Heuristic].

## 5. Probe assignment

| curve | probe | what must be shown | exactness |
|---|---|---|---|
| spiral | **P1 + P2** | outline of a warped slanted stroke is `r = A + Bθ` to render precision; conversion to a shape keeps it (not a Bézier fit); the box read-out acts on the ideal curve | (a) required; if (b), the roots are those of the *fit*, accepted only by the user |
| power spirals | P1 | straight strokes only give `b = 1`; others need curved glyph strokes with exact polynomial form | (a) unlikely |
| quartic | P5 (no lead) | any route to `(sinh u, tanh u)` or `(tan φ, sin φ)` | (a) |
| `tanh`/logistic | P3 | exact sigmoid trendline: none exists | (a) |
| catenary | P3, P4 | exact `cosh`: none | (a) |
| involute / projective image of sine | P5 | a vector (or exact numeric) read-out of a 3-D or shadow image | (a) |
| trochoid | P4 | motion-path "Sine Wave"/"Loop de Loop" are Béziers | (b) |
| chart curves | P3 | log-axis trendline = `p(2^x)`; only reduces to R classes | (a) |

## 6. Negatives and what each failing route gives

- **Spiral does not give `tan x = x`**; it gives T3 and `(x+β)tan x = 1`.
- **Offsets of spiral/involute** add nothing (stationary points unchanged; involute offset is a
  rotation).
- **Cycloid, trochoid:** Kepler only for lines and for offset inversion; Gröbner shows `tan t = t`
  is no conic section of an affine trochoid image.
- **Logarithmic spiral:** all line/offset results reduce to sine-meets-exp and exp-meets-line.
- **Chart curves:** lines reduce to R classes; `cosh`, `tanh`, logistic are out of reach.
- **Polar images of circles/ellipses** are algebraic in `e^{iθ/N}` (elementary).
- **Goat:** none of the spiral, quartic, catenary or `tanh` curves reach it (it needs
  `sin β − β cos β = π/2`, a *tangent intercept*, family E). Only the involute or a projective
  image of the sine does.
- **3-D perspective:** exact homography, so mathematically the strongest source of tangent-from-a-
  point, but its read-out is raster; nothing is drawable yet.
- **`λ ≠ 1` with the sine+involute (family E)** is impossible: affine images of the sine cancel
  the amplitude.

## 7. Corrections to earlier notes

- **R5 row 15** (finite spherical well, `l = 0`): `O/[Open]` should be **R**. With `x = ka`,
  `tan x = −x/√(R²−x²) ⇒ x + arcsin(x/R) = mπ ⇒ sin x = ± x/R`; the root has `cos x < 0`
  (`x = π − arcsin(x/R)`), so it is the unique intersection of `sin` with the line `y = x/R` in a
  window where `cos x < 0`. [Wolfram, `R = 3`: `x = 2.27886266007582831269995110456`, `cos x =
  −0.650366…`, residual 0 to 44 digits against both forms.] The 1-D even states `x tan x =
  √(R²−x²)` are `cos x = x/R` likewise (`x = 1.17012095000262605370604301186`).
- **R5 row 16** (`x tan x = Bi`): `O` should be **M** (needs only the quartic); `Bi = 1` also
  from the spiral.
- **`PLAN-ppt-tan-curves.md` §2 spiral row**: replace "`θ·tan(θ−α) = 1`, so `x tan x = 1` and
  `tan x = k − x`" with "`tan y + y = k` for every P-constructible `k`; `(x+β)tan x = 1`".
- **`sheared-sine-intersections.md` §2:** the quartic reaches `tan x = λx + μ` and `(λx+μ)tan x = 1`,
  not only `tan x = ±x`.

## 8. Open

1. Whether any combination of base operations reaches `tan x = x` from the spiral by a
   *non-uniform* configuration (excluded by convention only).
2. Conic ∩ trochoid beyond `tan t = t`; spiral ∩ conic / sine classes (§3.1) marked **?**.
3. Arc length and offset inversion of `tanh` and the quartic (elliptic type).
4. Whether a *shadow* or any 3-D read-out is vector (P5): decides rank 4.
5. P1 must test whether `Follow Path` is arc-length based (needed for §4.2) and give the exact
   zero-radius angle of the slanted-stroke spiral.
