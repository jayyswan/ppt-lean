# C: compositions of depth 2

Stream C of `pptc/PLAN-spiral.md` (wave 3). Pure mathematics; PowerPoint not opened; no Lean, no `Defs.lean` change,
nothing committed. Backend: **Wolfram MCP** for every identity and every number (25-40 digit working precision);
**no Python**. Labels: [Proof] paper argument, [Wolfram] checked, [Heuristic], [Open]. Classes E/R/N/? as in plan §1.
Assumption throughout: a spiral constructor exists (W's normal form: mirrored similarity images of `r = ψ` on windows
`[2πq₁, 2πq₂]`, P-constructible ends). Inputs: W, I1-I4, O, B, F2-F4, L, `M.md` §2, `sheared-sine-intersections.md`.

Notation. `θ₁ = 0.86033358901937976248389342413766233341188…` (root of `θ tan θ = 1`);
`θ₂ = 1.46066305530887730226827934974397474004639…` (root of `θ tan(θ−θ₁) = 1`);
`θ₃ = 1.93719470301168022604424635888789279907039…` (root of `θ tan(θ−θ₂) = 1`) [Wolfram, residuals 0 to 39 digits].
`A(ψ) = ½(ψ√(1+ψ²) + asinh ψ)`, `G_d(ψ) = A(ψ) − d(ψ + arctan ψ)`.

## Findings summary

**Two structural theorems, then the table.**

**(S1) Triangularity [Proof].** Every constructor takes *numbers* (P-constructible reals, or rationals/integers in a few
slots) and *curves*; every curve is a finite term of constructors applied to numbers; every number output (`inter_x/y`,
`arc_length`, `box_*`, field ops) is a function of earlier curves/numbers. So a depth-n number is the last entry of a
**triangular** system `x₁ = f₁(params)`, `x₂ = f₂(x₁, params)`, … where each `f_i` is one step of the one-step catalogue
(I1-I4, O, B) with its parameters set to earlier outputs. A nested form such as `θ tan(θ − β(θ'))` with *the same* unknown in
both places cannot arise from feeding numbers: a parameter is a number fixed before the step is posed. Hence **depth 2 by
parameter feeding is always "parameter extension"**: same equation shapes as depth 1, parameters moved from `D₀` to `D₁`.
The only genuinely coupled systems are *inside one step*, where two spiral-derived curves meet (I4: spiral ∩ spiral with
different poles, spiral ∩ its own offset). Those are already depth-1 catalogue entries; composition does not create them.

**(S2) The box tower is the iteration of one function [Proof + Wolfram].** `θ tan(θ − β) = 1` is equivalent (θ>0,
branch k) to **`θ + arctan θ = β + π/2 + kπ`**, i.e. with `y = arctan θ`, T3: `tan y + y = β + π/2 + kπ`. So the box step is
the (branchwise) inverse of the strictly increasing `φ(θ) = θ + arctan θ`, which is the spiral's tangent-angle function (O).
Depth-n box numbers are the iterates `θ_{n+1} = φ⁻¹(θ_n + (k+½)π)`. Consequences:
(a) the family `{θ tan(θ−β)=1, β ∈ P}` is *closed*: roots are in P and every P number is a legal β (angle `β rad` has
`cos β, sin β ∈ P`; conversely `arccos` of a P number is in P), so feeding roots back yields the same family with new β;
(b) **surjective**: every P-constructible θ* in a drawn window is the stationary point for `β* = θ* − arctan(1/θ*) ∈ P`;
the family has no "shape" beyond this one function, and `β` cannot depend on the root, which is why `tan x = x` is outside
(M.md §6: needs `β` to depend on the root).

| # | composition | system | decouples? | class | worked example (Wolfram) |
|---|---|---|---|---|---|
| 1 | box root → box direction (tower) | `θ₂ tan(θ₂−θ₁)=1`, `θ₃ tan(θ₃−θ₂)=1` | yes (S1) | N (T3, new β) | θ₂, θ₃ above; identity `θ+arctanθ = β+π/2` residual 0 |
| 2 | T3 root β₁ (root of `tan y=−y`, 2.02875…) → box direction | `θ tan(θ−β₁)=1` | yes | N (T3) | θ = 2.42053345642200987370061997, value `θ²/√(1+θ²)` = 2.23713576682834288996865771257; NMaximize agrees 22 digits |
| 3 | spiral number as eccentricity and mean anomaly in Kepler (sine ∩ line) | `E − θ₁ sin E = θ₂` | yes | R | E = 2.17074967083185188447000544321663 |
| 4 | spiral number as scale in `exp_two` ∩ hyperbola (Lambert) | `θ₁ x 2^x = 1` | yes | R (Lambert W) | x = 0.710376390726573106750771553823 = W(ln2/θ₁)/ln2 |
| 5 | spiral number as parameter of the parabola class (`y = θ₁x²` meets spiral) | `sin t = θ₁ t cos²t` | yes | ? (F4 class, k=θ₁) | t = 2.254958820845812694 (also 13.8495…) |
| 6 | spiral number as circle data (circle through pole, diameter θ₂, direction θ₁) ∩ spiral | `t = θ₂ cos(t−θ₁)` | yes | R | t = 1.31333621006112573966916226742 |
| 7 | spiral number as arc length in `arc_of_length` along the spiral | `A(ψ₁) = θ₁` | yes | R (parabola inversion) | ψ₁ = 0.785699071075559310791640373450 |
| 8 | `arc_length` of the sine between spiral-derived points | `∫₀^{θ₁}√(1+cos²t)dt` | yes | R-with-new-parameter (elliptic) | 1.148718518629067683325843 |
| 9 | spiral number as offset distance d (cusp) | `d²(ψ²+2)²=(1+ψ²)³`, d=θ₁ | yes | E/R (B row 4) | ψ_c = 0.891498060577295079461971457 |
| 10 | box value as offset distance, then box of the offset | `min ℓ·P_d = −V + d`, d=V₁=θ₁cosθ₁ | yes | N shifted (B row 3) | β=0.7: θ=4.08184774705857890126, min = −3.40350974859024819328348705 (NMinimize: 15 digits) |
| 11 | spiral number as d and as x in offset inversion | `G_{θ₁}(ψ₁) − G_{θ₁}(2) = θ₂` | yes | ? (O's OI-S) | ψ₁ = 2.88334910124913672511511410653; cusp-free: `dκ` = 0.462 → 0.312 < 1 |
| 12 | spiral number as scale_x (non-uniform image diag(θ₁,1)), arc-length inversion | `∫_{2π}^{ψ₁}√(θ₁²(cosψ−ψsinψ)²+(sinψ+ψcosψ)²)=θ₂` | yes | ? (B row 12, param θ₁) | ψ₁ = 6.50899282826070304375, residual 0 |
| 13 | spiral number as pole shift D, mirror pair | on-axis `u cos u = D/2` | yes | R | D=θ₁: u = 0.48667235094907366078, 1.2061098650579391391, 4.8020883275857003756 |
| 14 | spiral number as pole shift D, same orientation, equal pitch | `ue^{iu} − ve^{iv} = D` | **no, coupled within one step** (two unknowns) | ? (I4 different poles) | D=θ₁: (u,v) = (1.832516644037514002, 2.216787292500420027) |
| 15 | spiral number as polynomial coefficient | — | — | only through affine data (see §3) | — |

Headline results.
1. **Depth 2 contains no new equation shape by number feeding** (S1) [Proof]. All depth-2 entries above are depth-1 shapes
   with depth-1 parameters. New *numbers* (θ₂, θ₃, …) are expected to be new (not algebraic over earlier ones) but this is
   [Open]; no transcendence tool is available.
2. **Closed families.** Box/T3 (S2); Kepler (sine ∩ line); sine ∩ hyperbola; exp ∩ line; I1's master equation; each is closed
   in the sense "roots lie in P and every P tuple is a legal parameter tuple".
3. **Parameter slots that spiral numbers cannot enter:** power-law exponent `b`, polynomial *shape* coefficients of degree
   ≥ 5 (one invariant fixed rational for degree 5, two for degree 6), glyph rationals `q₁,q₂` (window ends are still free
   through `restrict`/`arc_of_length`). Everything else is open to P (rotation angle: B shows any P number is legal).
4. **T1, T2 (λ≠1), T6 are not reached** by any single step with arbitrary real constants [Proof, I1/F3 extended: their
   argument allows arbitrary real constants]; chains with *root-dependent* parameter sequences are not covered by that
   proof [Open], but nothing found. **Collapses to R/E** happen only at special parameters (rows 3, 4, 6, 13).
5. **Unsurveyed (curve-level depth 2):** spiral-derived curves meeting *other* closure-derived curves (offset of a sine/
   ellipse ∩ spiral, offset spiral ∩ offset conic, …). These are one-step with a larger curve class, not covered by
   I1-I4/O. Default class ? [Open].

## 1. Spiral number as a parameter of existing constructors

Which slots accept an arbitrary P-constructible number (all via `translate`, `scale`, `rotate`, `restrict`, base data):

| constructor | slot | accepts spiral number? |
|---|---|---|
| `ellipse`, `rectangle` | centre, width, height | yes (PConstructible) |
| `cubic_bezier` | control points | yes |
| `sine` | amplitude, frequency, phase, offset | yes (`scale_x/y`, `translate`) |
| `exp_two` | affine images `A·2^{λx+μ}+c`: rate λ, any P | yes; base is `2^λ`, so base 2 only up to λ ∈ P |
| `poly_graph` (rational coefficients, deg ≤ 6) | affine data (translate, scale, shear) | yes for affine data; **shape** only partly (§3) |
| `power_law` `y = a x^b` | `a` after scaling | `a` yes, `b` no (rational only) |
| `rotate` | angle | yes: B showed every P number is a legal angle |
| `arc_of_length` | length x, start point | yes |
| `offset` | d | yes (either sign) |
| `restrict` | window bounds | yes |
| `translate` | pole position | yes |

### 1.1 Sine: Kepler with spiral eccentricity and anomaly (row 3)
`E − θ₁ sin E = θ₂` has `E = 2.170749670831851884470005443216632796587756602…` [Wolfram, residual 0 to 39 digits]. This is
`line ∩ sine` with amplitude `θ₁` (a `scale_y`) and offset `θ₂`: R by `sheared-sine-intersections.md` §1 row 1. It is the
"Kepler with spiral eccentricity" asked for: the equation is Kepler's, the eccentricity just happens to be a spiral number.
`e = θ₁ < 1`, so the orbit is elliptic.

### 1.2 `exp_two` (row 4)
`θ₁ x 2^x = 1` has `x = W(ln 2/θ₁)/ln 2 = 0.71037639072657310675077155382287886321` [Wolfram: `ProductLog` formula, residual 0].
`2^{λ x}` with `λ = θ₁` is also directly available: the affine image of `exp_two` has rate `λ ∈ P`. Everything is R (I3 and
M.md §3.8: Lambert W is a line against `exp_two`).

### 1.3 Ellipse, Bézier
Spiral numbers as ellipse centre/axes or Bézier control points: the intersection with any line/ellipse is algebraic in the
data (E over the field generated). Intersection with the *sine* or `exp_two` is the corresponding sheared-sine row with
parameters in P: R. Intersection with the spiral itself is I1's master equation with `(A,B,m,f)` in P: rows 5, 6.

### 1.4 Rotation angle (rows 1, 2)
For a direction `β` taken from a spiral number the box needs `(cos β, sin β) ∈ P`, true because `cos_Pconstructible`/
`sin_Pconstructible` (W) hold for any P number. Row 2: `β₁ = 2.02875783811043422357697112473471437611` (root of
`tan y = −y`), `θ = 2.4205334564220098737006199697287300101`, `θ cos(θ−β₁) = θ²/√(1+θ²) =
2.23713576682834288996865771257567505796` [Wolfram]; `NMaximize` on `[2,3]` returns the same to 22 digits. Rotating a
**sine** by a spiral angle is the same as shearing it (shear = rotation + scaling in P): the rows of
`sheared-sine-intersections.md` with P parameters. Rotating the **spiral** only changes the phase `β`: row 1.

### 1.5 `arc_of_length` and `arc_length` (rows 7, 8)
Row 7: laying length `x = θ₁` along the unit spiral from the vertex gives `A(ψ₁) = θ₁`, `ψ₁ = 0.78569907107555931079164037345`
[Wolfram]. Class R: parabola arc inversion (B row 10). For any P-constructible start the equation is `A(ψ₁) = c` with
`c ∈ P`; the spiral number only changes `c`. Along the offset spiral or a non-uniform image the equation stays ? (B rows
11-13) with `c = θ₂`.
Row 8: `arc_length` of the sine from `(0,0)` to `(θ₁, sin θ₁)` is `∫₀^{θ₁}√(1+cos²t)dt = 1.148718518629067683325843…`
[Wolfram]; an elliptic integral at a spiral number. By S1 this is a depth-2 *number*, not a depth-2 *shape*.

## 2. Spiral number fed back into a spiral step

- **Window end.** `restrict` to a P-constructible window or `arc_of_length` from a P-constructible start isolates any
  sub-arc (B item 9). A window end `ψ*` that is a spiral number is legal: cut at `x = λ ψ* cos(ψ*−β)`, P-constructible;
  conversely `ψ* = |z−C|/λ`. So the glyph-tied rational ends are not a limit: W's "isolate a sub-arc" holds and F2's
  global-extremum restriction is removed (B). [Proof, conditional on B's argument]
- **Pitch / scale.** A pitch `λ` is a similarity, absorbed in the normal form (W); it changes only the relative position
  with other curves (a circle of fixed radius meets `r = λθ` at `θ = r/λ`). Parameter extension.
- **Offset distance d (rows 9, 10, 11).**
  - Cusp: for `d = θ₁ > 1/2` the unique cusp is the root of `d²(ψ²+2)² = (1+ψ²)³`: `ψ_c = 0.891498060577295079461971457`
    [Wolfram]. E/R (algebraic).
  - Box of the offset: `V ∓ d` (B row 3). With `d = V₁ = θ₁cosθ₁ = 0.56109633819104506754040375316` (a box value used as
    offset) and `β = 0.7`: stationary `θ = 4.08184774705857890126200761288`, `min ℓ·P_d = −V + d =
    −3.40350974859024819328348705055` (formula) vs NMinimize `−3.403509748590249018` [Wolfram, agree to 15 digits,
    optimizer-limited]. A difference of two T3 numbers: depth-2 only as a number.
  - Offset inversion (row 11): `G_{θ₁}(ψ₁) − G_{θ₁}(2) = θ₂`, `ψ₁ = 2.88334910124913672511511410653`. Window check:
    `dκ(2) = 0.4617`, `dκ(ψ₁) = 0.3122`, both < 1, so cusp-free on the whole window (κ decreasing) [Wolfram]. Class ?
    (O's OI-S) with depth-1 `(d, x)`.
- **Pole position (rows 13, 14).** Translate by a spiral number `D`:
  - Mirror-symmetric poles `±D/2`: roots on the axis solve `u cos u = D/2` (spiral ∩ line, R). `D = θ₁`:
    u = 0.48667235094907366078, 1.2061098650579391391, 4.8020883275857003756 [Wolfram]. Off-axis roots: none found for
    `u, v ≤ 12` by a multistart scan [Heuristic: not a certified count].
  - Poles shifted by `D` along x, same orientation: `u e^{iu} − v e^{iv} = D` has the off-axis root
    `(u, v) = (1.832516644037514002, 2.216787292500420027)` (further ones near 7.925/8.032, 11.124/11.047, …) for `D = θ₁`
    [Wolfram, residual < 1e-20, multistart]. A coupled two-unknown equation, already in I4 ("different poles"): class ?.

## 3. Polynomial coefficients: what a spiral number can enter

`poly_graph` and `power_law` have rational coefficients; the closure ops add P-parameters.
- **Degree ≤ 4: every P-coefficient polynomial graph is reachable** [Proof sketch]. Translation in x kills the cubic term
  (shift `b/(4a)`) [Wolfram: the shifted quartic has zero cubic coefficient], a shear `y → y + δx` kills the linear term,
  `translate_y` the constant. What remains is `a x⁴ + c x²`; `x → x/s` multiplies the ratio `c/a` by `s²`, so starting from
  the rational base `x⁴ ± x²` (sign by the sign of `c/a`) any P ratio is reached (needs `s = √|c/a|`, in P). Degrees 2, 3
  likewise.
- **Degree 5: one rational invariant, degree 6: two.** After the same normalisations a quintic is `c₅x⁵ + c₃x³ + c₂x²`,
  and `x → sx`, `y → λy` leave `I = c₃³/(c₂² c₅)` fixed [Wolfram: under `x → s₀x` the unnormalised ratio changes by
  exactly the weight `s₀⁵ = c₅`]. So the invariant of a reachable quintic is that of the *rational* base polynomial; a
  spiral number cannot be put into it. [Heuristic: only graph-preserving affine maps considered; a rotation takes the
  graph out of the graph family but gives a legitimate partner curve for an intersection, covered by F3's
  general-position enumeration.]
- **Power law `y = a x^b`:** `a` after `scale_y` and `scale_x` (`a' = c a s^{-b}`) takes any P value; **`b` never**. So
  `y = x^{θ₁}` is not drawable and T6 (`b ∈ ℚ`) stays rational. [Proof: `b` is the rational exponent in the constructor and
  affine maps do not change it.]
- Net: spiral numbers enter every I2/F3 family through the affine data; the shape classes of I2/F3 are unchanged.

## 4. Closure and the tower

Define `D₀` = numbers of the spiral-free class, `D_{n+1}` = closure under spiral-free operations of `D_n ∪ {roots of
one-step shapes with parameters in D_n}`.

1. **`D_{n+1}` is generated by triangular systems** (S1). Depth-n numbers are the field-closure of the solutions of the
   catalogue's shapes with parameters from `D_{n-1}`; there is no depth-2 shape beyond I1-I4, O, B.
2. **Family-level closure.** Each family is the fibre of a single master-function inversion:
   - box/T3: `φ(θ) = θ + arctan θ = β + π/2 + kπ` (S2), `β ∈ P` arbitrary, root in P: closed;
   - Kepler (line ∩ sine): `E − e sin E = M`: closed in `(e, M)`;
   - spiral ∩ conic: `Re(Aθ²e^{2iθ} + Bθe^{iθ}) + mθ² + f = 0`, parameters in P, roots feed back as new parameters: closed;
   - OI-S: `G_d(ψ) = c`, `(d,c) ∈ P²`: closed.
   Feeding roots back yields only the same family with new parameters.
3. **Do the towers grow?** `D₁ ⊋ D₀` is expected (θ₁ is T3; non-reducibility only argued for some classes in F4,
   [Heuristic]). `D₂ ⊋ D₁`: θ₂ solves `θ₂ + arctan θ₂ = θ₁ + π/2` [Wolfram: residual 0 to 39 digits], not an identity in θ₁.
   Whether θ₂ already lies in `D₁` is [Open]: no relation found, no transcendence tool here.
4. **Nested non-decoupling forms** like `θ tan(θ − β(θ'))` with `β` a function of the unknown are not produced by any
   composition. A θ-dependent phase would need a curve whose phase moves with the parameter (an involute of the spiral, a
   polar image, ...), none of which is a constructor. This is exactly the obstruction to `tan x = x` (M.md §6).
5. **Curve-level coupling** is the only route to new shapes: two spiral-derived curves in one `inter` (I4), a spiral
   against closure-derived curves (offset sine, offset ellipse, arc of a base curve), box/arc_length of those. Surveyed:
   spiral ∩ spiral, spiral ∩ own offset, offset-spiral ∩ line/conic (O). Not surveyed: spiral ∩ offset(base curve),
   offset(spiral) ∩ offset(base curve). [Open]

## 5. Reaching T1, T2 (λ≠1), T6 or named problems

- **T1 `tan x = λx + μ`, T2 `(λx+μ)tan x = 1` with λ≠1, T6 `θ tan(θ−β) = b`, b≠1.** The I1/F3 negative proofs hold for
  arbitrary real constants (they force `R = S = 0` coefficient-wise and find only the trivial solution), so substituting
  any depth-1 constants into a conic/line/graph/power-law/Bézier step cannot reach them [Proof for the one-step shape].
  The box step has `λ = 1` fixed: the argument slope of tan is tied to the radial slope of the spiral; feeding a spiral
  number into β changes only `μ`. Multi-step chains with root-index-dependent parameters are outside the proof: [Open];
  no composite produced `tan x = x` (θ₂, θ₃ satisfy no T1 relation in any form tried).
- **Biot/Robin family.** `x tan x = Bi` (T2, `λ = 1/Bi`) is reached only at `Bi = 1` (θ₁). `cot x = x + β` (the
  `μ = β` family) is a different problem (a Robin slab with offset origin). Other Bi are not reached by composition.
  Rod with Robin end `tan x = −x/h`: `h = 1` only (2.0287578…); `h ≠ 1` is T1-like.
- **Kepler** with spiral eccentricity: reached (row 3), but Kepler was already R, so this is just a new e.
- **Gear involute `inv α = k`** (`tan α − α = k`, T1 form with λ=1): not reached; `tan y + y = k` (T3) is reached for all k.
- **Collapse to R/E** occurs at special parameters: mirror poles (row 13, on-axis roots R), circle through the pole (row 6, R),
  offset cusp (row 9, E/R), centred/through-pole cases (E, I1), Kepler/Lambert via sine/exp (rows 3, 4). No composition
  collapses a ? or N family into R in general: collapse conditions are those of the one-step catalogue, unaffected by
  the values of the parameters.

## 6. Hypothesis and legitimacy notes

- Rows 10-13 use `offset` / `arc_of_length` on whole spiral arcs (O, B hypotheses); parameter values are P-constructible so
  the hypotheses are unchanged. Row 12 window condition `Δφ_M < π` was not re-checked for `diag(θ₁,1)` [Open].
- Rows 3, 4, 7: `PConstructible θ₁` is available because `box_xmax` yields it (given the spiral constructor).

## Other things noticed

1. **T2(λ=1) and T3 are the same family** (`x = π/2 − y`, `k = β + π/2`; M.md says so). New here: both are the inversion of
   the tangent-angle function `φ(θ) = θ + arctan θ`, so the whole box catalogue is level sets of one function. O's tangent
   angle `φ = ψ + arctan ψ` appears in `G_d = A − dφ`: offset inversion and the box tower share `φ`.
2. **Surjectivity of the box step** (S2b): the box gives every P number as a root for some P direction; novelty lives
   only in the *map* `β ↦ θ`, i.e. in the tower relative to a base field. Stream D should say "new numbers over the
   spiral-free class", not "new numbers over P".
3. **Mirror-pole intersection** had only axis roots in the scan (6 roots, all on-axis, for `D = θ₁`); a proof or a
   counterexample would settle whether mirrored spiral pairs are R in general. [Open]
4. Mirror poles (row 13, R) and shifted poles (row 14, ?) differ in kind: mirror symmetry supplies the line `x = 0` as a
   selector; no such selector exists for the shifted pair.
5. **Poly invariants:** the degree-5/6 rational invariants bound the `poly_graph` class (a quintic graph with a spiral-number
   shape coefficient is not drawable); irrelevant for the spiral intersections of F3, which use affine images only.
6. **Chain question (T1 via root-dependent parameters):** asymptotics of `tan x = x` roots, `(k+½)π − 1/((k+½)π) + …`, and
   of `φ⁻¹` iterates are both series in `1/kπ`, so asymptotics do not separate them. A separation needs a
   differential-algebra argument in F4's style for the composite system. Not attempted.
