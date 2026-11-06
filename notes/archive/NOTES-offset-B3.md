# NOTES-offset-B3 — what offsets give beyond algebraic numbers

Status: COMPLETE. Task B3 of the `offset` programme. Scripts `archived files/offset-scripts/B3-*`.
Tags: [Lean] = proved in the library or checked via lean-lsp; [symbolic] = exact CAS reduction;
[numeric, N digits] = agreed/verified to N digits. No `.lean` file other than the private
`Pptc/Scratch/OffsetB3.lean` was touched. `sorry` = UNPROVED.

## Summary (12 lines)

1. Offset speed is `σ|1−dκ|`; a cusp-free offset arc has length `L−dΔθ` [symbolic; numeric 25].
2. `Δθ` is elementary for every drawable base, so cusp-free offset lengths add only a constructible angle: no new transcendental constant.
3. Cusp parameters solve `κ=1/d`, a cubic in `σ²`/`cos²x`/`(ln2)²2^{2x}` for ellipse/sine/`2^x`; cusped lengths are signed sums of constructible pieces.
4. `arc_of_length` on an offset inverts `s(t)−dθ(t)` (`E−elementary` for the ellipse); new functions, but neither `F` nor `am`.
5. The `s−B` obstruction is unchanged: an elementary angle cannot cancel the elliptic/boundary term.
6. Named equations are already reachable: Dottie, Lambert `W`, Laplace limit are library theorems; Kepler and `a sin x+b cos x=cx` follow from `sine ⋔` line.
7. `x=tan x`, Bessel zeros, catenary parameter, goat angle are not reachable; the offset-sine crossing gives a candidate new equation `x=d cos x/√(1+cos²x)`.
8. Minimal distance to `y=x^7` gives degree-12/13 algebraic candidates (Galois `S₁₂`/`S₁₃`); the normal condition is not a crossing, so not shown reachable.
9. Curvature at a constructible parameter is already in `K`; evolute/involute/cycloid/trochoid curves are not (they need a variable offset distance).
10. Parallel-ellipse perimeter `4aE(m)−2πd` and the largest sine-arch circle (`r=1/2`) are already reachable.
11. Technique: clearing `√` after an offset `⋔` line gives exact algebraic systems (e.g. `cos⁴x=1−d²` [Lean]); the variable-offset barrier is a reusable negative.
12. Bottom line: offsets enrich the class of constructible curves/implicit functions but yield no new named transcendental constant and do not reach `am`.

## Candidate table

| # | number / function | construction | new or already reachable (reason) | numeric check |
|---|---|---|---|---|
| 1 | Dottie `0.739085…` | `cos x = x`, cosine graph (`sine` translated) `⋔` `y=x` | **already** [Lean] `dottie_Pconstructible` | 0.739085133215160641655312087674 |
| 2 | Lambert `W(1)=0.567143…` | `e^u = 1/u`, `exp_two` (`scale_x log2`) `⋔` `power_law(-1)` | **already** [Lean] `lambertW_Pconstructible` | W(1)=0.567143290409783872999968662210 |
| 3 | Laplace limit `0.662743…` | `exp` `⋔` shifted hyperbola; [Lean] `laplaceLimit_Pconstructible` | **already** | — |
| 4 | Kepler anomaly `E` (e=0.7,M=1.1) | `sine ⋔` line `y=(x−M)/e` | **already** (immediate; not named) | 1.78413120270851721600135840892 |
| 5 | root of `a sin x + b cos x = cx` | `R sin(x+φ)` is a translated/scaled `sine` `⋔` line | **already** | 3.01880809273309726635233377163 (a=1.3,b=−0.6,c=0.25) |
| 6 | offset-sine `⋔ X=0`, d=1 | `x = d cos x/√(1+cos²x)` | candidate (unresolved); not identifiable | 0.628821244630582539464254567316 |
| 7 | offset-sine `⋔ Y=0` | `cos⁴x = 1−d²` [Lean] | reduces to `arccos((1−d²)^{1/4})`; **already** (`arccos_Pconstructible`) | — |
| 8 | foot of normal, P=(0,2) to `y=sin x` | `(2−sin x)cos x = x` | new transcendental eq.; not a legal crossing | x=0.839119566090770871515947680292, dist=1.51046981128962586399739702462 |
| 9 | min distance (1,0)→`y=x^7` | normal eq. `7t^13+t−1=0` | **candidate new**; deg 13, Galois S₁₃, extraction illegal | t=0.769159571193067978732271085199, dist=0.280449702706599812416313250736 |
| 10 | min distance (0,1)→`y=x^7` | `7t^12−7t^5+1=0` | **candidate new**; deg 12, Galois S₁₂ | t=0.687951574050468880810466029919 / 0.975052597739749…, dist 1.154442…/0.988434… |
| 11 | perimeter parallel ellipse | offset ellipse full loop; `4aE(m)−2πd` | **already** (`ellipticE_Pconstructible`, π) | P₀=9.68844822054767619842850319639 |
| 12 | largest circle under sine arch | symmetric tangent at (π/2,1), `r=1/2` | **already** (ellipse constructor) | 0.5 |
| 13 | cusp parameter of ellipse offset | `σ³=dab` → `sin²t=((dab)^{2/3}−b²)/a²` | **already** (nested radicals + arcsin) | d=0.7: t=0.25343572038134529142 |
| 14 | inverse of `s(t)−dθ(t)` (ellipse `aE(t,m)−d·arctan`) | `arc_of_length` on offset ellipse/sine | **new function**, no name | sine offset T(d=0.4,L=2)=2.14563871558326005455029098067 |
| 15 | involute/cycloid point | `(cos s+s sin s, sin s−s cos s)` etc. | point **already**; curve **not reachable** | (s=0.6): (1.1641210989466995, 0.0694411044492284) |

## Q1 — Lengths of offset arcs

**Setup.** Write `σ=|γ'|`, `K=det(γ',γ'')`, `κ=K/σ³` and `θ` for the tangent angle, so
`θ'=κσ`. Then `d/dt(γ+dN) = γ'(1−dκ)` and `speed(γ+dN)=σ|1−dκ|` [symbolic, B3-01]:
`sympy` reduced `speed(offset)² − σ²(1−dκ)²` to `0` for a generic `γ`. This is (O1).

**Cusp-free (O2).** Where `1−dκ` keeps one sign, `∫σ(1−dκ)dt = L − dΔθ` with `Δθ=θ(b)−θ(a)`.
Verified numerically to ≥25 digits for the ellipse `(2cos t, sin t)` and the sine, at `d=±0.3,
±0.8, 0.5, −1.1`, four `T` values (B3-01, diffs `0` or `2.3e-41`).

**Turning angle is elementary for every drawable base.** B3-01 gives, exactly:
* ellipse `a cos t, b sin t`: `K=ab`, `κσ = ab/σ²`, and `∫κσ dt = arctan((a/b)tan t)`;
  the correction integrand `σ(1−dκ)−σ = −d·ab/σ²` is rational in `sin,cos`, hence elementary.
* sine: `σ²=1+cos²t`, `K=−sin t`, `∫κσ = arctan(cos t)`.
* `2^x`: correction integrand `−2^t(ln2)²/(1+(ln2)²4^t)`, an `arctan`/`log` type.
* polynomial/power-law graph: `κσ = y''/(1+y'²)`, integral `arctan(y')`; parabola elementary.
Thus for a cusp-free offset arc whose endpoints are constructible **plane points** (which they are:
the offset endpoint is `γ(t)+dN(t)` with all data constructible), the measured length is
`L − d·(elementary angle)`. If `L` is reachable then so is the offset length; if the base arc came
from `arc_of_length` (length prescribed), the offset length is that prescribed number plus a
constructible angle. **No new constant.**

**Cusps.** A cusp of the offset is a zero of `1−dκ`, i.e. `κ(t)=1/d`. Squaring gives:
* sine, `u=cos²x`: `d²(1−u)=(1+u)³` — a **cubic** (B3-01);
* `2^x`, `w=(ln2)²2^{2x}`: `d²(ln2)²w=(1+w)³` — a **cubic**;
* ellipse, `σ²=a²sin²+b²cos²`: `σ³=dab`, i.e. `sin²t=((dab)^{2/3}−b²)/a²` — nested radicals.
So the cusp parameters are **constructible** (roots of a cubic then `arcsin`/`arccos` of
constructible data). Past a cusp the length is `∫|1−dκ|σ dt = Σᵢ εᵢ(Lᵢ − dΔθᵢ)` over the smooth
pieces; each piece is constructible and `εᵢ` is determined by which side of the constructible cusp
parameter the interval lies (this is exactly the `sign(S_k)` correction of R1a, verified there to
30 digits for offset chains). Hence **cusped offset lengths are in `K`**, and add no new constant.
The one place degree can grow is a high-degree base: for `y=x^7` the cusp equation is
`d²·1764·x^{10}=(1+49x^{12})³`, degree 36; here the cusp is *not* constructible by the radical
trick. This matters legally, because the offset is **not differentiable at a cusp**, so
`arc_length` (which demands `DifferentiableAt` at every parameter) cannot be applied across one:
a cusped offset arc must be measured piecewise, and that requires each cusp parameter to be a
constructible plane point. For ellipse/sine/`2^x` it is (displayed above); for `y=x^n`, `n≥7`, it
is not, so only the smooth pieces between *other* constructible endpoints are measurable there.
The cusp itself is not a crossing, so its coordinate is never extracted.

**Arcs obtained via `arc_of_length`.** Offsetting such an arc is legal (`offset` does not require
constructible endpoints), but the offset's far endpoint is then not a constructible plane point, so
`arc_length` cannot be applied to it directly. The way to use it is Q2: lay a *new* string on the
offset. This is the only route by which an offset interacts with a length that was itself the
output of an inversion, and it is exactly the `s(t)−dθ(t)` inversion below.

## Q2 — `arc_of_length` along offsets

`arc_of_length` inverts `s_d(t)=s(t)−dθ(t)` (cusp-free branch). The new inverse functions:
* **ellipse**: `s_d(t)=aE(t,m)−d·arctan((a/b)tan t)`, `m=1−b²/a²`. At `d=0` this is the known
  inverse of `E`, `ellipticEAm` [Lean `ellipticEAm_Pconstructible`]. For `d≠0` it is a *new*
  implicit function, the inverse of "second-kind elliptic **minus** elementary". Numeric check
  (B3-04): for `d=0.4`, inverting the sine-offset length `L=2` gives `T=2.14563871558326005455029098067`
  (residual 0 at 50 dps).
* **sine**: `s_d(x)=∫₀ˣ√(1+cos²)−d·arctan(cos x)` (or equivalently `−d·arctan(cos x)` shifted).
* **parabola**: the speed `√(1+4x²)` has an elementary antiderivative and the turning angle is
  `arctan(2x)`, so both terms are elementary and the inverse is elementary; no named new constant
  appears. (Its offset is a rational curve, cf. (O6).)
* **`2^x`**: correction elementary (log/arctan), base length elementary (R1c), so the inverse is
  elementary.
**Named functions/constants reached: none new.** The new object is the *function*
`(E − elementary)^{-1}`, which is not `EAm`, not `am`, and not in the existing catalogue. It is a
genuine but unnamed extension.

**Legality.** On the cusp-free branch the offset is traced by `t ↦ offsetParam γ d t`, whose start
is constructible and which stays injective; `offset` gives `hC1` (continuous velocity) and
`hreg` (nonvanishing speed), so `arc_of_length` is applicable. Across a cusp it is not (no
differentiability), cf. Q1.

**The `s−B` obstruction (one paragraph).** The overview explains that `F` is reachable forwards
only as `s_C − B` (arc length of a Bézier/curve minus an algebraic or second-kind boundary term),
and `arc_of_length` inverts `s_C`, not `s_C − B`. Offsetting changes `s_C` to `s_C − dΔθ`, where
`Δθ` is an **elementary** turning angle (Q1). An elementary function cannot cancel the elliptic
`E`-term or the algebraic boundary term responsible for the obstruction: at a pole/branch point of
the underlying elliptic curve the elementary angle is regular, while the obstruction lives in the
non-elementary part. So the offset does not convert `s_C−B` into a pure first-kind integral and
`F` (hence `am`) stays out of reach; this is the same reason R1a/R1c give. No amplitude quest was
pursued here.

**Can a clever `(d, curve)` cancel the blocking term?** No, in the class of drawable curves. The
offset contribution is `−d·Δθ` with `Δθ` elementary for every base (Q1), while the blocking term is
either the second-kind `E`-part or an algebraic boundary term; an elementary function is regular
where those have their non-holomorphic pole, so it cannot cancel them. The only way would be a base
curve whose **own** arc length is a pure first-kind form (R2's Serret family), which is not a
`Defs.lean` constructor.

## Q3 — offsets of `y=sin x` and `y=2^x` versus lines/conics/offsets

**Named equations, and their true status.**
* **Kepler `M=E−e sin E`**: crossing the `sine` curve with the line `y=(x−M)/e` gives
  `sin E=(E−M)/e`, i.e. Kepler. Unique on a suitable window. **Already reachable** (a line with
  constructible slope/intercept is `power_law(1)` scaled `scale_y` and translated). Numeric:
  `E=1.78413120270851721600135840892` for `e=0.7, M=1.1`, residual 0.
* **Lambert `W`**: `x·2^x=a` is `exp` `⋔` hyperbola; already a library theorem
  `lambertW_Pconstructible` [Lean], with the same construction (Basic.lean:2094). **Already.**
* **Dottie number**: `cos x=x`; already `dottie_Pconstructible` [Lean] (Basic.lean:2784).
* **`x=tan x`**: the equation mixes `x`, `sin x`, `cos x` nonlinearly. No known move produces the
  curve `y=tan x` or `y=x cos x`, and the sine-offset `⋔` line equation (below) does not reduce to
  `x cos x=sin x`: after clearing `√(1+cos²x)` it is
  `(a x+b sin x+c)²(1+cos²x)=d²(b−a cos x)²`, whose monomials are all of even total degree in
  `sin,cos` plus terms containing `x`; it cannot be rearranged into the odd combination
  `x cos x−sin x`. First root `4.49340945790906417530788092728`, not identifiable.
* **Bessel zeros / catenary parameter / goat-grazing angle**: not reachable. Bessel needs `J_ν`,
  not a constructor; the catenary is a *sum* of `e^x` and `e^{−x}` (no addition of curves); the goat
  problem leads to inverting `r ↦ r²arccos(r/2R) − …`, a combination no constructor inverts.
* **`a sin x+b cos x=cx`**: `a sin x+b cos x=R sin(x+φ)` is a translated, scaled `sine`, crossed
  with the line `y=cx`. **Already reachable.** Numeric root `3.01880809273309726635233377163`.

**The genuinely new offset-sine equation.** Crossing the offset of `(x,sin x)` by `d` with a
general line `aX+bY+c=0` gives `a x+b sin x+c+d(b−a cos x)/√(1+cos²x)=0`, and squaring produces a
polynomial relation between `x` and `(sin x,cos x)` that is **not** of the form `sin x=f(x)` for a
drawable `f`. Example (vertical line `X=0`, `d=1`): `x=cos x/√(1+cos²x)`, numeric root
`0.628821244630582539464254567316`, not identifiable by `mpmath.identify` and not a known constant.
This is a *candidate* new transcendental number, but I did not prove it is outside the closure of
bare crossings, so it is recorded as **unresolved**, not as a positive result. (Horizontal line
`Y=0` is the exception: it reduces to `cos⁴x=1−d²`, i.e. `arccos` of a fourth root, already
reachable.) For the `2^x` offset the same exercise produces `log`/`arctan`-elementary relations;
Lambert `W` and its generalized forms are already covered.

## Q4 — Distances and normals

* **Curvature at a constructible parameter** needs no new move: for the sine
  `κ=−sin x/(1+cos²x)^{3/2}`, so `κ(x)`, `ρ(x)=1/|κ|`, and the centre of curvature
  `γ(x)+ρN(x)` are field expressions of constructible numbers. Cosine/sine of a constructible are
  `cos_Pconstructible`/`sin_Pconstructible` [Lean]. Numeric: at `x=0.7`, `κ=−0.3228460645425…`,
  `ρ=3.0974514167…`. **Already in `K`, no offset needed.**
* **Foot of the perpendicular** from a constructible point to a transcendental curve. From
  `P=(X,Y)` to `y=sin x` the foot solves `(X−x)+(Y−sin x)cos x=0`. For `P=(0,2)`:
  `(2−sin x)cos x=x`, root `x=0.839119566090770871515947680292`, distance
  `1.51046981128962586399739702462`, not identifiable. This is a **new transcendental equation**
  not produced by any constructor: the normal line at the foot is not a fixed curve. It is not
  extractable by `inter_x`/`inter_y` (the normal bundle is a 1-parameter family, and `offset` takes
  a fixed `d`). **Negative result: the foot and the minimal distance are not shown reachable**;
  what *is* reachable is the whole family of offsets `offset_d(C)` for constructible `d`, which
  immediately gives the points at a *chosen* distance `d` from `C`, not the minimum.
* **Minimal distance between two curves** has the same character: it is an extremum with a common
  normal, not an isolated crossing, so no move reaches it. Offsets give "all points at distance `d`",
  for fixed `d`, not the critical `d`.
* **Radius of curvature data**: already reachable pointwise (above). The *evolute*, which is the
  offset by the variable `ρ(t)`, is not.

## Q5 — Envelopes, evolutes, involutes, constant width

* **Involute of a circle.** A *single* point has constructible coordinates: at constructible arc
  length `s`, `(cos s + s sin s, sin s − s cos s)` is a field combination of `s`, `cos s`, `sin s`
  (`cos_Pconstructible`, `sin_Pconstructible` [Lean]). But the **involute as a curve** is not a
  `Defs.lean` object: it is the locus of endpoints of the tangent lines to the circle (a 1-parameter
  family), and the move set has no constructor for it. Numeric `(s=0.6)`:
  `(1.1641210989466995, 0.0694411044492284)`.
* **Cycloid / trochoid.** A single point at constructible rolling angle `θ` has constructible
  coordinates `(θ−sinθ, 1−cosθ)`; neither curve is an offset of a drawable curve, and the rolling
  construction is not in the move set. **Not reachable as curves.** Numeric `(θ=0.8)`:
  `(0.0826439…, 0.3032932…)`.
* **Evolute / involute of a Bézier.** The evolute is `γ(t)+ρ(t)N(t)` with *variable* offset
  distance; `offset` only permits a constant `d ∈ K`. The set of cusps of `offset_d(Bézier)` as `d`
  varies *traces* the evolute, but `d` is not variable within one construction. So the evolute is
  **not reachable as an offset-related set**; only individual curvature centres at constructible
  parameters are. This matches the fact that the evolute of a cubic Bézier is a rational curve of
  degree higher than any single crossing could pin.
* **Constant-width curves.** A curve of constant width `w` satisfies `offset_w(C) = C` rotated by
  `π`. Among constructible curves the only constant-width example is the circle (offset of a circle
  is a concentric circle). Offsetting an ellipse or Bézier never returns a rotation of itself; so no
  non-circular constant-width curve is reachable. **Negative.**

## Q6 — Special values

* **Minimal distance to `y=x^7`.** `y=x^7` *is* drawable as `power_law(1,7)`. Foot from `(0,1)`
  solves `7t^{13}−7t^6+t=0`, i.e. `t(7t^{12}−7t^5+1)=0`. The degree-12 factor is **irreducible**
  over `ℚ` [symbolic, sympy] with mod-`p` cycle types including a 12-cycle (`p=2`) and an 11-cycle
  with fixed point (`p=3`), which generate `S₁₂` [Galois evidence via Chebotarev cycle types]. Two
  real feet: `t=0.687951574050468880810466029919` (dist `1.15444207558299459520930860323`) and
  `t=0.975052597739749303492561805282` (dist `0.988433813797326373272420251878`). From `(1,0)` the
  foot solves the irreducible `7t^{13}+t−1=0` (Galois `S₁₃`: a 13-cycle at `p=31`, a 12-cycle at
  `p=13`), `t=0.769159571193067978732271085199`, distance `0.280449702706599812416313250736`.
  Eliminating `t` gives a **degree-12** minimal polynomial for `distance²` from `(0,1)` (after the
  extraneous root `z=1`) and a degree-13 one from `(1,0)`. **Verdict: candidate new algebraic
  numbers, not shown reachable** — the extraction is a critical-point (common-normal) condition, not
  a unique crossing, and the known engines stop at degree ≤8 (plus the nonic and septic families).
  The checklist: irreducible degree 12/13 over `ℚ` [symbolic]; not ≤8 [symbolic]; not nonic
  (degree 12/13) [symbolic]; Galois `S₁₂`/`S₁₃` (orders divisible by 7 and 11), so outside every
  tower of degree-≤6 field extensions of `ℚ`, whose degrees are 5-smooth [Galois evidence]. It is
  *not* excluded from `K` by that alone: `K` has higher-degree engines (the decic offset engine of
  `Offset.lean`, cubic⋔power-law), and degree 12–13 sits beyond all of them, which is exactly what
  makes these candidates interesting.
* **Largest circle under a sine arch.** By symmetry the circle is centred at `(π/2,r)` and touches
  `y=0`; tangency to the sine at its maximum forces `2r=1`, so `r=1/2`. Reachable directly by the
  `ellipse` constructor (a circle of width=height=1 centred at `(π/2,1/2)`). **Already.** (Numerical
  sanity: `min_x ((x−π/2)²+sin²x)/sin x =1` at `x=π/2`.)
* **Perimeter of a parallel ellipse.** `P₀=4aE(m)` with `m=1−b²/a²` [Lean
  `ellipticE_Pconstructible`]. For a cusp-free offset `P_d=P₀−2πd`; numeric `a=2,b=1`: `P₀=`
  `9.68844822054767619842850319639`, and `∫|σ−dκσ|` agrees to 30 digits for `d=0.2`. For
  `d>` cusp threshold `b²/a=0.5` the offset self-cuts and the length is the signed sum over the
  constructible cusp parameters; e.g. `d=0.7`: cusp `t=0.25343572038134529142` and length
  `5.89099709807244725931414369002`. **Already in `K`** (E at constructible arguments, π, d).
* **`mpmath.identify`** returns `None` for all the offset-sine/normal-distance values above, and
  PSLQ finds no low-degree algebraic relation; they are not simple closed forms. No value here
  leads to a known non-elementary constant in closed form. Wolfram `RootApproximant[·,8]` and
  `FindIntegerNullVector[{1,π,log2,e,·}]` on the 30-digit inputs return only **spurious** relations
  whose coefficients (~`10¹²`) do not stabilise when the precision is raised — artifacts of the
  digit truncation, not identifications.

## Q7 — Techniques

1. **Offset speed/normal form.** `speed(offset)=σ|1−dκ|`, `κ=det(γ',γ'')/σ³`; the turning angle
   `∫κσ dt` is elementary for every base. Reusable for any offset length question.
2. **Cusp-radical trick.** Cusps solve `κ=1/d`; for ellipse/sine/`2^x` squaring reduces this to a
   cubic, so cusp parameters are constructible radicals and cusped arc lengths are signed sums of
   constructible pieces. (For `x^n`, `n≥7`, it becomes degree `≥3n` and becomes a candidate
   obstruction.)
3. **Offset to solve a normal-combination equation.** Clearing `√` after crossing an offset with a
   line/conic yields an exact algebraic system in `(x,sin x,cos x)`; e.g. `Y=0` gives
   `cos⁴x=1−d²`. This is the offset analogue of `offsetCrossPoly_normalForm`.
4. **Variable-offset barrier.** Every object that needs an offset distance depending on the point
   (evolute, involute, offset by radius of curvature, distance-to-curve) is out of reach because
   `offset` takes a constant `d`. This is a clean, reusable negative criterion.
5. **Trading a transcendental inversion for an offset.** An offset converts the inversion
   `s(t)=ℓ` into the inversion `s(t)−dθ(t)=ℓ`. Because `θ` is elementary this *does not* buy a new
   transcendental function, but it does provide a family of new implicit functions and is the
   cleanest illustration of why `arc_of_length` cannot reach `F`.

## Side discoveries

* The turning angle of the ellipse offset is **elementary**, not elliptic:
  `∫ab/σ² dt = arctan((a/b)tan t)`. (The *first-kind* integral for the ellipse is `∫1/σ dt`, which
  is a different quantity and is what R1a's obstruction is about; the turning angle is the *second*
  form `∫κσ dt`.) This is why the offset length is `E − elementary` rather than `E − F`.
* Crossing the sine offset with the x-axis produces the exact algebraic relation
  `cos⁴x = 1 − d²` for any `d`, i.e. the point `x = arccos((1−d²)^{1/4})`. For `d²=1/2` this is
  `arccos(2^{−1/4})`; the number `2^{−1/4}` is a degree-4 algebraic already reachable, so no new
  constant, but the reduction is a clean worked example of the offset normal form.
* Cusps of the offset of `y=x^7` satisfy the degree-36 equation `d²·1764x^{10}=(1+49x^{12})³`;
  this is a concrete example where the cusp parameter leaves the radical regime, even though the
  offset curve itself remains constructible.
* The minimal-distance polynomials `7x^{12}−7x^5+1` and `7x^{13}+x−1` have full symmetric Galois
  groups (`S₁₂`, `S₁₃`), so if a construction ever reached them it would be the first `K`-member
  with such a group — a sharp target for the frontier work.

## Leads for other tasks

1. **Q3 offset-sine equation as a genuine new number.** `x=cos x/√(1+cos²x)` (and its general
   `a,b,c,d` family) is a candidate outside every current engine; a B-task/SYN task should try to
   decide whether it reduces to a constructible crossing or whether it is a new closure point of
   `K`. Deciding this needs a theory of which `x`-`sin`-`cos` relations drawable crossings can
   produce (compare R1c §4's algebraic-`φ` argument).
2. **Cusped offset arc lengths as a degree engine.** For `y=x^n` the cusp equation has degree
   `3n` in `x` (e.g. 36 for `n=7`); if a way were found to extract a cusp (rather than a crossing),
   this would be a whole new high-degree algebraic source. Check whether the cusp locus of one
   offset can be obtained as the self-intersection of a *second* offset, i.e. an `offset ⋔ offset`
   crossing (A3).
3. **`(E − elementary)^{-1}`.** The new implicit function from Q2 should be added to the catalogue
   of constructible functions; it is the natural next inversion after `ellipticEAm`. Check whether
   it satisfies an autonomous ODE with an elementary right-hand side (the `kind` criterion of X5
   §3.2) and whether that class is closed.
4. **Minimal distance to `y=x^n`.** The foot equations for `n=2,3,4` have degree 3,5,7 ≤ 8 and are
   therefore automatically reachable; `n=5` is degree 9 and should be checked against the nonic
   family `nonicVal_root_Pconstructible`; `n=6` (degree 11) and `n=7` (degree 13) are candidates.
   A clean statement "the foot from `P` to `y=x^n` is in `K` iff its minimal polynomial is covered
   by the current engines" would sharpen the frontier.
5. **Offset vs variable-curvature objects.** The variable-offset barrier (Q7.4) should be stated as
   a B2/B4 lemma: no finite sequence of `offset` with constant `d` produces the evolute/involute of
   a drawable curve, because the offset distance is a constant parameter of the construction.

## Verification index

| item | claim | tag | script / source |
|---|---|---|---|
| speed identity | `speed(off)=σ|1−dκ|` | [symbolic] | B3-01 |
| (O2) | `L_d=L−dΔθ` | [symbolic]+[numeric,25] | B3-01 |
| ellipse turning angle | `∫ab/σ²=arctan((a/b)tan t)` | [symbolic] | B3-01 |
| sine turning angle | `∫κσ=arctan(cos x)` | [symbolic] | B3-01 |
| cusp cubics | sine `d²(1−u)=(1+u)³`, `2^x` `d²(ln2)²w=(1+w)³` | [symbolic] | B3-01 |
| Kepler | `E=1.78413…`, residual 0 | [numeric,30] | B3-02 |
| Dottie | `dottie_Pconstructible` | [Lean] | Basic.lean:2784 |
| Lambert W | `lambertW_Pconstructible` | [Lean] | Basic.lean:2099 |
| Laplace limit | `laplaceLimit_Pconstructible` | [Lean] | Basic.lean:2462 |
| `cos⁴x=1−d²` | offset-sine `⋔ Y=0` | [Lean] | Scratch/OffsetB3.lean |
| foot poly | `7x^{12}−7x^5+1` irreducible, Galois `S₁₂` | [symbolic]+[Galois cycle types] | B3-03, Wolfram/sympy |
| foot poly 2 | `7x^{13}+x−1` irreducible, Galois `S₁₃` | [symbolic]+[Galois cycle types] | B3-03, Wolfram/sympy |
| parallel ellipse | `P_d=P₀−2πd`, `P₀=4aE(m)` | [symbolic]+[numeric,30] | B3-04 corrected |
| inscribed circle | `r=1/2` | [symbolic] | B3-02 |
| arc_of_length inverse | `T(d=0.4,L=2)=2.1456…` residual 0 | [numeric,50] | B3-04 |
