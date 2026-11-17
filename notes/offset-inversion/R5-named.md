# R5 — named problems in the angle–arc-length class

Stream R5 of `PLAN-offset-inversion.md`. Literature + Wolfram survey. **No `.lean` file is
touched by this note.**

Labels: **[Proof]** (argument written out here), **[Wolfram]** (checked in Wolfram Language,
30–50 digit working precision; see §6), **[Heuristic]**, **[Open]**.

## 0. The dictionary this note classifies against

Let `γ` have tangent angle `ψ`, arc length `s`, and Whewell function `s = R(ψ)`. Offset `γ`
by signed distance `d` and lay an arc of length `x` starting at the offset image of a point
where the tangent angle is `ψ₀` and `R(ψ₀)` is known. The endpoint tangent angle `ψ` solves

> **`R(ψ) − R(ψ₀) − d (ψ − ψ₀) = x`.**   (OI)

Equivalently, with `u = asinh(tan ψ)`, `ψ = gd u`, `tan ψ = sinh u`, `A(u) = ∫ S du` and
`S = ds/du`:

> **`A(u) − A(u₀) − d (gd u − gd u₀) = x`.**

The three **tower curves** that matter below are (`S = ds/du`, `w = tan ψ = sinh u`):

| curve | `R(ψ)` | `S(u)` | `dR/dψ` |
|---|---|---|---|
| catenary `y = a cosh(x/a)` | `a tan ψ` | `a cosh u` | `a sec²ψ > 0` |
| log-cosine `y = ln sec x` | `gd⁻¹ψ = ln(sec ψ + tan ψ)` | `1` | `sec ψ > 0` |
| parabola `y = x²/2` | `½(tan ψ sec ψ + gd⁻¹ψ)` | `cosh²u` | `sec³ψ` |

All three are monotone on `ψ ∈ (−π/2, π/2)`, so (OI) is an honest one-arc equation there.

**Status legend.** **R** = reachable now by the existing constructors. **C** = in the
offset-inversion class with a *drawable* curve (reachable once the L2-style formalization is
done). **M** = a **sufficient** offset-route construction requires a named **missing** curve.
This is a statement about one construction (Route O), **not** an impossibility result: the
intersection route (Route I) may or may not be excluded, and `R8-missing-curve-audit.md` marks
each row. **O** = outside this family (elementary/algebraic, or not of the form (OI)).

The "uniform convention" is `sheared-sine-intersections.md` §3: one configuration must solve
the whole family, changing only P-constructible data that does not depend on the unknown
root. Rows marked *uniform* below pass it; where the mode index changes a sign or an integer
multiple of `π`, that data is still root-independent (the integer is a window label).

**Convention tags.** The claims below are tagged `S` / `B0` / `B1` / `C` / `A` (`B1×C` for
hybrids); see `notes/reachability/R12-convention.md` §2 and §4.2, which is the reference table.
In particular, rows 7/10 with real log monodromy are A-robust; rows 6/13/15/16 are B-only, because
real value-side `φ` resolve their `1/log`, `δlogδ` or complex-monodromy log singularities; row 14 is
B-only by non-elementarity.

## 1. Summary table

| # | problem | classical equation | `(u, gd u)` form | curve (`R`) and data | status |
|---|---|---|---|---|---|
| 1 | optimal projectile arc length | `sin θ · gd⁻¹θ = 1` | `z tanh z = 1`, `θ = gd z` | — (elementary reduction) | **R** (L0) |
| 2 | primary rainbow angle | `cos i = √((n²−1)/3)` | algebraic in `n` | — | **R** (sqrt closure) |
| 3 | catenary of given length | `L = a sinh(b/a)`, `h = a(cosh(b/a)−1)` | — | — | **R** (elementary: `a=(L²−h²)/(2h)`) |
| 4 | Neile / semicubical parabola, `d=0` | `sec³ψ = 3x` | — | Neile `R=⅓sec³ψ` | **R** (collapses, `arccos`) |
| 5 | clothoid arc length | `ψ = s²/(2a²)` | — | clothoid `R=a√(2ψ)` | **R** (collapses to a quadratic in `√ψ`) |
| 6 | `tan x = λx`; `j₁` zeros; clamped–hinged beam; spherical well `l=1` | `tan x = λx` | `sinh u − λ gd u = λkπ` | catenary, `d=λ`, `x=λkπ` | **M** catenary |
| 7 | gear involute function | `tan α − α = k` | `sinh u − gd u = k` | catenary, `d=1`, `x=k` | **M** catenary |
| 8 | cantilever (clamped–free) beam | `cos x cosh x = −1` | `x ± gd x = (2m+1)π` | log-cosine, `d=∓1`, `x=(2m+1)π` | **M** log-cosine |
| 9 | clamped–clamped beam | `cos x cosh x = 1` | `x ± gd x = 2mπ` | log-cosine, `d=∓1`, `x=2mπ` | **M** log-cosine |
| 10 | rhumb line / isometric latitude | `gd⁻¹φ = kφ + c` | `u − k gd u = c` | log-cosine, `d=k`, `x=c` | **M** log-cosine |
| 11 | pendulum separatrix | `θ' = ±sin θ` (separatrix) | `θ = gd t` | log-cosine (same curve as 8–10) | **M** (reformulation only) |
| 12 | goat grazing (interior) | `sin β − β cos β = π/2` | `tan β − β = (π/2)sec β` | `R(ψ)=tanψ−(π/2)secψ`, `d=1`, `x=π/2` | **M**, plus pole/fold obstruction (§2.12) |
| 13 | tractrix | `s = ln cosh t`, `tan ψ = −csch t` | `ψ = gd t − π/2` | tractrix `R(ψ) = −ln sin ψ` | **M** tractrix |
| 14 | Euler elastica (rectangular) | `ψ'' + c sin ψ = 0` | `s = F(ψ/2 | m)` (elliptic) | elastica `R` = elliptic `F`, genus 1 | **M** elastica |
| 15 | finite spherical well `l=0` | `tan x = −x/√(R²−x²)` | algebraic in `sinh u, gd u` | no tower curve identified | **O** / [Open] |
| 16 | Biot / Robin eigenvalues | `x tan x = Bi` | `sinh u · (gd u + kπ) = Bi` | product, not (OI) | **O** (spiral route for `Bi=1`, other plan) |
| 17 | relativistic aberration | `cos θ' = (cos θ−β)/(1−βcos θ)` | `β = tanh η`, `θ = π/2 − gd η` (at `θ'=π/2`) | — | **O** (elementary) |
| 18 | caustics / rainbow | envelope of a one-parameter family | algebraic for algebraic mirrors | — | **O** (algebraic) |
| 19 | `tan x = x` by the quartic `y=x/√(1+x²)` | `(1+x²)sin²x = x²` | — | quartic / circle involute / quadratrix | **M** (not (OI); note §2) |
| 20 | Laplace-limit / catenoid | `z tanh z = 1` | `λ = csch z` | — | **R** (`Pptc/Basic.lean`) |

## 2. Derivations and sources

### 2.1 Optimal projectile arc length — **R**, uniform in nothing (a single number)

Maximising `∫√(1+y'²)dx` for `y = x tan θ − g x²/(2v²cos²θ)` gives

  `sin θ · ln(sec θ + tan θ) = sin θ · gd⁻¹θ = 1`.

Put `θ = gd z`; then `sin θ = tanh z` and `gd⁻¹θ = z`, so the equation is `z tanh z = 1`.
Hence `cot θ* = cos(gd z)/sin(gd z) = sech z / tanh z = csch z = λ`, the Laplace limit:

  `θ* = arccot λ = arctan(1/λ) = arctan(sinh z)`.

[Wolfram] `z = 1.1996786402577338339163698486…`, `θ* = 0.9855147378623154621149285372573…`
`= 56.4658351274523481063059796451…°`, `λ = cot θ* = csch z = 0.6627434193491815809747420971…`.
`Pptc/Basic.lean` already has `laplaceRoot`, `laplaceLimit` and `laplaceLimit_spec`, so this
is the L0 corollary and nothing new is needed from R5. Source: Cooper & Swifton,
*Maximising the arc length of a projectile*, arXiv:1611.02376 (the arXiv abstract states the
optimal angle is the smallest positive root of exactly this equation).

### 2.2 Primary rainbow — **R**

Descartes' stationarity condition for the primary bow is

  `cos i = √((n²−1)/3)`,

where `i` is the angle of incidence and `n` the refractive index. For `n = 4/3`,
[Wolfram] `i = 59.3911023402906921666577917610…°`. This is algebraic in `n`, so
`sqrt_Pconstructible` and `arccos_Pconstructible_of_mem_Icc` reach it; **no arc length** is
involved. Source: Descartes (1637); standard derivation in Adam, *The mathematical physics of
rainbows and glories*.

### 2.3 Catenary of given length and rise — **R**

For a catenary through `(±b, h)` (lowest point at the origin) with total length `2L`:
`L = a sinh(b/a)` and `h = a(cosh(b/a)−1)`. Eliminating `b/a` gives
`(h+a)² − L² = a²`, hence

  `a = (L² − h²)/(2h)`,

elementary in the P-constructible data `L, h`. [Proof] (algebra; no arc-length inversion is
needed). The catenary itself is **not** a `Defs` constructor, so this is a statement about the
classical problem, not a claim that the curve is drawable. Source: standard (Wikipedia,
"catenary"; Huygens 1691).

### 2.4 Neile's semicubical parabola and the clothoid — **R** (collapse)

- Neile `y = x^{3/2}`: `R(ψ) = ⅓sec³ψ`. With `d=0`, (OI) is `sec³ψ = 3x`, so
  `cos ψ = (3x)^{-1/3}` and `ψ = arccos((3x)^{-1/3})`: already reachable. This is the
  source note's collapse. With `d ≠ 0` the equation mixes `sec³ψ` and `ψ` and no longer
  collapses.
- Clothoid (Euler spiral, `κ ∝ s`): `R(ψ) = a√(2ψ)`. With `d ≠ 0`, putting `y = √ψ` gives
  `d y² − a√2 y + x = 0`, a quadratic; roots are radicals. So the whole clothoid offset
  family **collapses** and adds no new numbers. [Proof]

Sources: Neile 1657 (via the source note); clothoid: Cornu 1874, Fresnel integrals.

### 2.5 `tan x = λx` — **M**, catenary

`tan x = λx` with `x` in the `k`-th branch, `x = arctan(sinh u) + kπ = gd u + kπ`, becomes

  `sinh u − λ gd u = λkπ`.

This is (OI) for the **catenary** (`R(ψ)=a tan ψ`, `ψ₀=0`, `a=1`) with `d = λ`, `x = λkπ`.
[Wolfram] for `λ=1, k=1` the equation `sinh u − gd u = π` has
`u = 2.2080…`, and `tan(gd u + π) = 4.4934094579090641753078809272803…`, the first positive
root of `tan x = x`; residual `< 10⁻⁴⁸`. [Wolfram] `j₁`'s first positive zero equals the same
number to 10⁻⁴⁸; the clamped–hinged beam eigenvalue equation is also `tan x = x`.

- **Uniform in `λ`:** yes — one catenary, `d = λ`, window `k=1`, for every P-constructible
  `λ`; `x = λπ` is known data.
- `tan x = x` is the `λ=1` case; `k` is the branch label (a `restrict` window), not the
  family parameter.
- Source: `j₁` zeros — Abramowitz & Stegun 9.5; spherical well `l=1` — Griffiths, *QM*;
  clamped–hinged beam — Den Hartog, *Advanced Strength of Materials*.

### 2.6 Gear involute function — **M**, catenary

`inv α = tan α − α`. [Proof] This is (OI) for the catenary with `a=1`, `ψ₀=0`, `d=1`,
`x=k`: `tan ψ − ψ = k`. [Wolfram] `k=3/10` gives `α = 0.858844142240183196758295238687…`
rad `= 49.2081446098958471330129514194…°`, residual `<10⁻⁴⁹`. This is *the same curve and
the same family* as 2.5 — the involute function is the `λ`-free slice of the catenary
equation. Source: KHK, *Gear Technical Reference* §3.2, `inv α = tan α − α`; Wikipedia,
"Involute gear".

### 2.7–2.8 Bernoulli–Euler beam eigenvalues — **M**, log-cosine

For `y = ln sec x`, `ψ = x` and `s = ∫sec = gd⁻¹ψ`; so `R(ψ) = gd⁻¹ψ`. (OI) with `d = −1`
and base `ψ₀=0` is `gd⁻¹ψ + ψ = x`; with `d=+1`, `gd⁻¹ψ − ψ = x`. Writing `x = gd⁻¹ψ`
(i.e. `ψ = gd x`):

- `d=−1`: `x + gd x = const`;
- `d=+1`: `x − gd x = const`.

[Wolfram] the beam spectra are **exactly** these:

| beam | equation | spectrum |
|---|---|---|
| clamped–free (cantilever) | `cos x cosh x = −1` | `x + gd x, x − gd x, x + gd x, x − gd x, … = π, π, 3π, 3π, …` |
| clamped–clamped | `cos x cosh x = +1` | `x + gd x, x − gd x, … = 2π, 2π, 4π, 4π, …` |

Verified roots: `1.8751040687119611664453082410…` (`x+gd x=π`), `4.6940911329741745764363917780…`
(`x−gd x=π`), `7.8547574382376125648610085827…` (`x+gd x=3π`); clamped–clamped
`4.7300407448627040260240481008…` (`x+gd x=2π`), `7.8532046240958375564770666872…`
(`x−gd x=2π`), `10.9956078380016709066690325191…` (`x+gd x=4π`). Residuals `<10⁻⁴⁹`.

[Proof of the reformulation, up to the sign chase] `cos²x cosh²x = 1` gives
`cos²x = sech²x`, hence `sin²x = tanh²x = sin²(gd x)`, hence `x = ±gd x + 2πm` or
`x = π ∓ gd x + 2πm`; the four branches are the two displayed above with the sign of
`cos x cosh x` selecting `+1` or `−1`. **So both beam eigenvalue equations are offset
inversions of one curve**, with `d = ±1` and `x` an integer multiple of `π`.
Source: Den Hartog, *Advanced Strength of Materials*, ch. 5; Blevins, *Formulas for Natural
Frequency and Mode Shape*, table 8-1 (eigenvalues `1.875104`, `4.694091`, `7.854757` for
clamped–free, `4.730041`, `7.853205`, `10.995608` for clamped–clamped).

### 2.9 Rhumb line / Mercator — **M**, log-cosine

A rhumb line of course angle `k` on a sphere satisfies `gd⁻¹φ = kφ + c` (isometric latitude
linear in latitude). Put `u = gd⁻¹φ`, so `φ = gd u`:

  `u − k gd u = c`,

which is (OI) for the **log-cosine** curve with `d=k`, `x=c`, base `u₀=0`. [Wolfram] `k=2`,
`c=0`: `φ = 1.4638606385280711214813500422…` rad `= 83.8730363829842621288520075404…°`;
the identity `gd⁻¹φ = asinh(tan φ)` holds to 10⁻⁷⁹. (`k=1` has only the trivial `φ=0`; the
nontrivial crossing needs `k>1`.) Source: Wikipedia, "Rhumb line" / "Mercator projection";
the inverse Gudermannian is the isometric latitude (John D. Cook, "Inverse Mercator
projection").

### 2.10 Pendulum separatrix — **M** (reformulation, no new curve)

The separatrix of `θ'' = sin θ` is `sin(θ/2) = sech t`, equivalently `θ = gd t`
(`sin(gd t)=tanh t`). [Proof] So the **same** log-cosine curve that solves the beam and the
rhumb line is the separatrix: its Whewell function, `gd⁻¹ψ`, is the inverse of the
separatrix solution. This is a dictionary entry, not a new number. Source: standard
(Whittaker, *Analytical Dynamics*; the Gudermannian's origin in the Mercator problem).

### 2.11 Goat grazing (interior problem) — **M**, with a new obstruction

The interior goat problem reduces (Ullisch 2020) to

  `sin β − β cos β = π/2`,  equivalently  `tan β − β = (π/2) sec β`.

Let `R(ψ) = tan ψ − (π/2) sec ψ`. Then `R'(ψ) = sec²ψ − (π/2) sec ψ tan ψ`, and
`R(β) − R(0) − 1·β = π/2` is exactly the equation (since `R(0) = −π/2`). So **formally** (OI)
with `d=1`, `x=π/2`. [Wolfram] `β = 1.9056957293098838948826664371…` rad
`= 109.1883223255617178361742139273…°`; both forms vanish to `<10⁻⁴⁹`.

**Obstruction, new here.** Unlike the catenary and log-cosine, this `R` is **not monotone**
on any interval joining a convenient base point to `β`, and it has a pole at `ψ = π/2`
(inside `(0,β)`). `R'` is negative at `β` and at `2`, and positive at `2.5` and at `π`, so it
changes sign on `(β,π)`. A single laid arc from `ψ=0` would also have to cross the pole at
`π/2`. Starting at `ψ=π` avoids the pole (`R(π)=π/2`, and the equation again gives `x=π/2`),
but `R'` still changes sign on `(β,π)`. So the source note's dictionary entry is correct
**algebraically**, but the construction it suggests is not automatically legal; whether a
tower construction reaches `β` is **[Open]**.
The missing curve is the one with `|R'| = |sec²ψ − (π/2)secψ tanψ|`, which is not in the
tower (it is not algebraic, exponential or trigonometric in `t`). Source: Ullisch, *A
closed-form solution to the geometric goat problem* (2020); Quanta Magazine, 2020-12-09.

### 2.12 Tractrix — **M**, and a worked cusp crossing

Parametrise `γ(t) = (t − tanh t, sech t)`. Then [Proof]
`x' = tanh²t`, `y' = −sech t tanh t`, `speed = tanh t`, `κ = csch t`,
`ψ = gd t − π/2`, `s = ln cosh t`, and `sin ψ = −sech t`, so

  `R(ψ) = −ln|sin ψ|   (ψ < 0 on the drawn branch, and R(ψ) = −ln(−sin ψ))`.

(OI) is `−ln|sin ψ| − dψ = x`. This curve is **not** in the tower. [Wolfram]
`d = 3/10`: the offset has a cusp at `1 − dκ = 0`, i.e. `sinh t = 3/10`,
`t* = asinh(3/10) = 0.2956730475634224391027105297…`. On the cusp-free window
`[0.6, 1.1]`, numerical integration of the offset speed equals `ΔR − dΔψ`
(`0.2334433067007189440808822470…`, residual 10⁻⁴⁰). Across the cusp, the honest
`∫|1−dκ|` is `0.3221943039985032078261155044…`, while the signed `ΔR − dΔψ` is
`0.2334979243995302727025822850…`; the difference is `2×(the folded piece before t*)`
to the accuracy of the numerical integration near the non-smooth cusp. This is a concrete
instance of the R0 cusp question, not a new equation family. Source: standard (tractrix,
Huygens/Leibniz); the arc-length parametrisation `s = ln cosh t` is classical.

### 2.13 Euler elastica — **M**, elliptic (genus 1)

The planar elastica has `ψ'' + c sin ψ = 0`, so `s = ∫ dψ/√(2(E + c cos ψ))`, an elliptic
integral of the first kind in `ψ`; the rectangular elastica is the `E`-normalised `F`.
Offsetting adds `−dψ`, so the reachable equation is `F(ψ/2|m) − dψ = x`: still genus 1, but
the `ψ` term is **not** absorbed by `F`. [Proof, from the standard reduction] This is the
elliptic row of R1/R2; it needs a missing elastica curve. The **separatrix** is the
degenerate `m` limit and is exactly 2.10. Source: Levien, *The elastica: a mathematical
history*, UC Berkeley EECS-2008-103; Euler 1744.

### 2.14 Finite spherical well, `l=0` — **O**/[Open]

Matching conditions give `tan x = −x/√(R²−x²)` (`x = ka`, `R² = 2mV₀/ħ²`). [Wolfram] for
`R=3`, the first root is `2.2788626600758283126999511045…`, and `x² + x²/tan²x = 9` to
10⁻⁴⁹. In the `(u, gd u)` coordinate it is `sinh u = −(gd u + kπ)/√(R² − (gd u+kπ)²)`, an
**algebraic** relation between `sinh u` and `gd u`; this is not of the form (OI) with a tower
`A`. No tower curve is identified. [Open]: whether some composition of offsets/affine maps
produces a `u`-equation with these roots. (The `l=1` well is `j₁` zeros = row 6.)

### 2.15 Biot / Robin eigenvalues — **O**

`x tan x = Bi`. With `x = gd u + kπ`, `tan x = sinh u`, so
`sinh u · (gd u + kπ) = Bi`: a **product** of `sinh u` and `gd u`, not a difference. No `A`
in the tower makes this (OI). [Heuristic, not proved negative] For `Bi=1` the source note's
rotated-Archimedean-spiral box gives `x tan x = 1` directly; that is a *box* route, not an
offset-inversion route, and the spiral is `PLAN-ppt-tan-curves.md` territory. Source: standard
heat-transfer texts (Incropera; Carslaw & Jaeger).

### 2.16 Relativistic aberration / rapidity — **O**

With rapidity `η`, `β = tanh η`, and `cos θ' = (cos θ − β)/(1 − β cos θ)`. The condition that
the aberrated ray is perpendicular, `θ' = π/2`, gives `β = cos θ`; since
`tanh η = sin(gd η)`, this is `θ = π/2 − gd η`. [Proof] This is an **identity** relating two
angle coordinates, with no arc length and no unknown: every quantity is elementary in `η`.
So aberration is not an equation this programme solves. Source: Einstein 1905; standard
texts (Rindler, *Relativity*).

### 2.17 Caustics — **O**

For an algebraic mirror the catacaustic is the envelope of a rational one-parameter family,
hence algebraic; its points solve polynomial equations, not (OI). The rainbow (2.2) is the
one caustic condition that lands on a clean algebraic equation in an angle. High-degree
caustic coordinates are handled by `root_Pconstructible_le_six_coeffs` when the degree is
`≤ 6`. Sources: Bruce–Giblin, *Curves and Singularities*; Adam (1999).

### 2.18 `tan x = x` outside (OI): the quartic / involute / quadratrix — **M** (not (OI))

These are **intersection** routes, not offset-inversion routes, and are recorded here so the
final dictionary does not double-count them (source note §2):

- quartic `y = x/√(1+x²)` met with `y = sin x` gives `(1+x²)sin²x = x²`, whose roots include
  `tan x = ±x`; [Wolfram] the quartic residual vanishes at `4.493409457909064…` to 10⁻³⁸;
- the circle involute `(cos θ + θ sin θ, sin θ − θ cos θ)` crosses `y=0` exactly at
  `tan θ = θ`; [Wolfram] residual 0 to 10⁻³⁸;
- the quadratrix `x = y cot y` meets `x=1` at `tan y = y`; [Wolfram] residual 0 to 10⁻³⁸.

All three need a curve outside `Defs`; none is (OI). The quartic is the one to probe in the
PowerPoint UI (`PLAN-ppt-tan-curves.md`).

### 2.19 Laplace limit / catenoid — **R**

`z tanh z = 1` is the Laplace-limit equation (Lagrange series for Kepler's equation;
catenoid stability). [Wolfram] `z = 1.1996786402577338339163698486…`,
`λ = csch z = 0.6627434193491815809747420971…`, already formalised in `Pptc/Basic.lean`
(`laplaceRoot`, `laplaceLimit`). It is the same number as 2.1.

## 3. What this catalogue says

1. **The offset-inversion family is real and small.** It converts exactly the equations of
   the form `R(ψ) − dψ = x`; among the named problems above, five distinct missing curves
   carry all of them: **catenary** (rows 6, 7), **log-cosine** (rows 8, 9, 10, 11),
   **goat's transcendental curve** (row 12), **tractrix** (row 13) and **elastica**
   (row 14).
2. **Catenary and log-cosine are the whole story for the classical eigenvalue equations.**
   Every beam mode and every `tan x = λx` / `j₁` / involute equation is one of these two
   curves with `d = ±1` or `d = λ` and a `π`-multiple displacement. That is a sharper
   statement than "the offset family is large".
3. **The `l=0` well and `x tan x = Bi` are genuinely outside.** They produce products or
   algebraic relations between `sinh u` and `gd u`, not a difference. `Bi=1` is reachable by
   the *other* mechanism (a box of a spiral), which is a different plan.
4. **Nothing here is a negative theorem.** Rows 15/16 are [Open]/[Heuristic]: no tower curve
   was found, but R3/R4 must prove the separation, not this note.
5. **Named problems that are already reachable** are the projectile/Laplace constant (L0),
   the rainbow (sqrt), the given-length catenary (arithmetic), and the degenerate
   `d=0` Neile/clothoid cases (radicals). None of these needs the offset construction.

## 4. Uniform-convention notes

- Rows 6, 7 are **uniform**: `d = λ` (row 6) or `d = 1` (row 7), `x` a known multiple.
- Rows 8–10 are **uniform in the branch index** but not in a continuous parameter; the sign
  of `d` alternates with the mode, and `d = ±1` is known data. Whether the plan's convention
  wants one fixed sign per configuration or allows the window to select it is a question for
  R3/R4; this note flags it rather than deciding it.
- Row 12's `d=1, x=π/2` is fixed, but the pole/fold obstruction means the *construction* is
  not established.

## 5. Open items handed forward

1. **R1/R2**: compute the Whewell functions of the catenary/log-cosine/tractrix/elastica
   and the goat curve *as curves in the tower question* — they are all outside `Defs`, so
   R1 records them as missing, not as reachable, and R2 must decide what their affine images
   do.
2. **R3**: prove that no single intersection/box solves `tan x = λx` uniformly. The catenary
   route needs a curve that is not drawable; the quartic/involute/quadratrix routes need
   their own curves. The source note's §3b analytic-continuation argument is the model.
3. **R4**: (a) the goat's pole/monotonicity obstruction — can a two-step construction cross
   it? (b) whether `x tan x = Bi` can be written as (OI) with a *tower* `A(u)` after one
   affine step (the product looks irreducible, hence [Heuristic]).
4. **R0**: the tractrix cusp example (§2.12) is a concrete test case for the "lay an arc
   across a cusp" question.

## 6. Numbers: backend and residuals

Everything numeric in this note was produced by **Wolfram Language** via
`wolfram_WolframLanguageEvaluator`, with `WorkingPrecision` 30–50. Representative residuals
(all `0``n` = zero to `n` significant digits):

| check | residual |
|---|---|
| `x + gd x − π` at `1.8751040687…` | `0``49.6` |
| `x + gd x − 2π` at `4.7300407448…` | `0``49.6`* |
| `x − gd x − π` at `4.6940911329…` | `0``49.3` |
| `sinh u − gd u − π` at `u=2.2080…` | `0``49.0` |
| `tan(gd u + π) − (gd u + π)` at the same `u` | `4.49340945790906417530788092728…` (matches the root to 10⁻⁴⁸) |
| `tan α − α − 3/10` at `0.8588441422…` | `0``49` |
| `gd⁻¹φ − 2φ` at `1.4638606385…` | `0``48.8` |
| `sin β − β cos β − π/2` at `1.9056957293…` | `0``49.3` |
| `tan β − β − (π/2)sec β` at `1.9056957293…` | `0``48.3` |
| `tan x + x/√(9−x²)` at `2.2788626600…` | `0``49.1` |
| `j₁` first zero `−` first root of `tan x = x` | `−1.2…×10⁻⁴⁹` |
| tractrix offset, cusp-free window `[0.6,1.1]`, `d=3/10` | `0``40.6` |

\* the `2π` clamped–clamped check returned `2.1×10⁻⁴⁹` with a zero-precision marker from
`FindRoot`; the underlying residual is at the 49th digit.
