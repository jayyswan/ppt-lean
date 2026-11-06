# Offset inversion: equations in the tangent angle

**Question.** What does `arc_of_length` along an **offset** curve solve?

Earlier analyses (`Pptc/Jacobi.lean`, Outlook; `sheared-sine-inversion.md` §3) set the offset
aside, because it "adds only `−d` times the turning angle, which is elementary". For `am` that
is correct. But it misses something: the turning angle *as a function of the unknown
endpoint* is a transcendental function that no intersection supplies. Inverting along an
offset therefore solves a class of equations that intersections apparently cannot reach.

Labels:

- **[Proof]**: complete argument on paper.
- **[Wolfram]**: checked in Wolfram Language to about 40 digits.
- **[Heuristic]**: the natural routes are excluded, but there is no proof.

## 1. The mechanism [Proof + Wolfram]

Let `γ` be a drawable curve with tangent angle `ψ` and arc length `s`. Write its **Whewell
equation** (arc length as a function of tangent angle) as `s = R(ψ)`.

The offset by `d` satisfies `P_d' = (1 − dκ) γ'`. So on any stretch without cusps
(`1 − dκ > 0`), its arc length is

  `L_d = ΔR − d Δψ`.

Lay an arc of P-constructible length `x` along `P_d`, starting from the offset image of a
point where `ψ` is P-constructible, such as a vertex. Then read the endpoint off with
`box_xmax`/`box_ymax`, which works whenever the arc is monotone in a coordinate. This makes
P-constructible the root `ψ` of

  **`R(ψ) − d ψ = x`**   for every P-constructible `d` and `x`.

**Example: the parabola `y = x²/2`.** In terms of the slope `w = tan ψ`, its Whewell function
is `R = (w√(1+w²) + asinh w)/2`.

- The offset-arc formula `L_d(w) = (w√(1+w²) + asinh w)/2 − d·arctan w` was checked against
  numerical integration of the offset speed. [Wolfram, residual 0 to ~39 digits at
  `d ∈ {1/2, −3, 9/10}`, `w ∈ {7/10, 3}`]
- For `d < 1` there are no cusps, since `κ ≤ 1`. The offset abscissa `w(1 − d/√(1+w²))` is
  then increasing, so `box_xmax` returns it, and `w` is a root of a quartic with
  P-constructible coefficients.

## 2. The right coordinate: `tan ψ = sinh u`, so `ψ = gd u`

Parametrize any curve by `u = asinh(slope)`. Then `ψ = gd(u) = 2 arctan(eᵘ) − π/2`, the
Gudermannian. Write `S(u) = ds/du`. Then:

- the curve is recovered from `S` by `x = ∫ S / cosh u du` and `y = ∫ S tanh u du`;
- offset inversion solves `A(u) − d·gd(u) = x`, where `A(u) = ∫ S du`.

Single intersections of drawable curves solve equations that mix `u` with **one** of:

- `eᵘ` (exp-type curves);
- `sin`/`cos` of a linear function of `u` (sine-type curves).

An equation that needs **both `u` and `gd u`** is outside that list, because `gd u` is the
*angle* of the algebraic point `(1, sinh u)`. Arc length is the only operation that turns an
algebraic point into its angle as a function of a parameter.

So whether intersections alone can reach this class is **[Heuristic]**: I know of no route,
but there is no proof. Under the uniform convention of `sheared-sine-intersections.md` §3, the
analytic-continuation argument used there should settle it. Not done.

### What is reachable now [Proof]

Power laws `y = x^{1+1/n} + m x` (rational exponent, drawable) have

  `S(u) ∝ cosh²u · (sinh u − m)^{n−1}`.

- `n = 1` is the parabola: `A = sinh(2u)/4 + u/2`.
- `n = 2, m = 0` is Neile's semicubical parabola: `A = cosh³u / 3`.
  - Its equation collapses to `sec³ψ = αψ + β`. That has a single trig function, so it was
    already reachable by intersection.
- `m ≠ 0` mixes these with parabola terms, for example
  `cosh³u/3 − m(sinh 2u/4 + u/2) − d·gd u = x`.

So, for instance:

> **`sinh(2u)/4 + u/2 − d·gd(u) = x` has P-constructible roots for every P-constructible
> `d < 1` and `x`.**

This is, as far as I can tell, the first family of reachable equations that mixes a variable
with its Gudermannian (equivalently, `ψ` with `gd⁻¹ψ = ln(sec ψ + tan ψ)`).

Other drawable curves give non-elementary versions:

- general power laws give incomplete Beta functions minus `d·gd`;
- ellipses give `E` minus `d·ψ`;
- sheared sines give `Λ` minus `d·ψ`.

## 3. The famous "tan-type" equations land in exactly this class [Proof + Wolfram]

| Equation | In the `(u, gd u)` coordinate | Curve whose offset inversion would give it |
|---|---|---|
| `tan x = λx` (`j₁` zeros, clamped–hinged beam) | `sinh u = λ(gd u + kπ)`, where `x = gd u + kπ` | **catenary**, Whewell `s = a tan ψ` |
| cantilever beam `cos x cosh x = −1` | `x + gd x = π` (first mode), equivalently `sin x = tanh x` | **log-cosine curve** `y = ln sec x`, Whewell `s = gd⁻¹ψ` |
| goat-grazing problem `sin β − β cos β = π/2` | `tan β − β = (π/2) sec β` | Whewell `ds/dψ = sec²ψ − (π/2) sec ψ tan ψ` (transcendental) |

[Wolfram:
- beam root `1.87510406871196…`: `sin x − tanh x` and `x + gd x − π` both vanish to 40 digits;
- `tan x = x` root `4.49340945790906…`: `sinh u − gd u − π` vanishes, with `u = asinh tan(x − π)`.]

The beam reformulation is elementary: `cos²x cosh²x = 1` gives `cos²x = sech²x`, hence
`sin²x = tanh²x`. And `gd x = arcsin(tanh x)`. I had not seen it stated before; it may be
known.

**What this says.** Each of these needs one specific curve whose Whewell function makes the
equation exact. A uniform version (for all `λ` or all right-hand sides) forces exactly that
curve, because the Whewell function determines a curve up to congruence.

- The catenary has type-E coordinates `(t, cosh t)` but is not an offset or affine image of
  `2ˣ`.
- `ln sec x` composes a logarithm with a trig function, so it is in neither tower.

So all three are **[Heuristic]** out of reach for the *same* reason: one missing curve each.
That is a sharper statement than "needs sin and cos together" (`sheared-sine-intersections.md`).
None of these curves may be assumed. They become relevant only if the PowerPoint UI can
draw one, under an idealization the user accepts. That question is `PLAN-ppt-tan-curves.md`.
The same plan covers the quartic `y = x/√(1+x²)` of the earlier note, which would reach
`tan x = x` through an intersection instead.

A related check [Wolfram]: the box (extreme point) of a rotated **Archimedean spiral** solves
`θ tan(θ − α) = 1`. That gives `x tan x = 1` and `tan x = k − x`, but **not** `tan x = x`.

## 4. A small named-constant corollary (already reachable)

The launch angle that maximizes the arc length of a projectile's trajectory in vacuum is
`θ* ≈ 56.4658°`. It solves `sin θ · gd⁻¹θ = 1`, equivalently `csc θ = coth(csc θ)` (Cooper &
Swifton).

Put `θ = gd z`. Then `sin(gd z) = tanh z`, so the condition becomes `z tanh z = 1`. That is the
Laplace-limit / catenoid equation. Hence

  **`cot θ* = λ`, the Laplace limit constant `0.66274…`**, so `θ* = arccot λ`.

[Wolfram, 40 digits.] Given `λ` (in `Basic.lean`), this is P-constructible in one line. It is
cute rather than deep; I did not find this link with `λ` stated anywhere.

## 5. Open

- **Formalize §1 for the parabola.** You need:
  - `speed (offsetParam γ d) = (1 − dκ) speed γ` on a cusp-free window;
  - the closed-form antiderivative;
  - `arc_of_length` plus `box_xmax` on the offset arc (`BoxOffset.lean` already has the box
    half).

  The result would be the first Lean theorem whose number needs `u` and `gd u` together.
- **Prove the [Heuristic] in §2** under the uniform convention: no single intersection solves
  `sinh(2u)/4 + u/2 − d·gd u = x` for all `x`.
- **Iterate.** Affine images of offsets, offset again, have Whewell functions involving
  `√Q_n/Q_k^{3/2}` terms (Jacobi.lean Outlook). Do any of them produce `S(u) = cosh u`
  (catenary) or `S = const` (log-cosine) *exactly*? The congruence argument says no single
  curve can. But an equation with the same roots, not uniformly, is not excluded.
- **Classify the Whewell functions** `R` of all curves in the offset/affine tower. That is
  the complete list of equations this mechanism solves.
