# W4-offset: the offset of the egg has degree at least 16

Status: **W4a done (2026-11-10)**. Scoped negative: offset egg × general conic is not an
F = 11 engine. The geometric offset degree is **16** (N4's abscissa convention; this is the
degree that matches the ellipse octic and N4's other entries). The elimination polynomial
has total degree 28, a non-minimal degree; even the smaller geometric count 16 is well above
the threshold 10, and the parameter count (F = 11) cannot absorb the cofactor.

This note records the computation and the kill decision for W4a in
`PLAN-algebraic.md`. It supersedes the `[Open]` paragraph in `WARP.md` §8.1.

## 1. The question

`WARP.md` §8.1 observed that an offset adds one `PConstructible` parameter. The egg has
five parameters, so an offset egg has six; a general conic has five; hence
**offset egg × general conic** has F = 11, exactly H5's threshold for totally real decics,
provided the real offset degree `D` is small enough:

- crossing degree `2D`;
- cofactor degree at `n = 10` is `2D − 10`;
- the condition variety is positive-dimensional iff `2D − 10 < 11`, i.e. `D ≤ 10`.

W4a was to determine `D`. The answer is `D = 16` in N4's abscissa-degree convention: the
lower branch alone already has an elimination polynomial with X-degree 16 (total degree 28,
which is non-minimal).

## 2. Setup

The egg is

  `a² (d₀ + d₁ x − 2y)² = (d₀ + d₁ x)² x (2a − x)`,  `x ≥ 0`,

from `Pptc/Warp/Bilinear.lean` (`eggCurve`). Normalize `a = 1/2`, so `x ∈ [0, 1]` and
`D(x) = d₀ + d₁ x`. A rational parametrization of the lower branch is

  `x(t) = t² / (1 + t²)`,
  `D(t) = (d₀ + (d₀ + d₁) t²) / (1 + t²)`,
  `y(t) = D(t) (t − 1)² / (2 (1 + t²))`,  `t ≥ 0`.

(For `t ≥ 0`, `√(x(1−x)) = t/(1+t²)` and `y = D/2 − D√(x(1−x))`. The upper branch is
`t ≤ 0` with `(t + 1)²`; the lower branch alone already gives the degree bound below.)

The offset by signed distance `r`, in the convention of `Pconstructible.offsetParam`
(`unitNormal = (−y′, x′)/speed`), is

  `X = x − r y′/s`,  `Y = y + r x′/s`,  `s² = x′² + y′²`.

Eliminate `s` and `t` from

  `(X − x) s + r y′ = 0`,
  `(Y − y) s − r x′ = 0`,
  `s² − (x′² + y′²) = 0`

by two resultants (solve the first equation for `s`, substitute, then eliminate `t`).

## 3. Result

For the representative egg of the W4a task and three other generic parameter choices the
non-extraneous factor has the same bidegree (total degree 28, X-degree 16, Y-degree 12):

| `d₀` | `d₁` | `r` | total degree | `X`-degree | `Y`-degree |
|---:|---:|---:|---:|---:|---:|
| 1 | 2 | 1 | **28** | 16 | 12 |
| 2 | 3 | 1 | **28** | 16 | 12 |
| 1 | 4 | 1 | **28** | 16 | 12 |
| 2 | 5 | 1/2 | **28** | 16 | 12 |

The resultant also has extraneous factors in `X` only (degrees 1 and 3, squared); these come
from the parametrization denominators and are not part of the offset. The remaining factor
is irreducible over ℚ and is an elimination polynomial for the offset; its X-degree 16 is
the geometric offset degree. At a sample point `t = 2` it vanishes to the working precision
and its gradient is nonzero, so it is the correct component, not a spurious factor.

An independent **two-sided Groebner elimination** (the cross-product normal equation
`(X−x)F_y − (Y−y)F_x = 0` plus the distance equation, eliminating `x,y`) gives

  `(degree-4 extraneous factor)² · (degree-28 elimination factor)`,

with the degree-28 factor again of X-degree 16 and Y-degree 12. The degree-4 factor is
squared and has X-degree 2; it is not the offset. This confirms that the true offset is the
X-degree-16 component, not a lower-degree component hidden inside the resultant.

Calibration of the growth (total degree of the elimination polynomial / geometric X-degree):

| base curve | elimination total / geometric degree |
|---|---:|
| circle | 2 / 2 |
| parabola `y = x²` | 6 / 6 |
| ellipse | 16 / 8 |
| `y = x⁴` | 22 / 14 |
| egg (quartic) | **28 / 16** |

The **X-degree is the geometric offset degree**, and it matches N4's table (`N4.md` §8:
parabola 6, ellipse 8, `y = x⁴` 14) and the classical fact that the ellipse parallel curve
is an octic (MathWorld). The total degree of the elimination polynomial can be larger: the
ellipse analogue is total 16 but geometric 8, so the elimination polynomial is not minimal.
For the egg the geometric degree is **16**; the total 28 is the non-minimal elimination
degree. Both exceed the W4a threshold 10.

So the offset degree is not the optimistic sextic suggested by a preliminary numerical run.
That run used the mis-typed numerator `1 + 2t²` for the second term of `y`; the correct
numerator is `1 + 3t² = D(t)(1 + t²)`. With the corrected parametrization the low-degree
numerical relation disappears. **The geometric offset degree is 16.**

## 4. Consequence

The offset egg family has `5 + 1 = 6` P-parameters. A general conic has 5, so F = 11.

- The geometric offset degree is `D = 16`; crossing with a conic gives degree at least
  `16 · 2 = 32`, so the cofactor has degree at least 22 at `n = 10` (23 at `n = 9`).
- A naive Bézout count on the non-minimal elimination polynomial (total degree 28) gives
  56 and 46, even worse; the smaller geometric count 32/22 is the one that matters.

The parameter count is 11, far below the cofactor degree 22, so the condition variety has
no room for a monic linear-cofactor solution.

Even if the real locus were smaller than the complex degree, the F-point condition sees at
least the geometric degree-16 curve; the elimination factor is irreducible over ℚ of total
degree 28, so there is no smaller ℚ-factor to exploit either. The Bézout/parameter count
therefore kills **offset egg × general conic**, and with it the only warp-based route that
reached H5's F = 11 threshold.

**Comparison with the existing offset bases.** N4's table already has better offset bases:
a cubic Bézier offset has X-degree 10 with 8 control parameters, and `y = x^3` has X-degree
10. The egg offset has X-degree 16 with only 6 parameters (5 egg + distance). So even as an
offset-based engine or number source, the warp base is dominated by the offset bases
already in N4. The warp does not add a new offset engine.

**Scoped kill.** Offsets of the egg are closed as an engine route for the algebraic goals.
This does not say anything about offsets of other curves (`W1`'s offset towers), and it does
not say anything about non-algebraic uses of offsets (Route I, T6). It is a statement about
the egg offset and the egg × conic parameter count. A single offset egg is a new algebraic
curve of geometric degree 16, so a line section is outside the degree-8 closure; that is a
number-source question for the offset programme (`W1`/N4). A line partner would have F = 8
and cofactor degree 7, but the cubic Bézier offset (D = 10, more parameters) already
dominates it; it is not a new warp engine.

The kill is a Bézout/parameter-count kill, not a full H3 condition-variety computation. In
principle a highly degenerate condition variety of degree ≤ 10 could evade it, but the
degree-28 equation is irreducible over ℚ and there is no structural reason for such a
degeneration. Do not spend more on this route unless a new reason for degeneration appears.

## 5. Reproduction

The computation is one Wolfram cell:

```mathematica
x[t_] := t^2/(1 + t^2);
DD[t_] := (d0 + (d0 + d1) t^2)/(1 + t^2);
y[t_] := DD[t] (t - 1)^2/(2 (1 + t^2));
{d0, d1, r} = {2, 3, 1};
dx = D[x[tt], tt] /. tt -> t;
dy = D[y[tt], tt] /. tt -> t;
e1 = Numerator[Together[(X - x[t]) s + r dy]];
e2 = Numerator[Together[(Y - y[t]) s - r dx]];
e3 = Numerator[Together[s^2 - (dx^2 + dy^2)]];
sSol = Solve[e1 == 0, s][[1, 1, 2]];
e4 = Numerator[Together[e3 /. s -> sSol]];
res = Resultant[e4, Numerator[Together[e2 /. s -> sSol]], t];
FactorList[res]
```

The last factor is the elimination polynomial; its total degree is 28 and its X-degree is
16 (the geometric offset degree). Repeating with `{d0,d1,r} = {1,4,1}` and `{2,5,1/2}`
gives the same bidegree.

The independent two-sided check uses the cross-product normal equation:

```mathematica
F = a^2 (d0 + d1 x - 2 y)^2 - (d0 + d1 x)^2 x (2 a - x);
e1 = Numerator[Together[F]];
e2 = (X - x)^2 + (Y - y)^2 - r^2;
e3 = (X - x) D[F, y] - (Y - y) D[F, x];
gb = GroebnerBasis[{e1, e2, e3}, {X, Y}, {x, y},
  MonomialOrder -> EliminationOrder];
FactorList[gb[[1]]]
```

For `{a,d0,d1,r} = {1/2,2,3,1}` this returns
`(degree-4 factor)² · (degree-28 factor)`, and the degree-28 factor has X-degree 16,
Y-degree 12. The degree-4 factor is extraneous (it is squared).
