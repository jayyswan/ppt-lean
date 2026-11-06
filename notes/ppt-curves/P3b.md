# P3b: chart trendlines with data-determined real exponents

**Verdict: the parameters are all P-constructible, but the payoff is nil for the wishlist.** Every
exponent, base and coefficient a trendline can produce from UI-reachable data is P-constructible.
The exponential trendline `y = a r^x` is already derivable (an affine image of `exp_two`), so it is not
a new curve. The power trendline `y = a x^b` with irrational `b` (for example `b = log_2 3`) is a genuinely new
*curve*, but every intersection that matters reduces by `x = 2^s` to pairs of existing exponential curves, so it
reaches no new *numbers* against lines, `exp_two` or rational power laws. It reaches unnamed classes against
polynomials of degree 2 or more, the sine, conics and Bezier curves. It reaches none of tan x = x, the
cantilever beam, the goat problem or the inverse involute. The Gompertz curve does not help with `tanh` or the
logistic function.

Backends: Wolfram (`mcp__wolfram__WolframLanguageEvaluator`) for every identity and every number to 20 digits or
more. Python (win32com plus numpy, labelled) only to drive PowerPoint and parse its SVG export. Labels:
[Proof] / [Wolfram] / [Measured] / [Heuristic] / [Open]. Scripts and SVGs are in the scratchpad `P3b\` folder
(d1.py defaults, d2.py fill rules, f2.py render check).

## Findings table

| Curve (route) | Parameters reachable | Derivable already? | What it unlocks | Class |
|---|---|---|---|---|
| Exponential trendline `a r^x` (`a e^{bx}`) | `b` = LS slope of `ln y`, `r = e^b`, `a = e^{mean ln y - b mean x}`; all P-constructible; rational data give `b` in a rational combination of `ln` of rationals | **Yes.** `exp_PConstructibleCurve` (`scale_x` of `exp_two` by `log 2`), then `scale_x` by `1/b` and `scale_y` by `a` | nothing beyond `exp_two`; log of any positive P-constructible is already in the class | R (no new curve) |
| Power trendline `a x^b`, `b` rational | any rational `b` the LS happens to give | Yes, `power_law a b` | nothing new | R |
| Power trendline `a x^b`, `b` irrational (a ratio of quadratic forms in logs; two points give `ln(y2/y1)/ln(x2/x1)`) | `b` and `a` P-constructible (`log_Pconstructible`, field ops, `rpow_Pconstructible`). `b = log_2 3` is transcendental (Gelfond-Schneider) | **Curve: no** [Heuristic, see Q2]. **Intersection numbers with line, `exp_two`, rational power law: yes** [Proof] | lines: R; `exp_two`: R; rational `power_law`: R; poly deg >= 2, sine, conic, Bezier: **?** unnamed; box trivial (monotone); arc length and offset: **?** | R for line/exp; ? for the rest; **N: none** |
| Power trendline on a log-x axis (base 2 or 10) | `a 2^{b u}` or `a 10^{b u}` | **Yes** (affine image of `exp_two`, `x`-scale `1/b`, or `1/(b log_2 10)`) | nothing | R |
| Exponential trendline on a log-x axis: Gompertz `a exp(c 2^u)` | `c` = LS slope (sign free), `a` as above | **Curve: no.** Line meets it: log graph meets `exp_two`, R | box: Lambert `W` of a constant, R. Meets sine, poly deg >= 2: ?. No tanh, no logistic | R / ? ; **N: none** |
| `p(2^u)` polynomial trendline on log axis (P3) | rational LS coefficients from rational data; with 2^k abscissae, exact interpolation | no | (see M.md 4.5) | R / ? |
| Linear trendline on log axis | `alpha 2^u + beta` | yes (`exp_two` plus `scale`, `translate`) | nothing | R |

## Q1. Which data are UI-reachable?

**Default chart data sheets** [Measured, `Shapes.AddChart2` then read `ChartData.Workbook`, no edits]:

| Chart type | Default sheet |
|---|---|
| Scatter (all three subtypes) | `X-Values` 0.7, 1.8, 2.6 ; `Y-Values` 2.7, 3.2, 0.8 |
| Bubble | same X, Y; `Size` 10, 4, 8 |
| Line, Line+markers, Column, Bar, Surface | categories "Category 1..4"; Series 1 = 4.3, 2.5, 3.5, 4.5; Series 2 = 2.4, 4.4, 1.8, 2.8; Series 3 = 2, 2, 3, 5 |
| Area, Radar | 5 dates (2002-01-05..09); Series 1 = 32, 32, 28, 12, 15; Series 2 = 12, 12, 12, 21, 28 |
| Stock (HLC) | 5 dates; High 55, 57, 57, 58, 58; Low 11, 12, 13, 11, 35; Close 32, 35, 34, 35, 43 |
| Pie | 1st..4th Qtr = 8.2, 3.2, 1.4, 1.2 |

Trendlines can be added to scatter, bubble, line, column, bar, area and stock (not pie, radar, stacked, surface; P3).
For line, column and bar charts the fit abscissa is the category index 1..n [Heuristic, standard Excel behaviour;
P3 e6 measured the date-serial case]; so only a scatter chart lets the X column be fill-generated.

**Fill-handle rules** [Measured. I called `Range.AutoFill` in the chart's own workbook with each fill type; this is
the engine the fill handle uses, but I did not perform a mouse drag. Direction "fill down"; fill up is the
mirror image, [Heuristic]].

| Seeds | Plain drag (xlFillDefault) | Ctrl-drag / Fill Series (xlFillSeries) | Right-drag "Growth Trend" (xlGrowthTrend) |
|---|---|---|---|
| 1 cell, value `v` | copy `v, v, v...` | `v+1, v+2...` | copy `v` (ratio 1) |
| 2 cells `p, q` | arithmetic, step `q-p` | same | geometric, ratio `q/p`: (2,3) gives 4.5, 6.75, 10.125 |
| >= 3 cells | **least-squares line extrapolated** (not the last step): (1,2,4) gives 5.333, 6.833, 8.333; default scatter X (0.7, 1.8, 2.6) gives 3.6, 4.55, 5.5 | same | **exponential LS (LOGEST) extrapolated**: (1,2,4) gives 8, 16, 32; (0.7, 1.8, 2.6) gives 5.51641087106..., 10.63149..., 20.48952... |

Copy-only fills (`xlFillCopy`) repeat the block. Nothing else is needed. The Series dialog's step box is typed
input and so does not count (a growth step other than the one implied by the seeds is therefore out).

**Closed forms** [Wolfram]:
- Linear fill with `k` seeds `y_1..y_k`: the `m`-th extrapolated value is `ybar + beta (m - (k+1)/2)`, rational.
- Growth-trend fill with 3 seeds, 4th value: `y1^(-2/3) y2^(1/3) y3^(4/3)`. For the default scatter X this is
  `0.7^(-2/3) 1.8^(1/3) 2.6^(4/3) = 5.51641087106102367034...`, equal to the measured 5.51641087106103 to the
  15 digits PowerPoint gives. So growth fills put **algebraic** (rational-power-of-rational) numbers in the sheet.
  They are P-constructible by `rpow_Pconstructible`.

**Reachable datasets.** Start from the table above; repeatedly (1) take any contiguous block of cells as seeds,
(2) fill by one of the rules, (3) clear cells (a blank `y` is skipped by the trendline; a blank `x` in a scatter
as well), (4) copy cells. Every entry is a positive-or-negative algebraic number, in fact a product of rational
powers of earlier entries. Integers are cheap: two seeds `(2,3)` give 4, 5, ...; `(2,3)` filled upward gives 1, 0,
-1; `(1,2)` with Growth Trend gives 4, 8, 16. Typing is not available, so the set is not all of `Q`, but it contains
every integer progression, every `(a, a r, a r^2, ...)` with `r` a ratio of two existing cells, and the 1/10-grid
of the defaults.

**Least-squares formulas** [Proof; checked by Wolfram]. For `n` points with `x_i, y_i > 0`:

- power: `b = (n sum lx ly - sum lx sum ly) / (n sum lx^2 - (sum lx)^2)`, `ln a = mean ly - b mean lx`
  (`lx = ln x_i`, `ly = ln y_i`);
- exponential: `b = (n sum x ly - sum x sum ly) / (n sum x^2 - (sum x)^2)`, `r = e^b`, `ln a = mean ly - b mean x`.

So `b` is a ratio of two quadratic (or bilinear) forms in the logarithms of the data, with rational coefficients.
If `x` are integers and `y` rational, `b` lies in `Q(ln p : p prime)`.

Typical cases, each checked in Wolfram to >= 20 digits against a direct LS fit:

| Data | `b` | value |
|---|---|---|
| Default scatter (3 rows), power | `b = (3 sum lx ly - ...)/...`, 3-point LS | -0.70767731035901569532... (PowerPoint's trendline matches to 0.73 px); `a = 2.5201920459752863094...` |
| Default scatter, exponential | `b = -0.592179059457419826...`, `r = 0.553120687722955469...`, `a = 5.2128361708026144919...` | measured trendline 0.74 px |
| Two rows `(x1,y1),(x2,y2)` (clear the rest) | `b = ln(y2/y1)/ln(x2/x1)` | e.g. `x=(1,2)`, `y=(2,6)` gives `log_2 3` |
| `x = 1,2,4,8` (growth fill), `y = 1,2,3,4` (linear fill) | `b = 1/2 + log_2(3)/10` [Wolfram, difference 0 symbolically] | 0.65849625007211561814537389... |
| line chart `x = 1..4`, `y = 2 (3/2)^(k-1)` (growth fill of (2,3)) | `b = (L3-L2)(10 L2 + 2 L3)/(11 L2^2 - 6 L2 L3 + 3 L3^2)`, `L2 = ln 2`, `L3 = ln 3` | 0.85347313332917533420600773145937... (matches a direct LS fit to 25 digits) |
| `x = 1,2,4`, `y = 1,3,9` | `b = log_2 3` exactly | 1.58496250072115618... |

## Q2. Are the exponents/coefficients P-constructible, and is the curve already derivable?

**Numbers: yes** [Proof from existing lemmas]. `ln` of a positive P-constructible is P-constructible
(`log_Pconstructible`); the LS formulas are rational functions of such logs, and `PConstructible` is closed under
`+ - * /`. `a = e^w` with `w` P-constructible equals `2^(w / ln 2)`, P-constructible by `rpow_two_Pconstructible`;
`r = e^b` likewise. For growth-filled data the entries are `rpow` of rationals, so they are P-constructible too.
`b = log_2 3` is also transcendental by Gelfond-Schneider (if `b` were algebraic irrational, `2^b = 3` would be
transcendental) [Proof]. P-constructibility does not need algebraicity (that is the point of `exp_two`).

**Exponential trendline `y = a r^x`: derivable, [Proof].** `r^x = 2^(x log_2 r)`. With `c = log_2 r != 0`
P-constructible, `scale_x` by `1/c` carries `y = 2^x` to `y = 2^(c x)`, and `scale_y` by `a` gives `y = a r^x`
(`exp_PConstructibleCurve` already does this for `e^x`). `r = 1` is a horizontal line (`translate_y` of the
x-axis, or `poly_graph`). No new constructor.

**Power trendline `y = a x^b`, `b` irrational: no composition, so the curve is not an affine image of a base
curve** [Heuristic]. In the coordinates `(u, v) = (log_2 x, log_2 y)` it is the line `v = b u + log_2 a`, i.e.
it is the parametric curve `(2^t, a 2^{b t})`. The class has no operation that applies `exp` to one coordinate of
another curve, only affine maps, integer-degree rotations, crops, arc/offset constructions. An affine image of
a base curve is algebraic (ellipse, rectangle, `poly_graph`, rational `power_law`, Bezier) or the affine image
of the graph of an entire function (`exp_two`, `sine`); `y = x^b` with `b` irrational is neither, because it has
a branch point at `x = 0` and is not algebraic. The arc-length and offset constructors could in principle
produce it, but nothing suggests they do. I found no derivation and did not prove an impossibility;
treat "not derivable as a curve" as [Heuristic].

**Intersection numbers with the power curve are a different matter** [Proof]. Put `x = 2^s`: the power curve
becomes `y = a 2^{b s}`, which *is* an affine image of `exp_two`. For any curve `C` that is an affine image of
`exp_two` or a line in the right coordinates, `power ∩ C` equals `(2^s, ...)` where `s` is the abscissa of an
intersection of two existing curves:

- line `y = m x + c`: `a 2^{b s} = m 2^s + c`: intersection of `y = a 2^{bs}` and `y = m 2^s + c`, both affine
  images of `exp_two`. [Wolfram: `x^{log_2 3} = x + 2` has the root `x0 = 2.6298027661121326449...` with
  `s0 = 1.3949546021707538761...`; `s0` is the abscissa of `3^s = 2^s + 2`, residual 0 to 43 digits; the `x`
  coordinate is `2^{s0}`, P-constructible by `rpow_two_Pconstructible`.] The same step works for every `b`.
- `exp_two` (or any `p r^x + q`): `a x^b = 2^x`: `ln a + b ln x = x ln 2`, a log graph meets a line. R.
- rational `power_law`: `x^{b - b'} = const`, `rpow`. R.
- two power curves, one translated: `(x - x0)^b = (x - x1)^{b'}` no longer linearises. ?

So against lines, `exp_two` and rational power laws the new curve produces nothing new. This matches M.md
4.5's verdict for `a exp(k 2^u)`: the chart curves reduce, for lines, to R classes.

**The log-x versions.** `y = a x^b` on a log-2 axis is `a 2^{b u}`: **derivable** (not new). `y = a e^{b x}` on a
log-2 axis is `a exp(b 2^u)`, the Gompertz-shaped curve: **not derivable** [Heuristic], though with `w = b 2^u`
it is `y = a e^w` and `u = log_2 (w / b)`, so it is `exp_PConstructibleCurve` with the *abscissa* replaced by
`log_2 (ln(y/a)/b)`; no operation composes curves. `p(2^u)` likewise. These are the curves P3 listed, now
with the LS parameters known to be P-constructible (data-determined, any sign of `c`).

## Q3. What does each new curve unlock?

Classes follow M.md section 3 (R reachable, N named new, E elementary, ? unnamed new).

**Power curve `y = a x^b`, `b = log_2 3` (equivalently the curve `(2^t, 3^t)`; `a = 1`).**

| operation | result |
|---|---|
| line | `3^s = m 2^s + c`: R (two `exp_two` images), [Wolfram example above]. The line through `(2,3)` and `(4,9)` is `y = 3x - 3`; it meets the curve exactly at `x=2, 4` (roots `s = 1, 2`) [Wolfram `NSolve` on `3^s = 3 2^s - 3`, convex so only two]. Rational points `(2^k, 3^k)` lie on the curve for every integer `k`. |
| `exp_two`, rational `power_law` | R |
| poly graph of degree `d >= 2` | `a 2^{b s} = sum p_j 2^{j s}`: an exponential polynomial with `d + 1` incommensurate frequencies `ln 2 {b, 0, 1, ..., d}`. For rational `b` this is algebraic (and already reachable); for irrational `b` it is **?**, no name |
| sine, ellipse, Bezier | `a x^b = sin x`, `x^{2b} + ... = r^2`: **?** |
| box | monotone, trivial (asymptotes); with `restrict` the end points |
| arc length | `integral sqrt(1 + a^2 b^2 x^{2b-2}) dx` hypergeometric; for `b` irrational not elementary, **?** [Open] |
| offset / offset inversion | **?** [Open] |
| tangency | if `sin x = a x^b` were tangent: `tan x = x / b`, i.e. T1 with arbitrary `lambda = 1/b`. The class has **no tangency operation**, and the box of an affine image does not produce one for two different curves; so this is not reachable [Heuristic] |

Named problems: none of tan x = x, `x tan x = Bi`, cantilever beam, goat, inverse involute. T1-T6 need the
tangent function or `gd`. The power curve gives only exponential-polynomial classes.

**Exponential `a r^x`: nothing new** (derivable; `exp_two`'s classes only).

**Gompertz `y = a exp(c 2^u)`** [Proof/Wolfram]:
- line: `c 2^u = ln((m u + n)/a)`: `exp_two` meets a (log of affine) graph. R. [Wolfram: `u0 = 1.2116501963315995428743...` for
  `a=3, c=-1/2, y=(2u+7)/10`; both forms satisfied to 39 digits.]
- box: tangent slope `s`: `a c ln 2 2^u exp(c 2^u) = s`, i.e. `w e^w = s/(a ln 2)` with `w = c 2^u`:
  `w = W(s / (a ln 2))`, a Lambert-`W` of a constant, which `exp_two ∩ hyperbola` already reaches. [Wolfram: root
  `w0 = 0.24974608021537258690...` for `s = 2/3`, `a = 3`, check 0.66666... exact.] R.
- `exp_two`: `a exp(c 2^u) = 2^u`: Lambert, R. Rational `power_law`: log vs `exp_two`, R.
- sine, poly deg >= 2: **?**.
- **tanh/logistic: no.** `tanh u = 1 - 2/(1 + z)` with `z = e^{2u}` (and the logistic `1/(1 + e^{-u})`) has a
  *shifted reciprocal* of the exponential; the Gompertz curve is `a exp(c z)`, a different function; the Gompertz
  sigmoid is the Gumbel CDF, not the logistic CDF. The beam equation `sin x = tanh x` ⇔ `cos x cosh x = +-1`
  needs `cos x (1 + e^{2x}) = -2 e^x`, a product of the sine with an exponential; the class has no curve `cos x * e^{2x}`,
  and `a exp(c 2^u)` has no `e^{+x}` and `e^{-x}` pair. No help for the cantilever beam. [Proof, by comparing function
  classes; same argument as P3 for the polynomial-in-`2^u` family.]
- arc length `integral sqrt(1 + (a c ln 2 2^u e^{c 2^u})^2) du`: **?**.

**Any "transcendence-flavoured" numbers?** The new curve gives exact rational points `(2^k, 3^k)`, and its
intersection coordinates are `2^s` with `s` a root of `a 3^s = m 2^s + c`: positive real roots of two-base
exponential polynomials. These are in the class already (via exp_two images). I know of no named constant they
describe, and I did not find a point where they would give a Gelfond-Schneider-type new transcendence statement.
`log_2 3` itself is a transcendental number the class already contains. [Open: whether 3^{log_2 3} is transcendental; I do not
know the answer, and it plays no role.]

## Q4. Idealization

[Measured] I checked one case of the renderer with an irrational exponent. `Chart.Export(file,"SVG")` of a
scatter chart with the data `x=(1,2,4)`, `y=(1,3,9)` (exact `y = x^{log_2 3}`) and a Power trendline:
the dashed polyline has 741 vertices over `x` in `[1.010, 4.003]` and agrees with `x^{1.58496250072}` to a maximum
of 1.09 px and rms 0.43 px (numpy fit, so the LS exponent is the one computed above). Exponential on
`(0,1,2,3)`, `(1,3,9,27)`: 0.98 px max, 0.46 rms against `3^x`. Default scatter data: power 0.73 px max, 0.30 rms
(`b = -0.7077`); exponential 0.74 px, 0.31 rms. These agree with P3's 0.8 to 1.0 px. So irrational exponents
render like the others: **category (a)**, the same precedent as the other trendlines. Window: the polyline spans
exactly `[min x, max x]` of the data unless Forecast periods are added (Forecast is spinner/arrow input, but
`restrict` does the same job).

## Other things noticed

1. **The log-log duality** is the useful structural fact: under `x = 2^s` the power curve becomes an exponential
   and its intersections with `exp`-type curves go to `exp ∩ exp`. A full log-log chart would turn power curves
   into straight lines, but the UI offers a log axis only on x (memory), so that is a statement about the
   mathematics, not a chart the UI can draw.
2. **Growth Trend fills a sheet with algebraic non-rational values** (rational powers of rationals), such as
   `5.5164...` above. They are P-constructible, but outside `Q`. So LS exponents such as `b = 1/2 + log_2(3)/10` come
   from *rational* data, and the data can be non-rational on top of that.
3. **Two reachable data points give any `log_a b`**, by clearing the rest of a scatter table. Any rational pair
   `(x1,y1),(x2,y2)` of reachable cells gives the exponent exactly (the trendline passes through both points). So
   `b` ranges over `{ln(y2/y1)/ln(x2/x1)}`, a countable set of transcendental numbers, and the curve passes through
   the two data points.
4. **Line charts use category indices**, so the clearing trick (blank `y`) leaves `x` in `{1..n}`; scatter is needed
   for free `x`.
5. **The default linear fill with 3 or more seeds is a least-squares extrapolation**, not "continue the last step".
   Worth knowing for any later probe that uses the fill handle on the default columns.
6. **PowerPoint instance.** There was no `PPT-UI.lock` at the start. While I worked, the instance with the
   AutoRecovered presentation from P3 disappeared and a fresh `Presentation1` (1 slide, Saved) appeared. I did not
   create or close it. Everything I opened I closed. Chart rendering is racy: the first SVG export of a fresh chart
   sometimes lacks the series and trendline; retrying a whole new chart fixes it (f2.py does this).
