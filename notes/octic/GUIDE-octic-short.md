# Constructing a real root of an octic: the short version

**Given:** an octic `q(X)` with constructible coefficients and a real root `x` of it.
**Allowed:** arithmetic (`+ − × ÷`), and one primitive:

> **SOLVE6** — find a real root of a polynomial of degree ≤ 6 with constructible coefficients.

Square roots, cubics, quartics, quintics and sextics are all SOLVE6.

The explicit formulas for every step are in `GUIDE-octic-construction.md`; the script
`octic_construct.py` runs them on seven examples.

## The idea

An octic cannot be solved by SOLVE6 alone. But a change of variable `y = φ(x)` turns it into
a *reduced* octic, whose root can be read off a single curve crossing. So:

1. **Change variable.** Find a polynomial `φ` of degree ≤ 7 such that `y = φ(x)` satisfies a
   reduced equation. Finding `φ` costs a few SOLVE6 calls (table below).
2. **One crossing.** Read `y` off the picture.
3. **Recover `x`.** Run Euclid's algorithm on `q(X)` and `φ(X) − y`. The last remainder is
   linear, `r₁X + r₀`, and `x = −r₀ / r₁`. This is arithmetic only.

## Which case you are in

First divide out any repeated roots (`gcd(q, q′)`); the factors then have degree ≤ 7. Otherwise
count the real roots of `q`:

| Roots of `q` | SOLVE6 calls to find `φ` | Reduced equation | The crossing |
|---|---|---|---|
| 2 or 4 real (two or more complex pairs) | quadratic, quadratic, cubic | `y⁸ = quartic(y)` | `Y = X⁸` meets a quartic graph |
| 6 real (one complex pair) | quadratic, sextic | `y⁸ = quartic(y)` | `Y = X⁸` meets a quartic graph |
| 8 real | cubic, quadratic, sextic, quintic | `Q(y²) = c·y`, `Q` a quartic | a quartic graph meets `Y = c·√X`; then `y = ±√X` |

What the calls are for:

- **Complex roots present.** `φ` must satisfy three conditions: the sums of `φ(r)`, `φ(r)²`
  and `φ(r)³` over the roots `r` of `q` are all zero. The first is linear (free). The second is
  a quadratic condition: one quadratic gives a first solution. The third is a cubic condition,
  met either by a second quadratic and a cubic (two or more pairs), or by a sextic (one pair).
  These three conditions are exactly what removes the `y⁷`, `y⁶`, `y⁵` terms.
- **All roots real.** Here the conditions are that the sums of `φ(r)`, `φ(r)³`, `φ(r)⁵` are
  zero, which removes the `y⁷`, `y⁵`, `y³` terms. The four calls impose them one at a time.

## Three things to be honest about

- **You need approximate roots of `q` first.** They are used only to decide the case, to pick
  rational starting values, and to know which crossing is yours. No approximate number enters
  the construction itself.
- **Step 3 is a shortcut that the Lean proof does not use.** It works when `φ(x)` differs from
  `φ` at the other seven roots. That always holds in the 8-real case, and held at every root of
  every example we ran in the other cases, but is not proved there. If it fails, `x` is a root
  of `φ(X) − y`, of degree ≤ 7, and the same three steps apply one degree down (reduced
  equation `y⁷ = cubic(y)`, one crossing, then SOLVE6).
- **The crossing is new.** Step 2 is the one place where SOLVE6 is not enough.

## Example: `X⁸ − X − 1`

Two real roots, three complex pairs: first row of the table. Two quadratics and a cubic give

    φ ≈ 0.538 + 0.035X − 0.019X² + 0.714X³ − 0.154X⁴ + 0.124X⁵ − 0.101X⁶ − 0.615X⁷

and `y = φ(x)` satisfies

    y⁸ = −3.858y⁴ + 1.825y³ − 0.324y² + 0.026y − 0.001.

Cross `Y = X⁸` with that quartic to read `y`; Euclid on `q` and `φ − y` then returns `x`
(≈ 1.0970 or ≈ −0.8117, depending on which crossing was read).
