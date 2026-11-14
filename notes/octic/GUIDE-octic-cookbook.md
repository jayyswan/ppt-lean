# How to construct a real root of an octic

You have an octic `q(X) = X⁸ + a₇X⁷ + … + a₀` (divide by the leading coefficient first) and
want to construct one of its real roots `x`.

**What you construct:**

- **arithmetic** — `+ − × ÷`, powers and roots (so square roots and the quadratic formula
  are arithmetic) on numbers already constructed;
- **SOLVE6** — a real root of a polynomial of degree 3 to 6;
- **CROSS** — one crossing of two curves, once per octic.

**What you work out on paper or in a spreadsheet:** the coefficients of those equations.
**What Wolfram Alpha is for:** the approximate roots of `q` (Step 0), and the approximate
roots of each equation so you know which root to take.

**There is no trial and error.** Every choice below is forced: where an equation has several
real roots, the text says which one to take (any one, or the one nearest a given number).

The shape is always the same: arithmetic and one to three SOLVE6 steps give a polynomial `φ`;
one CROSS gives `y = φ(x)`; one last SOLVE6 gives `x`.

| Case | SOLVE6 steps to find `φ` | CROSS | Last step |
|---|---|---|---|
| A (2 or 4 real roots) | a cubic | `Y = X⁸` against a quartic | one SOLVE6 |
| B (6 real roots) | a sextic | `Y = X⁸` against a quartic | one SOLVE6 |
| C (8 real roots) | a cubic, a sextic, a quintic | a quartic against `Y = c·√X` | one SOLVE6 |

## Step 0. Alpha: roots and case

Type `q` into Alpha.

- If Alpha factors it, your root belongs to a factor of lower degree; this guide is for an
  octic that does not factor.
- Write down the eight approximate roots `r₁, …, r₈`, to as many digits as you can get.
- Count the real ones:

| Real roots | Case |
|---|---|
| 2 or 4 | **A** |
| 6 | **B** |
| 8 | **C** |

## Step 1. The value table and the bracket

Every polynomial `u` in this guide is recorded two ways: its coefficients, and its **value
column** `u(r₁), …, u(r₈)`. Adding polynomials adds their columns.

The **bracket** of one or more polynomials is the sum, over the eight rows, of the product
of their values:

    ⟨u⟩ = Σᵢ u(rᵢ),     ⟨uv⟩ = Σᵢ u(rᵢ)·v(rᵢ),     ⟨u²v⟩ = Σᵢ u(rᵢ)²·v(rᵢ),   and so on.

Complex roots come in conjugate pairs and so do the values, so a pair contributes twice the
real part of its product. Every bracket is a real number.
(Every bracket is in fact an exact fraction in the coefficients of `q`; the approximate roots
are only a quick way to evaluate it.)

## Cases A and B: two preparations

Write the nonreal roots as conjugate pairs `z = α + βi` (`β > 0`).

**N1. A pair vector `e` for each pair.**

1. Divide `q` by `X² − 2αX + (α² + β²)` (long division). The quotient `q₆` has degree 6; the
   remainder should be about 0.
2. Evaluate `q₆(z) = w₁ + w₂i` (Horner, complex arithmetic).
3. `E(X) = (w₁X + βw₂ − αw₁)·q₆(X)`. Then `E(z) = i·s` is purely imaginary (CHECK: real part
   about 0), with `s = β(w₁² + w₂²)`.
4. `e = E / s`.

Now `e` is 0 at the six other roots, `e(z) = i`, and `⟨e²⟩ = −2`. For any polynomial `u`,
`⟨u e⟩ = −2·Im u(z)`.

**N2. Two positive vectors `g_c`, `g_d`.** To **clean** a polynomial `u`, subtract `Im u(z)·e`
for every pair `z` (all pairs, not only the ones you will use); the result has real values at
every root. Then

    m₁ = X − s₁/8,    m₂ = X² − s₂/8        (sⱼ = r₁ʲ + … + r₈ʲ)
    g_c = clean(m₁),    h = clean(m₂),    g_d = h − (⟨h g_c⟩ / ⟨g_c²⟩)·g_c
    d_c = ⟨g_c²⟩,    d_d = ⟨g_d²⟩         (both come out positive)

`e`, `g_c`, `g_d` are mutually orthogonal (`⟨e g_c⟩ = ⟨e g_d⟩ = ⟨g_c g_d⟩ = 0`), and
`⟨e⟩ = ⟨g_c⟩ = ⟨g_d⟩ = 0`.

## Case A (2 or 4 real roots)

Take the pair vectors `e₁`, `e₂` of two different pairs (say the two with the smallest real
part).

**A1. Arithmetic.** `t = √(2/d_c)`, `t′ = √(2/d_d)`.

**A2.** `P = e₁ + t·g_c`, `R = e₂ + t′·g_d`.

**A3. SOLVE6 (cubic).** `τ` = any real root of

    ⟨R³⟩τ³ + 3⟨P R²⟩τ² + 3⟨P² R⟩τ + ⟨P³⟩ = 0.

(A cubic always has one. If ⟨R³⟩ = 0, take `φ = R` and skip A4.)

**A4.** `φ = P + τ·R`. Go to **Finish**.

## Case B (6 real roots)

One pair, vector `e`.

**B1. Arithmetic.** `t = √(2/d_c)`.

**B2.** Form

    U = d_c·(e − t·g_c),      V = −2·t·d_c·g_d,      W = d_d·(e + t·g_c).

**B3. SOLVE6 (sextic).** `m` = any real root of `Ψ₆m⁶ + Ψ₅m⁵ + … + Ψ₀ = 0`, where

    Ψ₀ = ⟨U³⟩             Ψ₁ = 3⟨U²V⟩             Ψ₂ = 3⟨U²W⟩ + 3⟨UV²⟩
    Ψ₃ = ⟨V³⟩ + 6⟨UVW⟩    Ψ₄ = 3⟨V²W⟩ + 3⟨UW²⟩    Ψ₅ = 3⟨VW²⟩           Ψ₆ = ⟨W³⟩

This sextic always has a real root (see "Things to know"). If Ψ₆ = 0, take `φ = W` and skip B4.

**B4.** `φ = U + m·V + m²·W`. Go to **Finish**.

## Finish (Cases A and B)

**F1. Reduced equation.** From the value column `yᵢ = φ(rᵢ)` compute `p_k = Σᵢ yᵢᵏ` for
`k = 1, …, 8`. CHECK: `p₁ = p₂ = p₃ = 0` (up to rounding). Then

    c₄ = p₄/4,   c₃ = p₅/5,   c₂ = p₆/6,   c₁ = p₇/7,   c₀ = p₈/8 − p₄²/32

and `y = φ(x)` satisfies `y⁸ = c₄y⁴ + c₃y³ + c₂y² + c₁y + c₀`.

**F2. CROSS.** Let `y₀ = φ(your approximate x)`.

- `y₀ > 0`: draw `Y = X⁸` and `Y = c₄X⁴ + c₃X³ + c₂X² + c₁X + c₀`. They cross at `X = y`.
- `y₀ < 0`: draw `Y = X⁸` and `Y = c₄X⁴ − c₃X³ + c₂X² − c₁X + c₀`. They cross at `X = −y`.

The curves may cross more than once; yours is the crossing at `X = |y₀|`. Restrict to an
interval around it containing no other crossing.

**F3. SOLVE6: recover x.**

- If `φ` has degree ≤ 6: `x` is a root of `φ(X) = y`. (Degree 1 or 2 is arithmetic.) Alpha lists its real roots; yours is the
  one equal to your approximate `x`.
- If `φ` has degree 7: divide `q(X)` by `φ(X) − y` (one long division; the quotient is linear).
  The remainder has degree ≤ 6 and `x` is one of its roots.

## Case C (8 real roots)

If `q` has only even powers and an `X` term, it is already reduced: take `φ = X` and go to C7.

**C0. Six seed polynomials.** Label the roots `r₁, …, r₈` in any order.

1. For each `i`, divide `q(X)` by `X − rᵢ` (synthetic division; the quotient has degree 7) and
   divide the quotient by its own value at `rᵢ`. This gives eight polynomials `ℓ₁, …, ℓ₈`:
   `ℓᵢ` is 1 at `rᵢ` and 0 at the other roots.
2. For each row of this table, the seed is `Σᵢ yᵢ·ℓᵢ(X)`, where `y₁, …, y₈` is the row:

| seed | y₁ | y₂ | y₃ | y₄ | y₅ | y₆ | y₇ | y₈ |
|---|---|---|---|---|---|---|---|---|
| `a`  | −4 | −2 | 2 | −1 | 1 | 4 | 1 | −1 |
| `b`  | 0 | 3 | 0 | 2 | 1 | −1 | −6 | 1 |
| `g`  | 1 | −2/3 | 0 | −1 | 1 | 3/2 | 2/3 | −5/2 |
| `w₁` | −143/21 | −113/21 | −22/21 | −452/63 | −18/7 | 170/21 | −24/7 | 1154/63 |
| `w₂` | 38/35 | 29/35 | 1/35 | 137/105 | 96/35 | −44/35 | 156/35 | −193/21 |
| `w₃` | 167/35 | −89/35 | 184/35 | −272/105 | −501/35 | −186/35 | −101/35 | 370/21 |

3. Round each coefficient to 10 decimals, then subtract `⟨seed⟩/8` from the constant term so
   that `⟨seed⟩ = 0`.

(The table is the proof's "centre". If the seeds were exact, the roots found below would be
exactly `0, 5/3, −5322/2915, −1`; rounding moves them slightly. That is why each step says
"nearest".)

**C1. SOLVE6 (cubic).** `λ` = the real root nearest `0` of
`⟨b³⟩λ³ + 3⟨ab²⟩λ² + 3⟨a²b⟩λ + ⟨a³⟩ = 0`. Put `P = a + λ·b`.

**C2.** For `j = 1, 2, 3` put `W_j = w_j − ( ⟨P²w_j⟩ / ⟨P²g⟩ )·g`.

**C3. Arithmetic (quadratic formula).** `ξ` = the real root nearest `5/3` of
`⟨P W₂²⟩ξ² + 2⟨P W₁W₂⟩ξ + ⟨P W₁²⟩ = 0`. Put `q₀ = W₁ + ξ·W₂`.

**C4.** With `A = ⟨P W₁²⟩`, `B = ⟨P W₁W₃⟩`, `C = ⟨P W₃²⟩`, `E₁ = ⟨P q₀W₁⟩`, `E₀ = ⟨P q₀W₃⟩`, form

    U = C·q₀ − 2E₀·W₃,      V = 2B·q₀ − 2E₀·W₁ − 2E₁·W₃,      W = A·q₀ − 2E₁·W₁.

**C5. SOLVE6 (sextic).** `μ` = the real root nearest `−1.8257` (= −5322/2915) of the sextic with the
coefficients `Ψ₀, …, Ψ₆` of step B3, computed from these `U, V, W`. Put

    v = ( U + μ·V + μ²·W ) / ( Aμ² + 2Bμ + C ).

**C6. SOLVE6 (quintic).** `κ` = the real root nearest `−1` of

    ⟨v⁵⟩κ⁵ + 5⟨P v⁴⟩κ⁴ + 10⟨P²v³⟩κ³ + 10⟨P³v²⟩κ² + 5⟨P⁴v⟩κ + ⟨P⁵⟩ = 0.

Put `φ = P + κ·v`.

CHECK: the four roots you took are within 0.001 of `0, 5/3, −1.8257, −1`. If one is not, the
seeds or the roots of `q` are not accurate enough: use more digits (this is the only thing that
can go wrong).

**C7. Reduced equation.** With `yᵢ = φ(rᵢ)` and `p_k = Σᵢ yᵢᵏ` (CHECK: `p₁ = p₃ = p₅ = 0`):

    e₂ = −p₂/2
    e₄ = (−e₂p₂ − p₄)/4
    e₆ = (−e₄p₂ − e₂p₄ − p₆)/6
    e₈ = (−e₆p₂ − e₄p₄ − e₂p₆ − p₈)/8
    c  = p₇/7

and `y = φ(x)` satisfies `Q(y²) = c·y` with `Q(X) = X⁴ + e₂X³ + e₄X² + e₆X + e₈`.

**C8. CROSS.** Let `y₀ = φ(your approximate x)`. Draw `Y = Q(X)` and `Y = c·√X` if `y₀ > 0`,
or `Y = −c·√X` if `y₀ < 0`. Yours is the crossing at `X = y₀²`; restrict to an interval
containing no other.

**C9. Arithmetic.** `y = √X` if `y₀ > 0`, `y = −√X` if `y₀ < 0`.

**C10. SOLVE6: recover x.** As F3.

## Worked example (Case A): q = X⁸ + X⁷ − 2X⁵ + 3X⁴ + X² − X − 2

Alpha gives the roots `−0.67337`, `0.93408`, `0.86217 ± 0.78650i`, `−0.18648 ± 0.86419i`,
`−1.30604 ± 1.13199i`: two real roots, Case A, three pairs.

| Step | Result |
|---|---|
| N1 | three pair vectors, each with `⟨e²⟩ = −2`; the first two (`z = −1.30604 + 1.13199i`, `z = −0.18648 + 0.86419i`) are `e₁`, `e₂` |
| N2 | `d_c = ⟨g_c²⟩ = 6.16862`, `d_d = ⟨g_d²⟩ = 2.24712` |
| A1 | `t = √(2/6.16862) = 0.569405`, `t′ = √(2/2.24712) = 0.943414` |
| A2 | `P = e₁ + t·g_c`, `R = e₂ + t′·g_d` (coefficients below) |
| A3 | `4.17765τ³ + 0.56102τ² − 0.08153τ + 3.97065 = 0`, `τ = −1.036981` |
| A4 | `φ = P + τR`; divided by its largest coefficient, `φ = −0.06759 − 0.12400X − 0.40137X² + X³ − 0.49736X⁴ − 0.28582X⁵ + 0.08493X⁶ + 0.21903X⁷` |
| F1 | `p₄ = −6.28635`, `p₅ = 2.69315`, `p₆ = 3.31914`, `p₇ = −1.13298`, `p₈ = 9.69485` |
| | `y⁸ = −1.57159y⁴ + 0.53863y³ + 0.55319y² − 0.16185y − 0.02309` |
| F2 | for `x ≈ 0.93408`: `y₀ = φ(0.93408) = −0.10819 < 0`, so cross `Y = X⁸` with `Y = −1.57159X⁴ − 0.53863X³ + 0.55319X² + 0.16185X − 0.02309` near `X = 0.10819`; `y = −0.108190` |
| F3 | `φ` has degree 7: divide `q` by `φ(X) − y`; the remainder has degree 6 and real roots `−0.695542` and `0.934080`; `x = 0.934080` |

Coefficients (low to high) used above:

    P = 0.03181 + 0.37194X + 0.04534X² + 0.24761X³ − 0.22205X⁴ − 0.00182X⁵ + 0.13906X⁶ + 0.09740X⁷
    R = 0.10723 + 0.49913X + 0.49832X² − 0.89385X³ + 0.34919X⁴ + 0.32197X⁵ + 0.03791X⁶ − 0.15416X⁷

(Multiplying `φ` by a constant is harmless and keeps the numbers readable.)

So this root costs: one cubic, one crossing and one degree-6 equation; the rest is arithmetic.

## Things to know

- **`python3 octic_byhand.py a8 a7 … a0`** carries out exactly these steps and prints every
  intermediate number, so you can check your arithmetic against it. `python3 octic_byhand.py test`
  ran the procedure on 150 random octics (60 A, 60 B, 30 C); every real root was constructed on
  the first and only try. With the roots of `q` rounded to 7, 9 or 12 decimals the conditions
  `p₁ = p₂ = p₃ = 0` (or `p₁ = p₃ = p₅ = 0`) still held to about the same number of digits.
- **Why no choice is needed.**
  - *Case A:* two isotropic directions `P`, `R` span a plane on which the trace form vanishes, so
    `φ = P + τR` has `Tr φ = Tr φ² = 0` for every `τ`, and `Tr φ³` is a cubic in `τ`.
  - *Case B:* with one pair there is a symmetry of the roots (negate the real-root values and
    conjugate-negate the pair value) that fixes `e` and negates `g_c, g_d`, and it turns `Tr φ³`
    into its negative. Since `U, V, W` lie in span(`e, g_c, g_d`), the sextic takes both
    signs, so it has a real root.
  - *Case C:* this is the proof's own route: for exact seeds the four roots are exactly the
    nominal values, and the seeds are close enough to exact that the roots stay close.
- **The cubic in A3 is sometimes arithmetic too.** When it has only one real root, Cardano's
  formula gives that root with real square and cube roots.
- **The two routes are not literally the Lean proof's** in Cases A and B (the proof picks its
  vectors differently and recovers `x` through the degree-7 theorem); Case C is. What is the same
  is what makes it correct: `φ` satisfies the bracket conditions (the CHECK in F1 or C7), which
  gives the reduced equation, and `x` is a root of the polynomial in the last step. The proof's
  own choices are in `GUIDE-octic-construction.md`.
- **Precision.** Brackets of high powers magnify rounding errors. Carry at least 10 significant
  digits in the roots; the CHECKs tell you if you have lost too many.
- **Drawing the quartic graph** for the crossing: `GUIDE-octic-construction.md` §9.
