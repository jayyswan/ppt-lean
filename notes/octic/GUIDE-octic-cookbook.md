# How to construct a real root of an octic

You have an octic `q(X) = X⁸ + a₇X⁷ + … + a₀` (divide by the leading coefficient first) and
want to construct one of its real roots `x`.

**What you construct:**

- **SOLVE6** — a real root of a polynomial of degree ≤ 6 (square roots included);
- **CROSS** — one crossing of two curves, once per octic;
- arithmetic (`+ − × ÷`) on numbers already constructed.

**What you work out on paper or in a spreadsheet:** the coefficients of those equations.
**What Wolfram Alpha is for:** the approximate roots of `q` (Step 0), and the approximate
roots of each equation so you know which root to take.

The shape is always the same: a few SOLVE6 steps give a polynomial `φ`; one CROSS gives
`y = φ(x)`; one last SOLVE6 gives `x`.

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

The **starting polynomials** are the centred powers

    m_j = Xʲ − s_j/8,     s_j = r₁ʲ + … + r₈ʲ,     j = 1, …, 7.

(Every bracket is in fact an exact fraction in the coefficients of `q`, because the `s_j` are;
the approximate roots are only a quick way to evaluate it.)

## Case A (2 or 4 real roots)

**A1. Orthogonalise.** Work through `m₁, m₂, m₃, …` in order:

    g₁ = m₁,                                             d₁ = ⟨g₁²⟩
    g_k = m_k − Σ_{i<k} ( ⟨m_k g_i⟩ / d_i )·g_i,         d_k = ⟨g_k²⟩

Stop as soon as two of the `d`'s are negative and two are positive. Call the negative ones
`g_a, g_b` and the positive ones `g_c, g_d`. (If some `d_k` comes out 0, set that `m_k` aside
and come back to it after the others.)

**A2. SOLVE6 (two square roots).** `t = √(−d_a/d_c)`, `t′ = √(−d_b/d_d)`.

**A3.** `P = g_a + t·g_c`, `R = g_b + t′·g_d`.

**A4. SOLVE6 (cubic).** `τ` = a real root of

    ⟨R³⟩τ³ + 3⟨P R²⟩τ² + 3⟨P² R⟩τ + ⟨P³⟩ = 0.

**A5.** `φ = P + τ·R`. Go to **Finish**.

## Case B (6 real roots)

**B1. Orthogonalise** as in A1, through all of `m₁, …, m₇`. Exactly one `d` is negative: call
its polynomial `g_a`. Pick two with positive `d`: `g_c`, `g_d`.

**B2. SOLVE6 (square root).** `t = √(−d_a/d_c)`.

**B3.** Form

    U = d_c·(g_a − t·g_c),      V = −2·t·d_c·g_d,      W = d_d·(g_a + t·g_c).

**B4. SOLVE6 (sextic).** `m` = a real root of `Ψ₆m⁶ + Ψ₅m⁵ + … + Ψ₀ = 0`, where

    Ψ₀ = ⟨U³⟩             Ψ₁ = 3⟨U²V⟩             Ψ₂ = 3⟨U²W⟩ + 3⟨UV²⟩
    Ψ₃ = ⟨V³⟩ + 6⟨UVW⟩    Ψ₄ = 3⟨V²W⟩ + 3⟨UW²⟩    Ψ₅ = 3⟨VW²⟩           Ψ₆ = ⟨W³⟩

Put the sextic into Alpha. If it has no real root, go back to B1 and pick a different `g_c`,
`g_d` (swapping the two also counts as different).

**B5.** `φ = U + m·V + m²·W`. Go to **Finish**.

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

- If `φ` has degree ≤ 6: `x` is a root of `φ(X) = y`. Alpha lists its real roots; yours is the
  one equal to your approximate `x`.
- If `φ` has degree 7: divide `q(X)` by `φ(X) − y` (one long division; the quotient is linear).
  The remainder has degree ≤ 6 and `x` is one of its roots.

## Case C (8 real roots)

If `q` has only even powers and an `X` term, it is already reduced: take `φ = X` and go to C7.

Take `a = m₁, b = m₂, g = m₃, w₁ = m₄, w₂ = m₅, w₃ = m₆`.

**C1. SOLVE6 (cubic).** `λ` = a real root of `⟨b³⟩λ³ + 3⟨ab²⟩λ² + 3⟨a²b⟩λ + ⟨a³⟩ = 0`.
Put `P = a + λ·b`.

**C2.** CHECK `⟨P²g⟩ ≠ 0`. For `j = 1, 2, 3` put `W_j = w_j − ( ⟨P²w_j⟩ / ⟨P²g⟩ )·g`.

**C3. SOLVE6 (quadratic).** `ξ` = a real root of `⟨P W₂²⟩ξ² + 2⟨P W₁W₂⟩ξ + ⟨P W₁²⟩ = 0`.
Put `q₀ = W₁ + ξ·W₂`.

**C4.** With `A = ⟨P W₁²⟩`, `B = ⟨P W₁W₃⟩`, `C = ⟨P W₃²⟩`, `E₁ = ⟨P q₀W₁⟩`, `E₀ = ⟨P q₀W₃⟩`, form

    U = C·q₀ − 2E₀·W₃,      V = 2B·q₀ − 2E₀·W₁ − 2E₁·W₃,      W = A·q₀ − 2E₁·W₁.

**C5. SOLVE6 (sextic).** `μ` = a real root of the sextic with the coefficients `Ψ₀, …, Ψ₆` of
step B4, computed from these `U, V, W`. Put `v = U + μ·V + μ²·W`.

**C6. SOLVE6 (quintic).** `κ` = a real root of

    ⟨v⁵⟩κ⁵ + 5⟨P v⁴⟩κ⁴ + 10⟨P²v³⟩κ³ + 10⟨P³v²⟩κ² + 5⟨P⁴v⟩κ + ⟨P⁵⟩ = 0.

Put `φ = P + κ·v`. CHECK: the eight values `φ(rᵢ)` are all different.

If a step has no real root or a CHECK fails, try another root of an earlier step; if that
does not help, shuffle which of `m₁, …, m₆` plays which role (swap `g` and `w₁` first).

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

**C9. SOLVE6 (square root).** `y = √X` if `y₀ > 0`, `y = −√X` if `y₀ < 0`.

**C10. SOLVE6: recover x.** As F3.

## Worked example (Case A): q = X⁸ + X⁷ − 2X⁵ + 3X⁴ + X² − X − 2

Alpha gives the roots `−0.67337`, `0.93408`, `0.86217 ± 0.78650i`, `−0.18648 ± 0.86419i`,
`−1.30604 ± 1.13199i`: two real roots, Case A.

| Step | Result |
|---|---|
| A1 | `d₁ = 0.875`, `d₂ = −49.1429`, `d₃ = −62.7936`, `d₄ = 44.8999`. Negative: `g₂, g₃`. Positive: `g₁, g₄`. |
| A2 | `t = √(49.1429/0.875) = 7.494215`, `t′ = √(62.7936/44.8999) = 1.182593` |
| A3 | `P = g₂ + t·g₁ = 0.079634 + 1.637073X + X²` |
| | `R = g₃ + t′·g₄ = 1.632744 + 2.131802X + 1.700834X² + 1.967655X³ + 1.182593X⁴` |
| A4 | `550.621τ³ − 330.766τ² − 303.349τ − 35.950 = 0`, take `τ = −0.386965` |
| A5 | `φ = P + τR`; after dividing by its largest coefficient, `φ = −0.679908 + X + 0.420909X² − 0.937540X³ − 0.563477X⁴` |
| F1 | `p₄ = 132.4580`, `p₅ = 376.0428`, `p₆ = −564.2740`, `p₇ = −1558.3281`, `p₈ = 3698.2738` |
| | `y⁸ = 33.1145y⁴ + 75.2086y³ − 94.0457y² − 222.6183y − 86.0008` |
| F2 | for `x ≈ 0.93408`: `y₀ = φ(0.93408) = −0.57162 < 0`, so cross `Y = X⁸` with `Y = 33.1145X⁴ − 75.2086X³ − 94.0457X² + 222.6183X − 86.0008` near `X = 0.57162`; `y = −0.571623` |
| F3 | `φ` has degree 4: solve `φ(X) = −0.571623`. Real roots `0.104809` and `0.934080`; `x = 0.934080` |

(Multiplying `φ` by a constant is harmless and keeps the numbers readable.)

So this root costs: two square roots, a cubic, one crossing, a quartic.

## Things to know

- **`python3 octic_byhand.py a8 a7 … a0`** carries out exactly these steps and prints every
  intermediate number, so you can check your arithmetic against it. `python3 octic_byhand.py test`
  ran the procedure on 150 random octics (60 A, 60 B, 30 C); every real root was constructed.
- **Case A always works.** In Cases B and C some steps say "if there is no real root, pick
  differently". In the tests a working choice always existed (Case C: the first choice in 27 of
  30), but that is experience, not a theorem.
- **This is not literally the Lean proof's route.** The proof finds its starting polynomials
  differently and recovers `x` through the degree-7 theorem. What is the same is what makes it
  correct: `φ` satisfies the three bracket conditions (the CHECK in F1 or C7), which is what
  gives the reduced equation, and `x` is a root of the polynomial in the last step. If you get
  stuck in B or C, the proof's own choices are in `GUIDE-octic-construction.md`.
- **Precision.** Brackets of high powers magnify rounding errors. Carry at least 10 significant
  digits in the roots; the CHECKs tell you if you have lost too many.
- **Drawing the quartic graph** for the crossing: `GUIDE-octic-construction.md` §9.
