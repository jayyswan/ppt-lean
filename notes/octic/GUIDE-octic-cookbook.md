# How to construct a real root of an octic

You have an octic $`q(X) = X^8 + a_7X^7 + \dots + a_0`$ (divide by the leading coefficient first) and
want to construct one of its real roots $`x`$.

**What you construct:**

- **arithmetic** — $`+ \;-\; \times \;\div`$, powers and roots (so square roots and the quadratic formula
  are arithmetic) on numbers already constructed;
- **SOLVE6** — a real root of a polynomial of degree 3 to 6;
- **CROSS** — one crossing of two curves, once per octic.

**What you work out on paper or in a spreadsheet:** the coefficients of those equations.
**What Wolfram Alpha is for:** the approximate roots of $`q`$ (Step 0), and the approximate
roots of each equation so you know which root to take.

The shape is always the same: arithmetic and one to three SOLVE6 steps give a polynomial $`\varphi`$;
one CROSS gives $`y = \varphi(x)`$; one last SOLVE6 gives $`x`$.

| Case | SOLVE6 steps to find $`\varphi`$ | CROSS | Last step |
|---|---|---|---|
| A (2 or 4 real roots) | a cubic | $`Y = X^8`$ against a quartic | one SOLVE6 |
| B (6 real roots) | a sextic | $`Y = X^8`$ against a quartic | one SOLVE6 |
| C (8 real roots) | a cubic, a sextic, a quintic | a quartic against $`Y = c\sqrt{X}`$ | one SOLVE6 |

## Step 0. Alpha: roots and case

Type $`q`$ into Alpha.

- If Alpha factors it, your root belongs to a factor of lower degree; this guide is for an
  octic that does not factor.
- Write down the eight approximate roots $`r_1, \dots, r_8`$, to as many digits as you can get.
- Count the real ones:

| Real roots | Case |
|---|---|
| 2 or 4 | **A** |
| 6 | **B** |
| 8 | **C** |

## Step 1. The value table and the bracket

Every polynomial $`u`$ in this guide is recorded two ways: its coefficients, and its **value
column** $`u(r_1), \dots, u(r_8)`$. Adding polynomials adds their columns.

The **bracket** of one or more polynomials is the sum, over the eight rows, of the product
of their values:

```math
\langle u\rangle = \sum_{i} u(r_i), \qquad
\langle uv\rangle = \sum_{i} u(r_i)\,v(r_i), \qquad
\langle u^2v\rangle = \sum_{i} u(r_i)^2\,v(r_i), \qquad \text{and so on.}
```

Complex roots come in conjugate pairs and so do the values, so a pair contributes twice the
real part of its product. Every bracket is a real number.

The **starting polynomials** are the centred powers

```math
m_j = X^j - \frac{s_j}{8}, \qquad s_j = r_1^j + \dots + r_8^j, \qquad j = 1, \dots, 7.
```

(Every bracket is in fact an exact fraction in the coefficients of $`q`$, because the $`s_j`$ are;
the approximate roots are only a quick way to evaluate it.)

## Case A (2 or 4 real roots)

**A1. Orthogonalise.** Work through $`m_1, m_2, m_3, \dots`$ in order:

```math
\begin{aligned}
g_1 &= m_1, & d_1 &= \langle g_1^2\rangle \\
g_k &= m_k - \sum_{i \lt k} \frac{\langle m_k g_i\rangle}{d_i}\, g_i, & d_k &= \langle g_k^2\rangle
\end{aligned}
```

Stop as soon as two of the $`d`$'s are negative and two are positive. Call the negative ones
$`g_a, g_b`$ and the positive ones $`g_c, g_d`$. (If some $`d_k`$ comes out $`0`$, set that $`m_k`$ aside
and come back to it after the others.)

**A2. Arithmetic.** $`t = \sqrt{-d_a/d_c}`$, $`t' = \sqrt{-d_b/d_d}`$.

**A3.** $`P = g_a + t\,g_c`$, $`R = g_b + t'\,g_d`$.

**A4. SOLVE6 (cubic).** $`\tau`$ = a real root of

```math
\langle R^3\rangle\,\tau^3 + 3\langle P R^2\rangle\,\tau^2 + 3\langle P^2 R\rangle\,\tau + \langle P^3\rangle = 0.
```

**A5.** $`\varphi = P + \tau R`$. Go to **Finish**.

## Case B (6 real roots)

**B1. Orthogonalise** as in A1, through all of $`m_1, \dots, m_7`$. Exactly one $`d`$ is negative: call
its polynomial $`g_a`$. Pick two with positive $`d`$: $`g_c`$, $`g_d`$.

**B2. Arithmetic.** $`t = \sqrt{-d_a/d_c}`$.

**B3.** Form

```math
U = d_c\,(g_a - t\,g_c), \qquad V = -2\,t\,d_c\,g_d, \qquad W = d_d\,(g_a + t\,g_c).
```

**B4. SOLVE6 (sextic).** $`m`$ = a real root of $`\Psi_6 m^6 + \Psi_5 m^5 + \dots + \Psi_0 = 0`$, where

```math
\begin{aligned}
\Psi_0 &= \langle U^3\rangle &
\Psi_1 &= 3\langle U^2V\rangle &
\Psi_2 &= 3\langle U^2W\rangle + 3\langle UV^2\rangle \\
\Psi_3 &= \langle V^3\rangle + 6\langle UVW\rangle &
\Psi_4 &= 3\langle V^2W\rangle + 3\langle UW^2\rangle &
\Psi_5 &= 3\langle VW^2\rangle \\
\Psi_6 &= \langle W^3\rangle
\end{aligned}
```

Put the sextic into Alpha. If it has no real root, go back to B1 and pick a different $`g_c`$,
$`g_d`$ (swapping the two also counts as different).

**B5.** $`\varphi = U + m\,V + m^2 W`$. Go to **Finish**.

## Finish (Cases A and B)

**F1. Reduced equation.** From the value column $`y_i = \varphi(r_i)`$ compute $`p_k = \sum_i y_i^k`$ for
$`k = 1, \dots, 8`$. CHECK: $`p_1 = p_2 = p_3 = 0`$ (up to rounding). Then

```math
c_4 = \frac{p_4}{4}, \quad c_3 = \frac{p_5}{5}, \quad c_2 = \frac{p_6}{6}, \quad c_1 = \frac{p_7}{7}, \quad c_0 = \frac{p_8}{8} - \frac{p_4^2}{32}
```

and $`y = \varphi(x)`$ satisfies $`y^8 = c_4y^4 + c_3y^3 + c_2y^2 + c_1y + c_0`$.

**F2. CROSS.** Let $`y_0 = \varphi(\text{your approximate } x)`$.

- $`y_0 > 0`$: draw $`Y = X^8`$ and $`Y = c_4X^4 + c_3X^3 + c_2X^2 + c_1X + c_0`$. They cross at $`X = y`$.
- $`y_0 < 0`$: draw $`Y = X^8`$ and $`Y = c_4X^4 - c_3X^3 + c_2X^2 - c_1X + c_0`$. They cross at $`X = -y`$.

The curves may cross more than once; yours is the crossing at $`X = |y_0|`$. Restrict to an
interval around it containing no other crossing.

**F3. SOLVE6: recover $`x`$.**

- If $`\varphi`$ has degree $`\le 6`$: $`x`$ is a root of $`\varphi(X) = y`$. (Degree 1 or 2 is arithmetic.) Alpha lists its real roots; yours is the
  one equal to your approximate $`x`$.
- If $`\varphi`$ has degree $`7`$: divide $`q(X)`$ by $`\varphi(X) - y`$ (one long division; the quotient is linear).
  The remainder has degree $`\le 6`$ and $`x`$ is one of its roots.

## Case C (8 real roots)

If $`q`$ has only even powers and an $`X`$ term, it is already reduced: take $`\varphi = X`$ and go to C7.

Take $`a = m_1,\ b = m_2,\ g = m_3,\ w_1 = m_4,\ w_2 = m_5,\ w_3 = m_6`$.

**C1. SOLVE6 (cubic).** $`\lambda`$ = a real root of $`\langle b^3\rangle\lambda^3 + 3\langle ab^2\rangle\lambda^2 + 3\langle a^2b\rangle\lambda + \langle a^3\rangle = 0`$.
Put $`P = a + \lambda b`$.

**C2.** CHECK $`\langle P^2g\rangle \neq 0`$. For $`j = 1, 2, 3`$ put $`W_j = w_j - \dfrac{\langle P^2w_j\rangle}{\langle P^2g\rangle}\, g`$.

**C3. Arithmetic (quadratic formula).** $`\xi`$ = a real root of
$`\langle P W_2^2\rangle\xi^2 + 2\langle P W_1W_2\rangle\xi + \langle P W_1^2\rangle = 0`$. Put $`q_0 = W_1 + \xi W_2`$.

**C4.** With $`A = \langle P W_1^2\rangle`$, $`B = \langle P W_1W_3\rangle`$, $`C = \langle P W_3^2\rangle`$, $`E_1 = \langle P q_0W_1\rangle`$, $`E_0 = \langle P q_0W_3\rangle`$, form

```math
\begin{aligned}
U &= C\,q_0 - 2E_0\,W_3, \\
V &= 2B\,q_0 - 2E_0\,W_1 - 2E_1\,W_3, \\
W &= A\,q_0 - 2E_1\,W_1.
\end{aligned}
```

**C5. SOLVE6 (sextic).** $`\mu`$ = a real root of the sextic with the coefficients $`\Psi_0, \dots, \Psi_6`$ of
step B4, computed from these $`U, V, W`$. Put $`v = U + \mu V + \mu^2 W`$.

**C6. SOLVE6 (quintic).** $`\kappa`$ = a real root of

```math
\langle v^5\rangle\kappa^5 + 5\langle P v^4\rangle\kappa^4 + 10\langle P^2v^3\rangle\kappa^3 + 10\langle P^3v^2\rangle\kappa^2 + 5\langle P^4v\rangle\kappa + \langle P^5\rangle = 0.
```

Put $`\varphi = P + \kappa v`$. CHECK: the eight values $`\varphi(r_i)`$ are all different.

If a step has no real root or a CHECK fails, try another root of an earlier step; if that
does not help, shuffle which of $`m_1, \dots, m_6`$ plays which role (swap $`g`$ and $`w_1`$ first).

**C7. Reduced equation.** With $`y_i = \varphi(r_i)`$ and $`p_k = \sum_i y_i^k`$ (CHECK: $`p_1 = p_3 = p_5 = 0`$):

```math
\begin{aligned}
e_2 &= -\frac{p_2}{2} \\
e_4 &= \frac{-e_2p_2 - p_4}{4} \\
e_6 &= \frac{-e_4p_2 - e_2p_4 - p_6}{6} \\
e_8 &= \frac{-e_6p_2 - e_4p_4 - e_2p_6 - p_8}{8} \\
c &= \frac{p_7}{7}
\end{aligned}
```

and $`y = \varphi(x)`$ satisfies $`Q(y^2) = c\,y`$ with $`Q(X) = X^4 + e_2X^3 + e_4X^2 + e_6X + e_8`$.

**C8. CROSS.** Let $`y_0 = \varphi(\text{your approximate } x)`$. Draw $`Y = Q(X)`$ and $`Y = c\sqrt{X}`$ if $`y_0 > 0`$,
or $`Y = -c\sqrt{X}`$ if $`y_0 < 0`$. Yours is the crossing at $`X = y_0^2`$; restrict to an interval
containing no other.

**C9. Arithmetic.** $`y = \sqrt{X}`$ if $`y_0 > 0`$, $`y = -\sqrt{X}`$ if $`y_0 < 0`$.

**C10. SOLVE6: recover $`x`$.** As F3.

## Worked example (Case A): $`q = X^8 + X^7 - 2X^5 + 3X^4 + X^2 - X - 2`$

Alpha gives the roots $`-0.67337`$, $`0.93408`$, $`0.86217 \pm 0.78650i`$, $`-0.18648 \pm 0.86419i`$,
$`-1.30604 \pm 1.13199i`$: two real roots, Case A.

| Step | Result |
|---|---|
| A1 | $`d_1 = 0.875`$, $`d_2 = -49.1429`$, $`d_3 = -62.7936`$, $`d_4 = 44.8999`$. Negative: $`g_2, g_3`$. Positive: $`g_1, g_4`$. |
| A2 | $`t = \sqrt{49.1429/0.875} = 7.494215`$, $`t' = \sqrt{62.7936/44.8999} = 1.182593`$ |
| A3 | $`P = g_2 + t\,g_1 = 0.079634 + 1.637073X + X^2`$ |
| | $`R = g_3 + t'\,g_4 = 1.632744 + 2.131802X + 1.700834X^2 + 1.967655X^3 + 1.182593X^4`$ |
| A4 | $`550.621\tau^3 - 330.766\tau^2 - 303.349\tau - 35.950 = 0`$, take $`\tau = -0.386965`$ |
| A5 | $`\varphi = P + \tau R`$; after dividing by its largest coefficient, $`\varphi = -0.679908 + X + 0.420909X^2 - 0.937540X^3 - 0.563477X^4`$ |
| F1 | $`p_4 = 132.4580`$, $`p_5 = 376.0428`$, $`p_6 = -564.2740`$, $`p_7 = -1558.3281`$, $`p_8 = 3698.2738`$ |
| | $`y^8 = 33.1145y^4 + 75.2086y^3 - 94.0457y^2 - 222.6183y - 86.0008`$ |
| F2 | for $`x \approx 0.93408`$: $`y_0 = \varphi(0.93408) = -0.57162 < 0`$, so cross $`Y = X^8`$ with $`Y = 33.1145X^4 - 75.2086X^3 - 94.0457X^2 + 222.6183X - 86.0008`$ near $`X = 0.57162`$; $`y = -0.571623`$ |
| F3 | $`\varphi`$ has degree 4: solve $`\varphi(X) = -0.571623`$. Real roots $`0.104809`$ and $`0.934080`$; $`x = 0.934080`$ |

(Multiplying $`\varphi`$ by a constant is harmless and keeps the numbers readable.)

So this root costs: one cubic, one crossing and one quartic; the rest is arithmetic.

## Things to know

- **`python3 octic_byhand.py a8 a7 … a0`** carries out exactly these steps and prints every
  intermediate number, so you can check your arithmetic against it. `python3 octic_byhand.py test`
  ran the procedure on 150 random octics (60 A, 60 B, 30 C); every real root was constructed.
- **Case A always works.** In Cases B and C some steps say "if there is no real root, pick
  differently". In the tests a working choice always existed (Case C: the first choice in 27 of
  30), but that is experience, not a theorem.
- **This is not literally the Lean proof's route.** The proof finds its starting polynomials
  differently and recovers $`x`$ through the degree-7 theorem. What is the same is what makes it
  correct: $`\varphi`$ satisfies the three bracket conditions (the CHECK in F1 or C7), which is what
  gives the reduced equation, and $`x`$ is a root of the polynomial in the last step. If you get
  stuck in B or C, the proof's own choices are in `GUIDE-octic-construction.md`.
- **The cubic in A4 is sometimes arithmetic too.** When it has only one real root, Cardano's
  formula gives that root with real square and cube roots.
- **Precision.** Brackets of high powers magnify rounding errors. Carry at least 10 significant
  digits in the roots; the CHECKs tell you if you have lost too many.
- **Drawing the quartic graph** for the crossing: `GUIDE-octic-construction.md` §9.
