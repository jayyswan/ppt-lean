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

**There is no trial and error.** Every choice below is forced: where an equation has several
real roots, the text says which one to take (any one, or the one nearest a given number).

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
(Every bracket is in fact an exact fraction in the coefficients of $`q`$; the approximate roots
are only a quick way to evaluate it.)

## Cases A and B: two preparations

Write the nonreal roots as conjugate pairs $`z = \alpha + \beta i`$ ($`\beta > 0`$).

**N1. A pair vector $`e`$ for each pair.**

1. Divide $`q`$ by $`X^2 - 2\alpha X + (\alpha^2 + \beta^2)`$ (long division). The quotient $`q_6`$ has degree 6; the
   remainder should be about 0.
2. Evaluate $`q_6(z) = w_1 + w_2 i`$ (Horner, complex arithmetic).
3. $`E(X) = (w_1X + \beta w_2 - \alpha w_1)\,q_6(X)`$. Then $`E(z) = i\,s`$ is purely imaginary (CHECK: real part
   about 0), with $`s = \beta(w_1^2 + w_2^2)`$.
4. $`e = E / s`$.

Now $`e`$ is $`0`$ at the six other roots, $`e(z) = i`$, and $`\langle e^2\rangle = -2`$. For any polynomial $`u`$,
$`\langle u e\rangle = -2\,\mathrm{Im}\,u(z)`$.

**N2. Two positive vectors $`g_c`$, $`g_d`$.** To **clean** a polynomial $`u`$, subtract $`\mathrm{Im}\,u(z)\cdot e`$
for every pair $`z`$ (all pairs, not only the ones you will use); the result has real values at
every root. Then

```math
\begin{aligned}
m_1 &= X - \frac{s_1}{8}, \qquad m_2 = X^2 - \frac{s_2}{8} \qquad (s_j = r_1^j + \dots + r_8^j) \\
g_c &= \mathrm{clean}(m_1), \qquad h = \mathrm{clean}(m_2), \qquad g_d = h - \frac{\langle h g_c\rangle}{\langle g_c^2\rangle}\, g_c \\
d_c &= \langle g_c^2\rangle, \qquad d_d = \langle g_d^2\rangle \qquad \text{(both come out positive)}
\end{aligned}
```

$`e`$, $`g_c`$, $`g_d`$ are mutually orthogonal ($`\langle e g_c\rangle = \langle e g_d\rangle = \langle g_c g_d\rangle = 0`$), and
$`\langle e\rangle = \langle g_c\rangle = \langle g_d\rangle = 0`$.

## Case A (2 or 4 real roots)

Take the pair vectors $`e_1`$, $`e_2`$ of two different pairs (say the two with the smallest real
part).

**A1. Arithmetic.** $`t = \sqrt{2/d_c}`$, $`t' = \sqrt{2/d_d}`$.

**A2.** $`P = e_1 + t\,g_c`$, $`R = e_2 + t'\,g_d`$.

**A3. SOLVE6 (cubic).** $`\tau`$ = any real root of

```math
\langle R^3\rangle\,\tau^3 + 3\langle P R^2\rangle\,\tau^2 + 3\langle P^2 R\rangle\,\tau + \langle P^3\rangle = 0.
```

(A cubic always has one. If $`\langle R^3\rangle = 0`$, take $`\varphi = R`$ and skip A4.)

**A4.** $`\varphi = P + \tau R`$. Go to **Finish**.

## Case B (6 real roots)

One pair, vector $`e`$.

**B1. Arithmetic.** $`t = \sqrt{2/d_c}`$.

**B2.** Form

```math
U = d_c\,(e - t\,g_c), \qquad V = -2\,t\,d_c\,g_d, \qquad W = d_d\,(e + t\,g_c).
```

**B3. SOLVE6 (sextic).** $`m`$ = any real root of $`\Psi_6 m^6 + \Psi_5 m^5 + \dots + \Psi_0 = 0`$, where

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

This sextic always has a real root (see "Things to know"). If $`\Psi_6 = 0`$, take $`\varphi = W`$ and skip B4.

**B4.** $`\varphi = U + m\,V + m^2 W`$. Go to **Finish**.

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

**C0. Six seed polynomials.** Label the roots $`r_1, \dots, r_8`$ in any order.

1. For each $`i`$, divide $`q(X)`$ by $`X - r_i`$ (synthetic division; the quotient has degree 7) and
   divide the quotient by its own value at $`r_i`$. This gives eight polynomials $`\ell_1, \dots, \ell_8`$:
   $`\ell_i`$ is $`1`$ at $`r_i`$ and $`0`$ at the other roots.
2. For each row of this table, the seed is $`\sum_i y_i\,\ell_i(X)`$, where $`y_1, \dots, y_8`$ is the row:

| seed | $`y_1`$ | $`y_2`$ | $`y_3`$ | $`y_4`$ | $`y_5`$ | $`y_6`$ | $`y_7`$ | $`y_8`$ |
|---|---|---|---|---|---|---|---|---|
| $`a`$  | −4 | −2 | 2 | −1 | 1 | 4 | 1 | −1 |
| $`b`$  | 0 | 3 | 0 | 2 | 1 | −1 | −6 | 1 |
| $`g`$  | 1 | −2/3 | 0 | −1 | 1 | 3/2 | 2/3 | −5/2 |
| $`w_1`$ | −143/21 | −113/21 | −22/21 | −452/63 | −18/7 | 170/21 | −24/7 | 1154/63 |
| $`w_2`$ | 38/35 | 29/35 | 1/35 | 137/105 | 96/35 | −44/35 | 156/35 | −193/21 |
| $`w_3`$ | 167/35 | −89/35 | 184/35 | −272/105 | −501/35 | −186/35 | −101/35 | 370/21 |

3. Round each coefficient to 10 decimals, then subtract $`\langle \text{seed}\rangle/8`$ from the constant term so
   that $`\langle \text{seed}\rangle = 0`$.

(The table is the proof's "centre". If the seeds were exact, the roots found below would be
exactly $`0,\ 5/3,\ -5322/2915,\ -1`$; rounding moves them slightly. That is why each step says
"nearest".)

**C1. SOLVE6 (cubic).** $`\lambda`$ = the real root nearest $`0`$ of
$`\langle b^3\rangle\lambda^3 + 3\langle ab^2\rangle\lambda^2 + 3\langle a^2b\rangle\lambda + \langle a^3\rangle = 0`$.
Put $`P = a + \lambda b`$.

**C2.** For $`j = 1, 2, 3`$ put $`W_j = w_j - \dfrac{\langle P^2w_j\rangle}{\langle P^2g\rangle}\, g`$.

**C3. Arithmetic (quadratic formula).** $`\xi`$ = the real root nearest $`5/3`$ of
$`\langle P W_2^2\rangle\xi^2 + 2\langle P W_1W_2\rangle\xi + \langle P W_1^2\rangle = 0`$. Put $`q_0 = W_1 + \xi W_2`$.

**C4.** With $`A = \langle P W_1^2\rangle`$, $`B = \langle P W_1W_3\rangle`$, $`C = \langle P W_3^2\rangle`$, $`E_1 = \langle P q_0W_1\rangle`$, $`E_0 = \langle P q_0W_3\rangle`$, form

```math
\begin{aligned}
U &= C\,q_0 - 2E_0\,W_3, \\
V &= 2B\,q_0 - 2E_0\,W_1 - 2E_1\,W_3, \\
W &= A\,q_0 - 2E_1\,W_1.
\end{aligned}
```

**C5. SOLVE6 (sextic).** $`\mu`$ = the real root nearest $`-1.8257`$ ($`= -5322/2915`$) of the sextic with the
coefficients $`\Psi_0, \dots, \Psi_6`$ of step B3, computed from these $`U, V, W`$. Put

```math
v = \frac{U + \mu V + \mu^2 W}{A\mu^2 + 2B\mu + C}.
```

**C6. SOLVE6 (quintic).** $`\kappa`$ = the real root nearest $`-1`$ of

```math
\langle v^5\rangle\kappa^5 + 5\langle P v^4\rangle\kappa^4 + 10\langle P^2v^3\rangle\kappa^3 + 10\langle P^3v^2\rangle\kappa^2 + 5\langle P^4v\rangle\kappa + \langle P^5\rangle = 0.
```

Put $`\varphi = P + \kappa v`$.

CHECK: the four roots you took are within $`0.001`$ of $`0,\ 5/3,\ -1.8257,\ -1`$. If one is not, the
seeds or the roots of $`q`$ are not accurate enough: use more digits (this is the only thing that
can go wrong).

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
$`-1.30604 \pm 1.13199i`$: two real roots, Case A, three pairs.

| Step | Result |
|---|---|
| N1 | three pair vectors, each with $`\langle e^2\rangle = -2`$; the first two ($`z = -1.30604 + 1.13199i`$, $`z = -0.18648 + 0.86419i`$) are $`e_1`$, $`e_2`$ |
| N2 | $`d_c = \langle g_c^2\rangle = 6.16862`$, $`d_d = \langle g_d^2\rangle = 2.24712`$ |
| A1 | $`t = \sqrt{2/6.16862} = 0.569405`$, $`t' = \sqrt{2/2.24712} = 0.943414`$ |
| A2 | $`P = e_1 + t\,g_c`$, $`R = e_2 + t'\,g_d`$ (coefficients below) |
| A3 | $`4.17765\tau^3 + 0.56102\tau^2 - 0.08153\tau + 3.97065 = 0`$, $`\tau = -1.036981`$ |
| A4 | $`\varphi = P + \tau R`$; divided by its largest coefficient, $`\varphi = -0.06759 - 0.12400X - 0.40137X^2 + X^3 - 0.49736X^4 - 0.28582X^5 + 0.08493X^6 + 0.21903X^7`$ |
| F1 | $`p_4 = -6.28635`$, $`p_5 = 2.69315`$, $`p_6 = 3.31914`$, $`p_7 = -1.13298`$, $`p_8 = 9.69485`$ |
| | $`y^8 = -1.57159y^4 + 0.53863y^3 + 0.55319y^2 - 0.16185y - 0.02309`$ |
| F2 | for $`x \approx 0.93408`$: $`y_0 = \varphi(0.93408) = -0.10819 < 0`$, so cross $`Y = X^8`$ with $`Y = -1.57159X^4 - 0.53863X^3 + 0.55319X^2 + 0.16185X - 0.02309`$ near $`X = 0.10819`$; $`y = -0.108190`$ |
| F3 | $`\varphi`$ has degree 7: divide $`q`$ by $`\varphi(X) - y`$; the remainder has degree 6 and real roots $`-0.695542`$ and $`0.934080`$; $`x = 0.934080`$ |

Coefficients (low to high) used above:

```math
\begin{aligned}
P &= 0.03181 + 0.37194X + 0.04534X^2 + 0.24761X^3 - 0.22205X^4 - 0.00182X^5 + 0.13906X^6 + 0.09740X^7 \\
R &= 0.10723 + 0.49913X + 0.49832X^2 - 0.89385X^3 + 0.34919X^4 + 0.32197X^5 + 0.03791X^6 - 0.15416X^7
\end{aligned}
```

(Multiplying $`\varphi`$ by a constant is harmless and keeps the numbers readable.)

So this root costs: one cubic, one crossing and one degree-6 equation; the rest is arithmetic.

## Things to know

- **`python3 octic_byhand.py a8 a7 … a0`** carries out exactly these steps and prints every
  intermediate number, so you can check your arithmetic against it. `python3 octic_byhand.py test`
  ran the procedure on 150 random octics (60 A, 60 B, 30 C); every real root was constructed on
  the first and only try. With the roots of $`q`$ rounded to 7, 9 or 12 decimals the conditions
  $`p_1 = p_2 = p_3 = 0`$ (or $`p_1 = p_3 = p_5 = 0`$) still held to about the same number of digits.
- **Why no choice is needed.**
  - *Case A:* two isotropic directions $`P`$, $`R`$ span a plane on which the trace form vanishes, so
    $`\varphi = P + \tau R`$ has $`\operatorname{Tr}\varphi = \operatorname{Tr}\varphi^2 = 0`$ for every $`\tau`$, and $`\operatorname{Tr}\varphi^3`$ is a cubic in $`\tau`$.
  - *Case B:* with one pair there is a symmetry of the roots (negate the real-root values and
    conjugate-negate the pair value) that fixes $`e`$ and negates $`g_c, g_d`$, and it turns $`\operatorname{Tr}\varphi^3`$
    into its negative. Since $`U, V, W`$ lie in $`\mathrm{span}(e, g_c, g_d)`$, the sextic takes both
    signs, so it has a real root.
  - *Case C:* this is the proof's own route: for exact seeds the four roots are exactly the
    nominal values, and the seeds are close enough to exact that the roots stay close.
- **The cubic in A3 is sometimes arithmetic too.** When it has only one real root, Cardano's
  formula gives that root with real square and cube roots.
- **The two routes are not literally the Lean proof's** in Cases A and B (the proof picks its
  vectors differently and recovers $`x`$ through the degree-7 theorem); Case C is. What is the same
  is what makes it correct: $`\varphi`$ satisfies the bracket conditions (the CHECK in F1 or C7), which
  gives the reduced equation, and $`x`$ is a root of the polynomial in the last step. The proof's
  own choices are in `GUIDE-octic-construction.md`.
- **Precision.** Brackets of high powers magnify rounding errors. Carry at least 10 significant
  digits in the roots; the CHECKs tell you if you have lost too many.
- **Drawing the quartic graph** for the crossing: `GUIDE-octic-construction.md` §9.
