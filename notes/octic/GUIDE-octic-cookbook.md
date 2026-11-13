# How to construct a real root of an octic

**You have:** an octic `q` with constructible coefficients, and you want one of its real roots `x`.
**You may use:**

- **COMPUTE** — arithmetic (`+ − × ÷`) on numbers you already have;
- **SOLVE6** — a real root of a polynomial of degree ≤ 6 (this covers square roots);
- **CROSS** — one crossing of two curves, used exactly once.

## Fastest route: let the script write the plan

    python3 octic_plan.py  a8 a7 a6 a5 a4 a3 a2 a1 a0

prints a numbered list of COMPUTE / SOLVE6 / CROSS steps for your octic, with every number
filled in, ending in each real root. With no arguments it does `X⁸ − X − 1`; that output is
reproduced at the end of this file. The rest of this file explains what the steps are, so you
can do them without the script.

## Setup (all cases)

Divide `q` by its leading coefficient: `q = X⁸ + a₇X⁷ + … + a₀`.

**S1. Power sums.** `s₀ = 8`, and for `k = 1, 2, …, 40`

    s_k = −(a₇s_{k−1} + a₆s_{k−2} + … + a_{8−k+1}s₁) − k·a_{8−k}     (k ≤ 8)
    s_k = −(a₇s_{k−1} + a₆s_{k−2} + … + a₀s_{k−8})                   (k > 8)

**S2. The bracket.** For a polynomial `w = w₀ + w₁X + w₂X² + …` put

    ⟨w⟩ = w₀s₀ + w₁s₁ + w₂s₂ + …

(This is the sum of `w(r)` over the eight roots `r` of `q`.) `⟨uv⟩`, `⟨u³⟩`, `⟨P²w⟩` mean:
multiply the polynomials out first, then take the bracket. Every polynomial below has degree
≤ 7 and is **centred**, meaning `⟨u⟩ = 0`; to centre a polynomial subtract `⟨u⟩/8` from its
constant term. Sums of centred polynomials are centred.

**S3. Which case.** Form the 7×7 matrix `G[j][k] = s_{j+k} − s_j·s_k/8` (`j, k = 1..7`) and
count its negative eigenvalues (numerically). That count is the number of complex-conjugate
pairs of roots.

| Negative eigenvalues | Roots | Go to |
|---|---|---|
| 0 | 8 real | Case 1 |
| 1 | 6 real | Case 2 |
| 2 or 3 | 4 or 2 real | Case 3 |

An eigenvector `(c₁,…,c₇)` of G stands for the centred polynomial `c₁X + … + c₇X⁷ − (c₁s₁+…+c₇s₇)/8`.

A **seed** is a polynomial with rational coefficients that you pick, subject to a sign check.
Where it comes from does not matter; only the check does. If a check fails, round less coarsely.

## Cases 2 and 3 (some complex roots): find φ with ⟨φ⟩ = ⟨φ²⟩ = ⟨φ³⟩ = 0

**A1. Seeds.** `e` := an eigenvector of G for a negative eigenvalue, rounded to a couple of
decimals and centred. `f` := the same for a positive eigenvalue.
Check `⟨e²⟩ < 0 < ⟨f²⟩`.

**A2. SOLVE6.** `t` := the positive root of `⟨f²⟩t² + 2⟨ef⟩t + ⟨e²⟩ = 0`.

**A3. COMPUTE.** `P = e + t·f`. (Now `⟨P²⟩ = 0`.)

### Case 3 (two or more complex pairs)

**B1. Seeds orthogonal to P.** Take eigenvectors `n₁, n₂` of G for two negative eigenvalues
and `p₁, p₂` for two positive ones. Round each of

    ⟨P n₂⟩·n₁ − ⟨P n₁⟩·n₂        and        ⟨P p₂⟩·p₁ − ⟨P p₁⟩·p₂

to rational polynomials `e₀`, `f₀`. Pick `j` with `c = ⟨P·u⟩ ≠ 0`, where `u = Xʲ − s_j/8`, and set

    e′ = c·e₀ − ⟨P e₀⟩·u,        f′ = c·f₀ − ⟨P f₀⟩·u.

Check `⟨e′²⟩ < 0 < ⟨f′²⟩`. (`⟨P e′⟩ = ⟨P f′⟩ = 0` holds automatically.)

**B2. SOLVE6.** `t′` := the positive root of `⟨f′²⟩t′² + 2⟨e′f′⟩t′ + ⟨e′²⟩ = 0`.

**B3. COMPUTE.** `x̃ = e′ + t′·f′`.

**B4. SOLVE6.** `τ` := a real root of the cubic `⟨x̃³⟩τ³ + 3⟨P x̃²⟩τ² + 3⟨P² x̃⟩τ + ⟨P³⟩ = 0`.
(If `⟨x̃³⟩ = 0`, skip this and take `φ = x̃`.)

**B5. COMPUTE.** `φ = P + τ·x̃`. Go to **Finish**.

### Case 2 (one complex pair)

For a centred polynomial `d` define

    σ(d) = ⟨d²⟩·P − 2⟨P d⟩·d,        Φ(d) = ⟨σ(d)³⟩.

**C1. Seeds.** Find rational centred `d⁺`, `d⁻` with `Φ(d⁺) > 0 > Φ(d⁻)`. Try
`Xʲ − s_j/8` and sums and differences of two of these; that usually works (27 of 30 random
tests). If it does not, the guaranteed recipe is: with `ω = −1/2 ± (√3/2)i`, take the
polynomial that is 1 at one real root, 0 at the other five real roots and ω at the complex
root, and round it; one of the first two real roots gives both signs. The script does this.

**C2. SOLVE6.** `Ψ(m) = Φ(d⁺ + m·(d⁻ − d⁺))` is a polynomial of degree 6 in `m`. Get its
coefficients by evaluating at `m = 0, 1/6, 2/6, …, 1` and interpolating. `Ψ(0) > 0 > Ψ(1)`,
so it has a root `m` in `(0, 1)`: take it.

**C3. COMPUTE.** `φ = σ(d⁺ + m·(d⁻ − d⁺))`. Go to **Finish**.

### Finish (Cases 2 and 3)

**F1. COMPUTE the reduced equation.** Let `χ(y) = y⁸ + χ₇y⁷ + … + χ₀` be the resultant of
`q(X)` and `y − φ(X)` with respect to X (equivalently the characteristic polynomial of
`φ(C)`, C the companion matrix of q). Then `χ₇ = χ₆ = χ₅ = 0`, so with `c_k = −χ_k`

    y⁸ = c₄y⁴ + c₃y³ + c₂y² + c₁y + c₀        holds at y = φ(x).

**F2. CROSS.** Evaluate `φ` at your approximation of `x` to learn the sign and rough size of `y`.

- `y > 0`: draw `Y = X⁸` and `Y = c₄X⁴ + c₃X³ + c₂X² + c₁X + c₀`. They cross at `X = y`.
- `y < 0`: draw `Y = X⁸` and `Y = c₄X⁴ − c₃X³ + c₂X² − c₁X + c₀`. They cross at `X = −y`.

Restrict to an interval of X containing only that crossing, and read off `y`.
(How the quartic graph itself is drawn: `GUIDE-octic-construction.md` §9.)

**F3. COMPUTE x.** Run Euclid's algorithm on `q(X)` and `φ(X) − y`. The last nonzero
remainder is `r₁X + r₀`, and `x = −r₀/r₁`.

## Case 1 (all eight roots real): find φ with ⟨φ⟩ = ⟨φ³⟩ = ⟨φ⁵⟩ = 0

**D1. Six seeds.** Number the roots `x₁ < … < x₈`. For each row, find the polynomial of
degree ≤ 7 taking these values at `x₁,…,x₈` (interpolation with approximate roots), round its
coefficients to 8 decimals, and centre it.

| name | values at x₁ … x₈ |
|---|---|
| a | −4, −2, 2, −1, 1, 4, 1, −1 |
| b | 0, 3, 0, 2, 1, −1, −6, 1 |
| g | 1, −2/3, 0, −1, 1, 3/2, 2/3, −5/2 |
| w₁ | −143/21, −113/21, −22/21, −452/63, −18/7, 170/21, −24/7, 1154/63 |
| w₂ | 38/35, 29/35, 1/35, 137/105, 96/35, −44/35, 156/35, −193/21 |
| w₃ | 167/35, −89/35, 184/35, −272/105, −501/35, −186/35, −101/35, 370/21 |

**D2. SOLVE6.** `λ` := the root nearest 0 of the cubic `⟨(a + λb)³⟩ = 0`. Put `P = a + λb`.

**D3. COMPUTE.** `Wⱼ = wⱼ − (⟨P²wⱼ⟩ / ⟨P²g⟩)·g` for `j = 1, 2, 3`. Check `⟨P²g⟩ ≠ 0`.

**D4. SOLVE6.** `ξ` := the root nearest 5/3 of the quadratic `⟨P·(W₁ + ξW₂)²⟩ = 0`.
Put `q₀ = W₁ + ξW₂`.

**D5. SOLVE6.** With `d = μW₁ + W₃`, `μ` := the root nearest −1.8257 of the sextic

    ⟨ ( ⟨P d²⟩·q₀ − 2⟨P q₀ d⟩·d )³ ⟩ = 0.

**D6. COMPUTE.** `v = q₀ − (2⟨P q₀ d⟩ / ⟨P d²⟩)·d`. Check `⟨P d²⟩ ≠ 0`.

**D7. SOLVE6.** `κ` := the root nearest −1 of the quintic `⟨(P + κv)⁵⟩ = 0`.

**D8. COMPUTE.** `φ = P + κv`. (Its values at the roots are close to 1, 2, 3, 4, −1, −2, −3, −4.)

**D9. COMPUTE the reduced equation.** `χ(y)` as in F1. Now `χ₇ = χ₅ = χ₃ = 0`, so

    Q(y²) = c·y,     Q(X) = X⁴ + χ₆X³ + χ₄X² + χ₂X + χ₀,     c = −χ₁.

**D10. CROSS.** Draw `Y = Q(X)` and `Y = ±c·√X` (sign `+` if `y = φ(x) > 0`, `−` if `y < 0`).
Restrict to an interval containing only the crossing at `X = y²`, and read off `X`.

**D11. SOLVE6.** `y = ±√X` (same sign).

**D12. COMPUTE x.** As F3.

For the coefficients of the cubic, quadratic, sextic and quintic in D2–D7, evaluate the
bracket at degree + 1 values of the unknown and interpolate.

## Things to know

- **Approximate roots are needed for planning only:** to pick seeds, to choose the root of
  each SOLVE6, and to know which crossing is yours. Every check is a strict inequality or a
  `≠`, so the planning numbers can be rough.
- **Steps F3 and D12 go beyond the Lean proof.** Euclid isolates `x` when `φ(x)` differs from
  `φ` at the other seven roots. That is guaranteed in Case 1 and held in all 90 random octics
  tried, but is not proved in Cases 2 and 3. If it fails, `x` is a root of `φ(X) − y`, of
  degree ≤ 7: see `GUIDE-octic-construction.md` §8. The script reports this as `SOLVE7`.
- **Repeated roots:** if `gcd(q, q′) ≠ 1`, work with `gcd(q, q′)` and `q / gcd(q, q′)`
  instead; both have degree ≤ 7.
- **Why it works, and the Lean lemma behind each step:** `GUIDE-octic-construction.md`.

## Worked example: X⁸ − X − 1

Output of `python3 octic_plan.py` (Case 3):

```
q(X) = (-1.0) + (-1.0)X + (1.0)X^8
approximate real roots: ['-0.81165232', '1.096981558']

 1. COMPUTE power sums s_0..s_40 (Newton):  s_0..s_8 = 8.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 7.0, 8.0
 2. COMPUTE G[j][k] = s_(j+k) - s_j s_k / 8  (j,k = 1..7);  eigenvalues ~ ['-13.7', '-9.98', '-4.69', '2.43', '7.85', '12.3', '14.7']
            3 negative  =>  CASE 3: two or more complex pairs
 3. COMPUTE seed e (rounded eigenvector of G, eigenvalue -13.68):
            e = (-0.34125) + (-0.72)X + (-1.0)X^2 + (-0.61)X^3 + (0.2)X^4 + (0.87)X^5 + (0.95)X^6 + (0.39)X^7
            check <e^2> = -51.194912 < 0
 4. COMPUTE seed f (rounded eigenvector of G, eigenvalue 14.69):
            f = (0.21875) + (-0.43)X + (-0.75)X^2 + (-0.96)X^3 + (-1.0)X^4 + (-0.88)X^5 + (-0.61)X^6 + (-0.25)X^7
            check <f^2> = 56.963687 > 0
 5. SOLVE6  positive root t of  (56.963687) t^2 + (-0.121425) t + (-51.194912) = 0   [= <f^2> t^2 + 2<ef> t + <e^2>]
            t = 0.94907954522307
 6. COMPUTE P = e + t f = (-0.133639) + (-1.1281)X + (-1.71181)X^2 + (-1.52112)X^3 + (-0.74908)X^4 + (0.03481)X^5 + (0.371061)X^6 + (0.15273)X^7
            (now <P> = 0 and <P^2> = 0)
 7. COMPUTE second pair of seeds, made orthogonal to P.  With u = X^5 - s_5/8, c = <P u> = -24.151599:
            e' = c e0 - <P e0> u,   e0 = (0.6475) + (1.0)X + (-0.14)X^2 + (-0.96)X^3 + (0.37)X^4 + (0.87)X^5 + (-0.59)X^6 + (-0.74)X^7
            f' = c f0 - <P f0> u,   f0 = (0.6125) + (-1.0)X + (-0.58)X^2 + (0.61)X^3 + (0.99)X^4 + (0.06)X^5 + (-0.95)X^6 + (-0.7)X^7
            check <e'^2> = -21844.562 < 0 < <f'^2> = 29249.815,  <P e'> = <P f'> = 0
 8. SOLVE6  positive root t' of  (29249.815) t'^2 + (92.759951) t' + (-21844.562) = 0   [= <f'^2> t'^2 + 2<e'f'> t' + <e'^2>]
            t' = 0.862607539795127
 9. COMPUTE x = e' + t' f' = (-28.3986) + (-3.31825)X + (15.4646)X^2 + (10.4772)X^3 + (-29.5611)X^4 + (-22.6348)X^5 + (34.0411)X^6 + (32.4555)X^7
            (now <x> = <x^2> = <P x> = 0)
10. SOLVE6  a real root tau of  (5407005.6) tau^3 + (-15289.596) tau^2 + (-5312.3848) tau + (-425.12835) = 0
            [= <x^3> tau^3 + 3<P x^2> tau^2 + 3<P^2 x> tau + <P^3>]
            tau = 0.0515199267007771
11. COMPUTE phi = (-0.7027666452) + (-0.5717528629)X + (-0.4027507998)X^2 + (-0.4319119264)X^3 + (-1.0)X^4 + (-0.4979309017)X^5 + (0.9352096698)X^6 + (0.8031618802)X^7
            (rescaled so its largest coefficient is 1;  <phi> = <phi^2> = <phi^3> = 0)
12. COMPUTE resolvent = characteristic polynomial of phi(C) = resultant_X(q(X), y - phi(X)):
            y^8 = (-93.52090823) y^4 + (-313.4655721) y^3 + (-342.9846178) y^2 + (-154.7275346) y + (-24.90250497)

    --- for the root x ~ -0.811652320028 ---
13. CROSS   the curves  Y = X^8  and  Y = (-93.52090823) X^4 + (313.4655721) X^3 + (-342.9846178) X^2 + (154.7275346) X + (-24.90250497)
            cross exactly once for 0.3 <= X <= 0.9, at X = 0.450674663322653;  y = -X = -0.450674663322653
14. COMPUTE Euclid's algorithm on q(X) and phi(X) - y ends with the remainder r1 X + r0;
            x = -r0 / r1 = -0.81165232002780264839
            check: q(x) = -3.89e-61

    --- for the root x ~ 1.0969815578 ---
15. CROSS   the curves  Y = X^8  and  Y = (-93.52090823) X^4 + (313.4655721) X^3 + (-342.9846178) X^2 + (154.7275346) X + (-24.90250497)
            cross exactly once for 1.0 <= X <= 2.6, at X = 1.45885025751193;  y = -X = -1.45885025751193
16. COMPUTE Euclid's algorithm on q(X) and phi(X) - y ends with the remainder r1 X + r0;
            x = -r0 / r1 = 1.0969815577985598179
            check: q(x) = -3.49e-59
```
