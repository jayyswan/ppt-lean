# How to construct a real root of an octic

You have an octic `q` and want to construct one of its real roots `x`.

**What you construct** (the actual work):

- **SOLVE6** — a real root of a polynomial of degree ≤ 6 (square roots included);
- **CROSS** — one crossing of two curves, once per octic;
- arithmetic (`+ − × ÷`) on numbers already constructed.

**What Wolfram does** (planning): all the algebra that decides which equations those are.
Paste the blocks below into Mathematica or a Wolfram Cloud notebook. Wolfram also solves each
equation numerically, so you see every number before you construct it.

In every case the construction has the same three parts:

1. a few SOLVE6 steps, which produce a polynomial `φ` of degree ≤ 7;
2. one CROSS, which produces `y = φ(x)`;
3. arithmetic, which turns `y` into `x`.

## Step 0. Setup and which case

```wolfram
q = X^8 - X - 1;                                  (* your octic, leading coefficient 1 *)
r = X /. NSolve[q == 0, X, WorkingPrecision -> 40];
br[w_] := Chop[Expand[Total[(w /. X -> #) & /@ r]], 10^-25];    (* sum of w over the 8 roots *)
center[u_] := u - br[u]/8;
seedV[v_] := center[Rationalize[Chop[Expand[InterpolatingPolynomial[Transpose[{r, v}], X]]], 10^-8]];
seed[fn_] := seedV[fn /@ r];
realroots[p_] := T /. NSolve[p == 0, T, Reals, WorkingPrecision -> 40];
Count[r, _Real]                                   (* number of real roots *)
```

`seedV[v]` is "the polynomial taking the values `v` at the eight roots, coefficients rounded
to rationals, shifted so that its values at the roots sum to 0". Seeds are only starting
points: any rational polynomial that passes the stated sign check is acceptable.

| Real roots | Case |
|---|---|
| 2 or 4 | **A** |
| 6 | **B** |
| 8 | **C** |

If `q` has a repeated root (`PolynomialGCD[q, D[q, X]]` is not 1), replace `q` by that gcd and
by `q` divided by it; both have degree ≤ 7 and this guide does not cover them.

## Case A: 2 or 4 real roots

```wolfram
{z, w} = Take[Select[r, Im[#] > 0 &], 2];         (* complex roots from two different pairs *)
at[z_, c_] := Function[s, Which[s == z, c, s == Conjugate[z], Conjugate[c], True, 0]];
e = seed[at[z, I]];  f = seed[at[z, 1]];  n = seed[at[w, I]];  p = seed[at[w, 1]];
{br[e^2], br[f^2]}                                (* CHECK: negative, positive *)

eq1 = br[f^2] T^2 + 2 br[e f] T + br[e^2]
t = Max[realroots[eq1]]
P = e + t f;

e1 = br[P n] e - br[P e] n;   f1 = br[P p] f - br[P f] p;
{br[e1^2], br[f1^2]}                              (* CHECK: negative, positive *)

eq2 = br[f1^2] T^2 + 2 br[e1 f1] T + br[e1^2]
t2 = Max[realroots[eq2]]
x2 = e1 + t2 f1;

eq3 = br[x2^3] T^3 + 3 br[P x2^2] T^2 + 3 br[P^2 x2] T + br[P^3]
tau = First[realroots[eq3]]
phi = P + tau x2;
```

**Construct, in this order:**

1. **SOLVE6:** `t` = the positive root of the quadratic `eq1`.
2. **SOLVE6:** `t2` = the positive root of the quadratic `eq2`. (Its coefficients are arithmetic in `t`.)
3. **SOLVE6:** `tau` = a real root of the cubic `eq3`. (Coefficients: arithmetic in `t`, `t2`.)
4. Go to **Finish (A and B)**.

## Case B: 6 real roots

```wolfram
z = First[Select[r, Im[#] > 0 &]];
at[z_, c_] := Function[s, Which[s == z, c, s == Conjugate[z], Conjugate[c], True, 0]];
e = seed[at[z, I]];  f = seed[at[z, 1]];
{br[e^2], br[f^2]}                                (* CHECK: negative, positive *)

eq1 = br[f^2] T^2 + 2 br[e f] T + br[e^2]
t = Max[realroots[eq1]]
P = e + t f;

sig[d_] := br[d^2] P - 2 br[P d] d;   Phi[d_] := br[sig[d]^3];
om = Exp[2 Pi I/3];
lag[xj_, c_] := Function[s, Which[s == z, c, s == Conjugate[z], Conjugate[c], s == xj, 1, True, 0]];
cand = Flatten[Table[seed[lag[xj, c]], {xj, Take[Select[r, Im[#] == 0 &], 2]}, {c, {om, Conjugate[om]}}]];
Phi /@ cand                                       (* CHECK: at least one positive, one negative *)
dp = First[MaximalBy[cand, Phi]];  dm = First[MinimalBy[cand, Phi]];

eq2 = Phi[dp + T (dm - dp)]                       (* a sextic in T, positive at 0, negative at 1 *)
m = First[Select[realroots[eq2], 0 < # < 1 &]]
phi = sig[dp + m (dm - dp)];
```

**Construct, in this order:**

1. **SOLVE6:** `t` = the positive root of the quadratic `eq1`.
2. **SOLVE6:** `m` = a root in `(0, 1)` of the sextic `eq2`. (Coefficients: arithmetic in `t`.)
3. Go to **Finish (A and B)**.

## Finish (A and B)

```wolfram
phi = phi/Max[Abs[CoefficientList[phi, X]]];      (* harmless rescaling *)
chi = Chop[Expand[Times @@ ((Y - (phi /. X -> #)) & /@ r)], 10^-25]   (* = Resultant[q, Y - phi, X] *)
c = -CoefficientList[chi, Y][[1 ;; 5]]            (* {c0, c1, c2, c3, c4} *)
x0 = Max[Select[r, Im[#] == 0 &]];                (* the real root you want, approximately *)
y0 = phi /. X -> x0

a = q;  b = phi - y0;
While[Exponent[b, X] > 1, {a, b} = {b, Chop[PolynomialRemainder[a, b, X], 10^-25]}];
b                                                 (* r1 X + r0 *)
-Coefficient[b, X, 0]/Coefficient[b, X, 1]        (* = x *)
```

`chi` has no `Y⁷`, `Y⁶`, `Y⁵` terms (CHECK), so `y = φ(x)` satisfies
`y⁸ = c4·y⁴ + c3·y³ + c2·y² + c1·y + c0`.

**Construct:**

1. **CROSS.** Look at the sign of `y0`.
   - `y0 > 0`: draw `Y = X⁸` and `Y = c4·X⁴ + c3·X³ + c2·X² + c1·X + c0`. They cross at `X = y`.
   - `y0 < 0`: draw `Y = X⁸` and `Y = c4·X⁴ − c3·X³ + c2·X² − c1·X + c0`. They cross at `X = −y`.

   The curves may cross more than once; yours is the crossing at `X = |y0|`. Restrict to an
   interval around it that contains no other crossing.
2. **Arithmetic.** Euclid's algorithm on `q(X)` and `φ(X) − y` (the `While` loop) ends in a
   linear remainder `r1·X + r0`. Then `x = −r0/r1`. Every division step is arithmetic in the
   numbers already constructed.

## Case C: 8 real roots

```wolfram
r = Sort[Re[r]];
a  = seedV[{-4, -2, 2, -1, 1, 4, 1, -1}];
b  = seedV[{0, 3, 0, 2, 1, -1, -6, 1}];
g  = seedV[{1, -2/3, 0, -1, 1, 3/2, 2/3, -5/2}];
w1 = seedV[{-143/21, -113/21, -22/21, -452/63, -18/7, 170/21, -24/7, 1154/63}];
w2 = seedV[{38/35, 29/35, 1/35, 137/105, 96/35, -44/35, 156/35, -193/21}];
w3 = seedV[{167/35, -89/35, 184/35, -272/105, -501/35, -186/35, -101/35, 370/21}];
near[p_, t0_] := First[MinimalBy[realroots[p], Abs[# - t0] &]];

eq1 = br[(a + T b)^3]                             (* cubic *)
lam = near[eq1, 0]
P = a + lam b;
br[P^2 g]                                         (* CHECK: not 0 *)
proj[u_] := u - br[P^2 u]/br[P^2 g] g;   {W1, W2, W3} = proj /@ {w1, w2, w3};

eq2 = br[P (W1 + T W2)^2]                         (* quadratic *)
xi = near[eq2, 5/3]
q0 = W1 + xi W2;

dT = T W1 + W3;
eq3 = br[(br[P dT^2] q0 - 2 br[P q0 dT] dT)^3]    (* sextic *)
mu = near[eq3, -5322/2915]
d = dT /. T -> mu;
br[P d^2]                                         (* CHECK: not 0 *)
v = q0 - 2 br[P q0 d]/br[P d^2] d;

eq4 = br[(P + T v)^5]                             (* quintic *)
kap = near[eq4, -1]
phi = P + kap v;

chi = Chop[Expand[Times @@ ((Y - (phi /. X -> #)) & /@ r)], 10^-25]
cl = CoefficientList[chi, Y];
Q = X^4 + cl[[7]] X^3 + cl[[5]] X^2 + cl[[3]] X + cl[[1]]
c = -cl[[2]]
x0 = Max[r];                                      (* the real root you want, approximately *)
y0 = phi /. X -> x0
```

`chi` has no `Y⁷`, `Y⁵`, `Y³` terms (CHECK), so `y = φ(x)` satisfies `Q(y²) = c·y`.
The values of `φ` at the eight roots come out close to `1, 2, 3, 4, −1, −2, −3, −4`.

**Construct, in this order:**

1. **SOLVE6:** `lam` = the root of the cubic `eq1` nearest 0.
2. **SOLVE6:** `xi` = the root of the quadratic `eq2` nearest 5/3.
3. **SOLVE6:** `mu` = the root of the sextic `eq3` nearest −1.8257.
4. **SOLVE6:** `kap` = the root of the quintic `eq4` nearest −1.
5. **CROSS.** Draw `Y = Q(X)` and `Y = c·√X` if `y0 > 0`, or `Y = −c·√X` if `y0 < 0`. Yours
   is the crossing at `X = y0²`; restrict to an interval containing no other.
6. **SOLVE6:** `y = √X` if `y0 > 0`, `y = −√X` if `y0 < 0`.
7. **Arithmetic.** Euclid on `q(X)` and `φ(X) − y`, exactly as in the Finish block.

Each equation's coefficients are arithmetic in the numbers constructed before it.

## Things to know

- **The Wolfram blocks have not been run.** There is no Wolfram in the environment this was
  written in. The mathematics of every step was checked numerically in Python
  (`octic_construct.py`, `octic_plan.py`), but treat the Wolfram syntax as a first draft.
- **`python3 octic_plan.py a8 a7 … a0` prints the same kind of plan** with all numbers
  filled in, and has been run on 90 random octics. It picks its seeds differently, so its
  numbers will not match the Wolfram ones; both are valid.
- **The Euclid step is a shortcut that the Lean proof does not use.** It needs `φ(x)` to
  differ from `φ` at the other seven roots. That is guaranteed in Case C and held in every
  test, but is not proved in Cases A and B. If the `While` loop does not end in a linear
  remainder, `x` is instead a root of `φ(X) − y`, of degree ≤ 7; see
  `GUIDE-octic-construction.md` §8.
- **Drawing the quartic graph** for the crossing is described in
  `GUIDE-octic-construction.md` §9.
- **Why it works**, and the Lean lemma behind each step: `GUIDE-octic-construction.md`.
