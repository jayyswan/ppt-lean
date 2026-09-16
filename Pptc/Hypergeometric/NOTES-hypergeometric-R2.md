# NOTES-hypergeometric-R2

**Explicit cubic/sextic signature reductions (H5).**

Research note, wave 0, task R2. No `.lean` file was edited, created or deleted.
Every identity below is labelled:

* **[NC n]** numerically checked to `n` significant digits (scripts in
  `archived files/hypergeometric-scripts/`, run with `py R2-*.py`);
* **[SY]** proved symbolically here (the proof is written out, or is a finite
  field/degree computation reproduced by the script);
* **[CL]** classical (from the literature, re-verified numerically here);
* **[SP]** speculative / not established.

Sources read: `AGENTS.md`, `PLAN-hypergeometric-00-overview.md` (§2 V7, §4 H5,
§5 B1, wave table), `NOTES-hypergeometric-R1.md` (the landed R1 note — its B1/B6
work is not repeated), `Pptc/Nonic/Nonic.lean` (`root_Pconstructible_of_rat_nonic_nonreal`),
and the primary sources for the two reductions (see §6).

Scripts (all in `archived files/hypergeometric-scripts/`):

| script | contents |
|---|---|
| `R2-01-quartic-v7.py` | V7 quartic, §1 (pre-existing; re-run) |
| `R2-02-cubic-rbbg.py` | cubic reduction + eliminated relation + invariant cubic, §2 |
| `R2-03-sextic.py` | sextic reduction + eliminated relations, §3 |
| `R2-04-degrees.py` | exact algebraic degrees over `ℚ(z)`, §4 |

---

## 0. Answers in brief

1. **V7 (quartic)** re-confirmed to **59.3 digits** (worst `4.7·10^{-60}`) at
   `z = 1/5, 1/3, 3/4, 1/2, …`; real domain `z ∈ [0,1)`. **[NC 59]**

2. **Cubic signature** `₂F₁(⅓,⅔;1;z)`. The exact reduction to `K` is
   Ramanujan's cubic transformation, proved by Berndt–Bhargava–Garvan
   (Theorem 5.6, p. 258 of Ramanujan's second notebook). It is naturally
   *parametric*: for `p ∈ [0,1)`,

   ```
   z   = β(p) = 27 p²(1+p)² / (4(1+p+p²)³),      k² = α(p) = p³(2+p)/(1+2p),
   ₂F₁(⅓,⅔;1;z) = γ(p)·₂F₁(½,½;1;k²),           γ(p) = (1+p+p²)/√(1+2p).
   ```

   Eliminating `p` gives a **palindromic bidegree-(6,4)** relation `R_c(k²,z)=0`;
   the change of variable `z ↦ k²` therefore has **degree 6**, but its invariant
   `t = k² + 1/k²` satisfies the **irreducible cubic** `Q_c(t,z)=0` (the genuine
   "cubic modular equation"). The prefactor `γ` has degree **12** over `ℚ(z)`
   (it is the fourth root of a degree-3 function). Verified to **79.1 digits**.
   **[CL]** + **[NC 79]**

3. **Sextic signature** `₂F₁(⅙,⅚;1;z)`. Exact reduction (Shen 2013; Robinson
   2020, Thm 8): for `p ∈ [0,1)`,

   ```
   z  = ξ(p) = (27/4) p²(1+p)²/(1+p+p²)³,        k² = x(p) = p(2+p)/(1+2p),
   ₂F₁(⅙,⅚;1;z) = (1−x+x²)^{1/4}·₂F₁(½,½;1;k²).
   ```

   Eliminating `p` gives the clean **sextic** relation
   `16z(1−z)(1−x+x²)³ = 27x²(1−x)²`; equivalently `Q := 1−x+x²` satisfies the
   **cubic** `27(1−Q)² = 16z(1−z)Q³`. Verified to **79.4 digits**. **[CL]** + **[NC 79]**

4. **Degrees (§4).** The two *argument maps* have degree 6 (≤ 9, Nonic-available);
   their natural invariants satisfy irreducible cubics. The two *prefactors* have
   degree 12 generically, which **exceeds the Nonic bound of 9** — a real caveat
   for the "moving `z` costs nothing" step. At `z = ½` (the value B1 needs) every
   degree collapses: cubic `k²` has degree 2 and `γ` degree 4; sextic `x = ½`
   (degree 1) and the prefactor degree ≤ 4. So the B1 rows are safe even though
   the generic prefactor is not.

5. Every algebraic function needed is built from **square roots** (the parametric
   forms need only `√(1+2p)` / `√((1+p+p²)/(1+2p))`) plus, to invert `z ↦ p`,
   the **cube root** from Cardano for the cubic invariant; the generic prefactors
   are **fourth roots** of degree-3 functions. No higher roots appear.

---

## 1. V7: the quartic reduction, re-confirmed

Statement (PLAN §2 V7, `R2-01-quartic-v7.py`):

```
₂F₁(¼,¾;1;z) = (1+√z)^(−1/2)·₂F₁(½,½;1; 2√z/(1+√z)),      z ∈ [0,1).
```

**Domain.** `√z` is real only for `z ≥ 0`; the map `w(z) = 2√z/(1+√z)` is
increasing from `0` to `1` as `z` runs over `[0,1)`, so both sides have
convergent (zero-balanced) series on `[0,1)`; at `z = 1` both diverge
logarithmically. Equivalently, in inverse form
`₂F₁(¼,¾;1; w²/(2−w)²) = √((2−w)/2)·₂F₁(½,½;1;w)`, `w ∈ [0,1)`.

**Numerics.** At 60 dps the worst absolute error over
`z ∈ {1/5, 1/3, 3/4, 1/100, 1/10, 2/7, 1/2, 9/10, 99/100}` is
`4.6673·10^{-60}` = **59.3 digits**; several of these points (`z = 1/5, 1/3`)
give the difference `0` to the working precision. **[NC 59]** (the identity
itself is **[CL]**, Goursat's quadratic transformation; see V7's provenance in
the plan).

---

## 2. The cubic reduction of `₂F₁(⅓,⅔;1;z)` to `K`

### 2.1 Statement **[CL]** (Ramanujan, 2nd notebook p. 258; Berndt–Bhargava–Garvan 1995, Thm 5.6)

For `0 ≤ p < 1`,

```
₂F₁(⅓,⅔;1; β(p)) = γ(p)·₂F₁(½,½;1; α(p)),
```

with

```
α(p) = p³(2+p)/(1+2p),        β(p) = 27 p²(1+p)²/(4(1+p+p²)³),
γ(p) = (1+p+p²)/√(1+2p).
```

`α(0)=β(0)=0`, `α(1)=β(1)=1`; both are strictly increasing on `(0,1)`
(`dα/dp = 6p²(1+p)²/(1+2p)²`, `dβ/dp = 27p(1−p²)(1+2p)(2+p)/(4(1+p+p²)⁴) > 0`),
so `p ↦ z = β(p)` is a bijection `(0,1) → (0,1)` and `k² = α(p)` is a
well-defined algebraic function of `z`. **[SY]** + **[NC 79]**

This is exactly V7's shape, with `K`-argument `k² = α(p)` in place of
`2√z/(1+√z)`. In the plan's notation the "transformation of the argument" is

```
z = β(p)  ↦  k² = α(p),
```

and `K(k) = (π/2)·₂F₁(½,½;1;k²)`.

### 2.2 The explicit algebraic map (eliminated form) **[SY]** + **[NC 79]**

Eliminating `p` between `z = β(p)` and `k² = α(p)` (a sympy/Wolfram resultant)
gives the **irreducible** relation `R_c(k²,z) = 0` with

```
R_c(A,z) = 256 z³(z−1)·(A⁶+1) − 768 z³(z−1)·(A⁵+A)
           + 3A₂(z)·(A⁴+A²) − 2B₂(z)·A³,
A₂(z) = 6561 − 17496 z + 15552 z² − 5120 z³ + 512 z⁴,
B₂(z) = 19683 − 52488 z + 46656 z² − 14720 z³ + 896 z⁴.
```

`R_c` is **palindromic in `A = k²`** (coefficients of `A⁰,A⁶` equal, `A¹,A⁵`
equal, `A²,A⁴` equal): it is invariant under `k² ↔ 1/k²`. Dividing by `A³` and
putting `t = A + 1/A = k² + 1/k²` turns it into the **cubic**

```
Q_c(t,z) = 256 z³(z−1)(t³−3t) − 768 z³(z−1)(t²−2) + 3A₂(z)·t − 2B₂(z) = 0.
```

Hence `[ℚ(z)(t):ℚ(z)] = 3`; `k²` is quadratic over `ℚ(z)(t)` (it solves
`A² − tA + 1 = 0`), so `[ℚ(z)(k²):ℚ(z)] = 6`. This is the sense in which the
**cubic modular equation** mediates the two signature arguments; the "degree-3
change of variable" is the relation for `t`, while the argument `k²` itself has
degree 6. **[SY]** (palindromic structure + tower law), **[NC 79]** (`R_c` and
`Q_c` vanish at the parametrized values: `|R_c| < 10^{-76}`, `|Q_c| < 10^{-75}`).

**Check at `z = ½`** (**[SY]** + **[NC 80]**): `β(p) = ½` gives
`p = (√3−1)/2`, whence

```
k² = (2−√3)/4,   γ = (3/2)/3^{1/4} = 3^{3/4}/2,   t = k²+1/k² = 17/2 + 15√3/4,
```

and therefore the clean special value

```
₂F₁(⅓,⅔;1;½) = (3^{3/4}/2)·₂F₁(½,½;1; (2−√3)/4).        (★)
```

(`(★)` is the `p = (√3−1)/2` instance of the RBBG relation; it is the value B1
needs, and it matches Gauss's second theorem
`₂F₁(⅓,⅔;1;½) = √π/(Γ(2/3)Γ(5/6))`, already confirmed to 50 digits in R1.)

### 2.3 Domain of the cubic reduction

* **Clean real domain:** `p ∈ [0,1)`; then `z = β(p) ∈ [0,1)` and
  `k² = α(p) ∈ [0,1)`, so both series converge absolutely. At `z = 1`
  (`p = 1`) both sides diverge like `−log(1−z)` with ratio `γ(1) = √3`.
* **Extended domain** (Shpot, arXiv:2411.19608): the identity is valid for
  `−½ < p < 1`, with two branches glued by a Pfaff transformation when
  `−½ < p < p*`, `p* = −(1+√3−√(2√3))/2 ≈ −0.43542` (where `α(p*) = −1` and
  the RHS leaves the unit disc). Numerically the direct form still holds at
  `p = −1/3` (tested, **[NC 80]**) because both reduced arguments stay in
  `(−1,1)` there. The *reduction to `K`* therefore does **not** require
  `z > 0` only: it is a genuine `z ∈ (0,1)` statement with an analytic
  continuation at the negative end.

### 2.4 Numerics **[NC 79]**

`R2-02-cubic-rbbg.py` at 80 dps, parametric form, `p ∈ {1/5, 1/3, 1/2, 2/3,
3/4, 9/10}`: worst `|LHS−RHS| = 7.17·10^{-80}` = **79.1 digits**. Inverse
("V7-shape") solve of `β(p)=z` at `z = 1/5, 1/3, 1/2, 3/4, 17/20`: error `0`
or `< 2.2·10^{-81}`. Eliminated relation `R_c` and invariant cubic `Q_c`:
`< 10^{-75}` at every tested `p`.

---

## 3. The sextic reduction of `₂F₁(⅙,⅚;1;z)` to `K`

### 3.1 Statement **[CL]** (Shen, Ramanujan J. 30 (2013); Robinson, arXiv:2009.07069, Thm 8)

There is an increasing bijection `x ↦ ξ` of `(0,1)` onto `(0,1)` given by

```
4 ξ(1−ξ) = (27/4)·x²(1−x)²/(1−x+x²)³,     i.e.   16 ξ(1−ξ)(1−x+x²)³ = 27 x²(1−x)²,
```

for which

```
₂F₁(⅙,⅚;1; ξ) = (1−x+x²)^{1/4}·₂F₁(½,½;1; x).
```

This is V7's shape with `K`-argument `k² = x(ξ)` — but note the exponent `1/4`
(not `1/2`) on the prefactor. Here `K(k) = (π/2)·₂F₁(½,½;1;k²)` with
`k² = x`.

The classical **parametric** form (the same `p` coordinate as the cubic; this is
the transformation recorded in Berndt–Bhargava–Garvan and Berndt's "Flowers"
survey) is

```
x(p)  = p(2+p)/(1+2p),          ξ(p) = (27/4) p²(1+p)²/(1+p+p²)³,
prefactor = (1−x+x²)^{1/4} = √(1+p+p²)/√(1+2p).
```

Both `ξ(p)` and the cubic `β(p)` are the *same* function of `p`; only the
classical argument differs (`α_cubic(p) = p³(2+p)/(1+2p)` versus
`x_sextic(p) = p(2+p)/(1+2p) = p^{-2} α_cubic(p)`). At `p = 1`,
`x = ξ = 1`; at `p = 0`, `x = ξ = 0`. **[SY]** + **[NC 79]**

### 3.2 The explicit algebraic map (eliminated form) **[SY]** + **[NC 79]**

The crucial algebraic simplification is

```
1 − x + x² = (1+p+p²)²/(1+2p)²,
```

so the sextic relation, written in the variable `Q := 1−x+x²`, becomes

```
27(1−Q)² = 16 ξ(1−ξ)·Q³                            (cubic in Q).
```

Hence `[ℚ(ξ)(Q):ℚ(ξ)] = 3`, and `x` solves `x² − x + (1−Q) = 0`, so
`[ℚ(ξ)(x):ℚ(ξ)] = 6`. Equivalently, with `y = x(1−x) = 1−Q`, the relation reads
`27 y² = 16 ξ(1−ξ)(1−y)³`. This is the sextic analogue of the cubic invariant:
the degree-6 change of variable `ξ ↦ x` is a degree-3 invariant relation times
a quadratic. **[SY]**

### 3.3 Domain of the sextic reduction

* **Clean real domain:** `p ∈ (0,1)` (endpoints `0` and `1` included by
  continuity as limits), giving `x, ξ ∈ (0,1)` and absolutely convergent
  series. `p ↦ ξ(p)` is increasing on `(0,1)` (the same derivative as `β`,
  positive there), so `x = x(ξ)` is well defined.
* **Extended domain:** on the negative branch, convergence of the RHS series
  needs `|x| < 1`, which holds exactly for `p ∈ (−2+√3, 0)`; there `x ∈ (−1,0)`
  and `ξ ∈ (0,½)`, and at the endpoint `p = −2+√3` one has `x = −1`, `ξ = ½`.
  Tested at `p = −1/4` (`x = −7/8`, `ξ = 0.44242…`; **[NC 80]**).

### 3.4 Numerics **[NC 79]**

`R2-03-sextic.py` at 80 dps, `p ∈ {1/5, 1/3, 1/2, 2/3, 3/4, 9/10, −1/4}`:
worst `|LHS−RHS| = 4.22·10^{-80}` = **79.4 digits**. Inverse solve of
`ξ(p) = z` at `z = 1/5, 1/3, 1/2, 3/4, 9/10`: error `0` or `< 2.2·10^{-81}`.
Auxiliary relations `16ξ(1−ξ)(1−x+x²)³ − 27x²(1−x)²` and
`27y² − 16ξ(1−ξ)(1−y)³`: `< 3·10^{-80}`.

**Check at `ξ = ½`** (**[SY]** + **[NC 80]**): `p = (√3−1)/2` gives
`x = ½`, `Q = 3/4`, so

```
₂F₁(⅙,⅚;1;½) = (3/4)^{1/4}·₂F₁(½,½;1;½).            (★★)
```

Numerically `1.0984306968398620689… = 0.9306048591020995989… × 1.1803405990160962260…`.

---

## 4. The algebraic functions involved and their degrees

`R2-04-degrees.py` eliminates `p` symbolically (sympy resultants) and factors
over `ℚ` at rational specializations of the signature argument. Because the
specialization is rational and the factors stay irreducible, the degree of the
specialised polynomial equals the degree over `ℚ(z)` (resp. `ℚ(ξ)`).

| function | where | degree over the signature argument | Nonic (≤ 9)? |
|---|---|---|---|
| `k² = α(p)` (cubic argument) | generic `z` | **6** (palindromic; `t=k²+1/k²` has degree **3**) | yes |
| `γ = (1+p+p²)/√(1+2p)` (cubic prefactor) | generic `z` | **12** (`γ⁴` deg 3, `γ²` deg 6) | **no** |
| `k² = x(p)` (sextic argument) | generic `ξ` | **6** (`Q=1−x+x²` has degree **3**) | yes |
| `(1−x+x²)^{1/4}` (sextic prefactor) | generic `ξ` | **12** (`Q` deg 3, `Q^{1/2}` deg 6) | **no** |
| cubic `k²` | `z = ½` | **2** | yes |
| cubic `γ` | `z = ½` | **4** | yes |
| sextic `x` | `ξ = ½` | **1** (`x = ½`) | yes |
| sextic prefactor | `ξ = ½` | **≤ 4** | yes |

Exact degrees at `z = ξ = 3/10` and `1/5`: argument 6, invariant 3, prefactor
12; at `z = ξ = ½`: cubic argument 2 / prefactor 4, sextic argument 1. **[SY]**
(the script reproduces the exact factorisations symbolically). All *individual*
algebraic functions are rational in `p` times at most one square root, so as
functions of `p` — before eliminating `p` — they have degree ≤ 2.

**Consequence for the plan.** The `"moving z costs nothing"` step is *safe for
the argument map* (`k²` and `x` have degree 6 ≤ 9, so `Pptc/Nonic` supplies them
as soon as `z` is P-constructible) and *safe at the B1 value `z = ½`*. It is
**not** automatic for the generic prefactors, which are fourth roots of
degree-3 algebraic functions and so have degree 12. Two honest ways out, both
worth a sentence in L9 (not settled here):

* the prefactor is `(degree-3 element)^{1/4}`, i.e. two successive square roots
  of a Nonic-available number; if `PConstructible` is closed under real square
  roots (plausible — a semicircle/diameter construction), the generic statement
  goes through;
* or restrict the *function-level* theorem to the special arguments (`z = ½` for
  B1) where the prefactor degree drops to ≤ 4, which is all the bridge-back
  `B1` actually consumes.

I flag the general-`z` prefactor-degree-12 fact as a **[SP]**-free but
unresolved step in the plan's argument, not as a theorem about PConstructibility.

**Which roots are needed.** Parametrically only **square roots** appear
(`√(1+2p)`, and `√((1+p+p²)/(1+2p))`). To *invert* `z = β(p)` (resp. `ξ(p)`) one
solves the cubic for the invariant `t = k²+1/k²` (resp. `Q = 1−x+x²`), which
introduces a **cube root** (Cardano); the generic prefactor is then a **fourth
root** of that degree-3 quantity. No roots of higher order than 4 occur, and
none of the individual functions needs a cube root / fourth root whose *base*
has degree > 9.

---

## 5. Numeric evidence and label ledger

Worst absolute errors, all scripts run at 80 dps (`R2-01` at 60 dps):

| identity | label | worst error | digits |
|---|---|---|---|
| V7 quartic | [CL] + [NC 59] | `4.67·10^{-60}` | 59.3 |
| cubic RBBG | [CL] + [NC 79] | `7.17·10^{-80}` | 79.1 |
| cubic eliminated `R_c`, invariant `Q_c` | [SY] + [NC 75] | `< 10^{-75}` | ≥ 75 |
| cubic special value `(★)` at `z=½` | [SY] + [NC 80] | `0` | ≥ 80 |
| sextic reduction | [CL] + [NC 79] | `4.22·10^{-80}` | 79.4 |
| sextic relations | [SY] + [NC 80] | `< 3·10^{-80}` | ≥ 80 |
| sextic special value `(★★)` at `ξ=½` | [SY] + [NC 80] | `0` | ≥ 80 |
| degree table | [SY] | exact factorisation | — |

| statement | label |
|---|---|
| V7 statement and domain (§1) | [CL] (Goursat quadratic) + [NC 59] |
| cubic RBBG relation and `α,β,γ` (§2.1) | [CL] (Ramanujan/BBG Thm 5.6) + [NC 79] |
| monotonicity / bijection `p ↔ z` (§2.1) | [SY] + [NC] |
| eliminated palindromic relation and invariant cubic (§2.2) | [SY] + [NC 75] |
| extended domain `−½<p<1`, `p*` (§2.3) | [CL] (Shpot) + [NC 80] |
| sextic relation and parametrisation (§3.1) | [CL] (Shen; Robinson Thm 8) + [NC 79] |
| sextic cubic in `Q=1−x+x²` (§3.2) | [SY] + [NC 80] |
| degree table (§4) | [SY] |
| general-`z` prefactor needs a degree-12 function | [SY], flagged for L9 |

No `sorry`; no Lean file touched. R1's B1/B6 conclusions are unchanged: the
cubic/sextic *values* at `z = ½` are what feed B1, and `(★)`, `(★★)` exhibit them
directly.

---

## 6. Sources

* **Cubic.** S. Ramanujan, *Second Notebook*, p. 258; B. C. Berndt,
  S. Bhargava, F. G. Garvan, "Ramanujan's theories of elliptic functions to
  alternative bases", *Trans. Amer. Math. Soc.* **347** (1995) 4163–4244,
  **Theorem 5.6**. Validity range extended in M. A. Shpot, "A Ramanujan's
  hypergeometric transformation formula, its validity range and implications",
  arXiv:2411.19608 (2024). (The related *self*-transformation is DLMF 15.8.33:
  `₂F₁(⅓,⅔;1;1−((1−x)/(1+2x))³) = (1+2x)₂F₁(⅓,⅔;1;x³)`; the Borwein–Borwein
  cubic AGM paper gives the AGM interpretation.)
* **Sextic.** Li-Chien Shen, "A note on Ramanujan's identities involving the
  hypergeometric function `F(1/6,5/6;1,z)`", *Ramanujan J.* **30** (2013)
  211–222; P. L. Robinson, "Hypergeometric identities in elliptic signature
  six", arXiv:2009.07069 (2020), **Theorem 8**; also B. C. Berndt, "Flowers
  which we cannot yet see growing…", and Berndt–Bhargava–Garvan (signature-6
  section).
* **Quartic V7.** PLAN §2 V7; Goursat's quadratic transformation (DLMF §15.8).
