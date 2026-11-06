# NOTES-jacobi-X6 — computer hunt for a formula

Task `PLAN-jacobi-X6-identity-hunt.md` (X series), read under `PLAN-jacobi-X0-overview.md`.
**Research only: no `.lean` file was created, edited or deleted.** Numerics: Python 3.12 with
`mpmath`/`numpy`/`scipy` at `C:\Users\<user>\AppData\Local\Programs\Python\Python312\python.exe`;
scripts in `archived files/jacobi-scripts/` with the `X6-` prefix. `mpmath.ellipfun(kind,u,m)`,
`mpmath.ellipf(phi,m)`, `mpmath.ellipe(phi,m)`, `mpmath.ellipk(m)`, `mpmath.ellipe(m)` all take
the **parameter** `m = c = k²`; the same convention is used throughout. Every identity is tagged
**[symbolic]** (exact) or **[numeric, N digits]**.

---

## Plain-language summary (≤10 lines)

1. We built a library of 48 cheap-to-draw functions of `u` (the amplitude's argument) and `c`,
   and asked numerically whether `am(u)`, `sn`, `cn`, `dn` or the periodic part
   `am(u) − uπ/(2K)` equals a simple combination of them.
2. PSLQ at 100 digits found **no** integer relation at any tested modulus/argument, over the
   full library and over every small subset (size ≤ 3). Total 15,372 calls, zero hits.
3. Real-coefficient fits found no linear identity either: the best fits interpolate the training
   interval but fail to extrapolate, which is the signature of an overfit, not an identity.
4. A greedy search over the full library (orthogonal matching pursuit, 12 terms) likewise shrank
   the training residual to `~10⁻⁸` while the extrapolation residual stayed at `10⁻²–10⁻⁵`.
5. Composing a single library function with `sin, cos, arcsin, arccos, √, 2^·, log` (or a
   degree-≤2 rational) gave nothing: best extrapolation residual `≥ ~10⁻³`.
6. An important trap: fitting the target against all 48 library functions at once gives a
   spurious `~10⁻¹⁴` off-grid residual, because the library has numerical rank only 17–20 of 48
   and the minimum-norm solution can interpolate any smooth function. Extrapolation exposes it.
7. Consequently the honest negative comes from small, well-conditioned subsets and from
   extrapolation, not from the full-library least-squares residual.
8. **Outcome: negative.** `am` is not a fixed (real) constant-coefficient combination of the
   documented library, nor a single-function elementary composition of it, at the moduli tested.
9. This is consistent with the earlier structural results: `am` is not D-finite (X1), the
   composition route is blocked (R3), and no classical conic mechanism inverts `F` (X3).
10. Special arguments (§4): `am(K/2)` and `am(K/3)` are P-constructible via degree-≤4
    polynomials (`sn(K/3)` is a quartic over `ℚ`); `2K/3, K/4, mK/5, …, K/8` have no
    degree-≤6 polynomial. A high-precision control also exposed (and discarded) earlier
    spurious PSLQ relations of degree 3.

---

## 1. Conventions and data

Fix the **parameter** `c` with `0 < c < 1` (so the modulus is `k = √c`). Write
`E(φ,c) = ∫₀^φ √(1−c sin²θ)dθ`, `F(φ,c) = ∫₀^φ dθ/√(1−c sin²θ)`, and
`EAm(u,c)` for the unique real `φ` with `E(φ,c) = u` (possible for all `u` since
`E' = √(1−c sin²·) ≥ √(1−c) > 0`). The targets are
`am(u,c)`, `sn = sin(am)`, `cn = cos(am)`, `dn = √(1−c sin²(am))`, and
`am_periodic = am(u,c) − u·π/(2K(c))`, all for `0 < u < K(c)` (principal branch).

Library values are evaluated at **100 digits** with `mpmath` (`X6_lib.py`) for the PSLQ search,
and in IEEE double with `scipy` (`X6-02-fits.py`, `X6-03-composition.py`) for the dense-grid
fits; candidates are escalated to `mpmath` only if they pass the double-precision screen.

---

## 2. The exact search space

This section is deliberately exhaustive so the search can be extended later.

### 2.1 Moduli and arguments

* **Moduli `c`:** `1/2` (lemniscatic), `1/3`, `(√2−1)² = 3−2√2` (singular modulus), `0.7`.
* **Primary arguments `U_PRIMARY`:** `1/2`, `1`, `3/2` (all `< K(c)` for the four moduli;
  e.g. `K(0.7) = 2.07536…`).
* **Re-test arguments `U_RETEST`:** `3/10`, `7/10`, `9/10`, `6/5`, `7/5`. Used only to
  re-test a relation found at a primary argument (brief rule: a single-`u` relation is a
  coincidence until it survives 5 other `u`).

### 2.2 The library `ℒ` (the 48-name `CORE`) and the move justifying each family

Each family is genuinely P-constructible from `u` and `c` by the moves of
`pptc/Pptc/Defs.lean` / the known black boxes listed in `PLAN-jacobi-X0-overview.md §"Already
known P-constructible"`. `c1 = 1−c`; `c_ℓ` is the descending Landen parameter
`c_ℓ = ((1−√(1−c))/(1+√(1−c)))²`.

| family (names) | value | move / justification |
|---|---|---|
| `u`, `u2`, `pi` | `u`, `u²`, `π` | given `u`; `mul`; `π` black box |
| `sqrt_u`, `sqrt_sin_u` | `√u`, `√(sin u)` | real roots of degree-≤6 polynomials (√ black box) |
| `sin_u`, `cos_u`, `tan_u` | `sin u`, `cos u`, `tan u` | `sine` curve / black boxes; `tan = sin/cos` (`div`) |
| `twou`, `log_u` | `2^u`, `log u` | `exp_two` base curve / `log` black box |
| `arccos_u` | `arccos u` | `arccos` black box (define only for `u ≤ 1`) |
| `F_u_c`, `E_u_c` | `F(u,c)`, `E(u,c)` | forward `ellipticF`/`ellipticE`, known P-constructible |
| `F_u_c1`, `E_u_c1` | `F(u,1−c)`, `E(u,1−c)` | complementary modulus (algebraic in `c`) |
| `F_u_cl`, `E_u_cl` | `F(u,c_ℓ)`, `E(u,c_ℓ)` | Landen modulus (algebraic in `c`) |
| `EAm_u_c`, `EAm_u_c1`, `EAm_u_cl` | `EAm(u,·)` | `ellipticEAm`, the known E-inverse (`Jacobi.lean:602`) |
| `K_c`, `E_c` | `K(c)`, `E(c)` | complete integrals at angle `π/2` |
| `K_c1`, `E_c1`, `K_cl`, `E_cl` | same at `1−c`, `c_ℓ` | algebraic parameter changes |
| `sinF`,`cosF`,`sinE`,`cosE`,`twoF` | `sin/cos/2^(F or E)` | elementary black boxes applied to a constructible value |
| `sqrtF`, `sqrtE` | `√F`, `√E` | √ black box applied to a constructible value |
| `EE`,`FF`,`EF`,`FE` | `E(E(u,c),c)` etc. | depth-2: forward integrals composed |
| `EAmE`, `EAmF` | `EAm(E(u,c),c)`, `EAm(F(u,c),c)` | depth-2 E-inverse composition; `EAmE = u` is the calibration |
| `Fsin`,`Esin`,`Fcos`,`Ecos` | `F/E` of `sin u, cos u` | depth-2 forward integrals |
| `K_cpow`, `E_cpow` | `K(c^u)`, `E(c^u)` | moving modulus `m(u)=c^u`, always in `(0,1)` |
| `K_cu`, `E_cu` | `K(cu)`, `E(cu)` | moving modulus `m(u)=cu`; defined only where `cu<1` |
| `arcL` | `√(1+u²)·E(u²/(1+u²))` | **[symbolic]** arc length of `y = u·sin x` on `[0,π/2]`: `∫₀^{π/2}√(1+u²cos²x)dx = √(1+u²)E(m)`, `m=u²/(1+u²)` |

The full `CORE` list (48 names, in order) is
```
u, u2, sqrt_u, sin_u, cos_u, tan_u, twou, log_u, arccos_u,
F_u_c, E_u_c, F_u_c1, E_u_c1, F_u_cl, E_u_cl,
EAm_u_c, EAm_u_c1, EAm_u_cl,
K_c, E_c, K_c1, E_c1, K_cl, E_cl,
sinF, cosF, sinE, cosE, sqrtF, sqrtE, twoF,
EE, FF, EF, FE, EAmE, EAmF,
Fsin, Esin, Fcos, Ecos,
K_cpow, E_cpow, K_cu, E_cu,
arcL, sqrt_sin_u, pi
```
(The `library()` function also returns `pi` and all of the above; `K_cu`/`E_cu` are `None`
outside their domain.)

Two reduced sub-libraries are used for the expensive combinatorial searches:

* **`PRIME` (16):** `u, sqrt_u, sin_u, cos_u, twou, log_u, F_u_c, E_u_c, F_u_c1, E_u_c1,
  EAm_u_c, EAm_u_c1, arcL, K_c, E_c, K_c1` — all valid on `(0,1.95]` for every modulus.
* **`PRIME3` (10):** `u, sin_u, cos_u, F_u_c, E_u_c, F_u_c1, E_u_c1, EAm_u_c, arcL, K_c` —
  used for the size-3 subsets only.

### 2.3 Targets

`am`, `sn`, `cn`, `dn`, `am_periodic = am − uπ/(2K)`.

### 2.4 Search 1 — fixed-`u` integer relations (PSLQ)

For each modulus and each `u ∈ U_PRIMARY`:

* (a) one PSLQ on the **full `CORE`** vector `[target, CORE…, 1]`, for target `am`;
* (b) PSLQ on **every subset** of `PRIME` of size 1–2 and of `PRIME3` of size 3, vector
  `[target, subset…, 1]`.

Settings: 100 digits (`tol = 10⁻⁸⁵`), `maxcoeff = 10¹²`, `maxsteps = 10⁴`; a hit requires the
target coefficient non-zero and residual `< 10⁻⁸⁰`. Every hit is re-tested at the 5 `U_RETEST`
values for the same `c`; it "holds" only if all five residuals are `< 10⁻⁵⁰`. Hit count per
`(c,u)`: `1 + 5·(C(16,1)+C(16,2)+C(10,3)) = 1281`; total `1281·3·4 = 15{,}372` PSLQ calls.

### 2.5 Search 2 — grid fits

Grids (all moduli): train `u ∈ [0.05,1.40]` (300 points); off-grid fresh points in the same
interval (180 points); **extrapolation** `u ∈ [1.50,1.95]` (120 points). The library was chosen
so that `PRIME` is finite on all of `(0,1.95]`.

* **Subset fit:** for every subset of `PRIME` of size `k ∈ {1,…,6}`, fit
  `target ~ b₀ + Σ bᵢ gᵢ` by least squares (SVD, `rcond=10⁻¹¹`); record train, off-grid and
  extrapolation max-residuals; report the subset minimising the extrapolation residual.
* **Greedy OMP:** orthogonal matching pursuit over the full `CORE`, up to 12 terms, fitting
  train and recording the extrapolation residual at each step.

### 2.6 Search 3 — compositions

For every `g ∈ CORE` (finite on the whole domain) and every
`h ∈ {sin, cos, arcsin, arccos, √, 2^·, log}`, test `target = h(g(u))` on the grid, judged by
extrapolation. Additionally fit a degree-≤2 rational `target ≈ (a g² + b g + c)/(d g + e)` by
total least squares (smallest right singular vector of `[g², g, 1, −target·g, −target]`).

---

## 3. Results — all negative

### 3.1 PSLQ (search 1) — [numeric, 100 digits]

**15,372 calls, 0 raw hits, 0 re-tested relations.** No integer relation of the searched shape
exists among the documented library values at any of the four moduli and three primary
arguments. In particular the full-`CORE` PSLQ for `am` returned nothing, and so did every
subset of size ≤ 2 of `PRIME` and size 3 of `PRIME3`. The results JSON
(`X6-pslq-results.json`) is empty.

### 3.2 Grid fits (search 2)

Subset fits (best subset per `(c,target)`, size ≤ 6 of `PRIME`); the off-grid column is the
minimum seen, the extrapolation column the decisive one:

| `c` | target | best off-grid | best extrapolation |
|---|---|---|---|
| `1/2` | `am` | `2e-4` | `3.3e-4` |
| `1/2` | `sn`,`cn`,`dn` | `1e-4…9e-4` | `1e-4…2.8e-3` |
| `1/2` | `am_periodic` | `4.6e-5` | `1.1e-3` |
| `1/3` | `am` | `2.1e-5` | `3.2e-4` |
| `1/3` | `sn`,`cn`,`dn` | `1e-4…1.6e-3` | `2e-4…1.1e-3` |
| `1/3` | `am_periodic` | `5.1e-5` | `5.8e-4` |
| `(√2−1)²` | `am` | `2.0e-6` | `3.6e-5` |
| `(√2−1)²` | `am_periodic` | `2.1e-7` | `1.7e-5` |
| `(√2−1)²` | `sn`,`cn`,`dn` | `7.8e-5…9.5e-4` | `1.3e-4…8.2e-4` |
| `0.7` | `am` | `1.1e-5` | `2.8e-4` |
| `0.7` | `sn`,`cn`,`dn` | `7e-5…1.1e-3` | `1.1e-4…2.1e-3` |
| `0.7` | `am_periodic` | `5.3e-5` | `2.1e-4` |

The singular modulus `(√2−1)²` gives the smallest off-grid residuals (down to `2·10⁻⁷` for the
periodic part), but the extrapolation residual remains `≥ 1.7·10⁻⁵`, i.e. **ten orders of
magnitude larger than a true identity** (`~10⁻¹²–10⁻¹⁴`). Greedy OMP over the full `CORE`
(12 terms) reached train residuals `2·10⁻⁸…3·10⁻⁷` while the extrapolation residual stayed at
`7·10⁻⁵…3·10⁻²`. **No candidate below the `10⁻⁸` acceptance threshold.**

### 3.3 Composition search (search 3)

**0 hits.** The best extrapolation residuals were `~10⁻²–10⁻³` (`arccos(cosE)`,
`sin(E_u_c)`, `cos(E_u_c)`, `rat2(sqrtE)`), i.e. not identities. Nothing composed of a single
library function with an elementary map reproduced a target.

### 3.4 Methodology caveat — full-library fits are misleading [numeric]

Fitting the target against the whole `CORE` (`48` columns) on the dense train grid produces an
apparently perfect `~10⁻¹⁴` residual both on train and on the off-grid points. This is an
artifact: the library has **effective numerical rank 17–20 of 48** (`CORE` is massively
collinear — e.g. at `c=1/2`, `F_u_c = F_u_c1` and `E_u_c = E_u_c1` exactly; `EAmE = u`; the
`F/E/EAm` families are nearly linearly dependent). The minimum-norm least-squares solution uses
the large nullspace to interpolate the target within the training interval.

* Demonstration (`c=1/2`, full `CORE`, target `am`): effective rank `18`, train `4.7·10⁻¹⁴`,
  off-grid `2.8·10⁻¹⁴`, **extrapolation `3.6·10⁻⁴`**. Similar at `c=1/3` (rank 17,
  extrap `1.5·10⁻⁵`) and at `(√2−1)²` (rank 17, extrap `1.2·10⁻⁵`).
* The remedy, and the method actually used for the verdict, is (i) small well-conditioned
  subsets, whose design matrices have (near-)full column rank, and (ii) an **extrapolation**
  test, which an exact functional identity survives and a numerical overfit does not.

---

## 4. Special-argument partial results (search 4) — [numeric, verified to 350 digits]

Script `X6-04-special.py`. At `u = mK/n`, `x = sn(u,c)` is algebraic; if it is a root of a
degree-≤6 polynomial with P-constructible coefficients then `sn(u,c)`, and hence
`am(u,c) = arcsin(sn(u,c))`, is P-constructible (`arcsin/arccos` is a known black box). We
find the minimum degree over `ℚ` and over `ℚ(s)` with `s = √(1−c)` (coefficients in `ℤ[s]`)
by incremental PSLQ.

**Spurious-relation control (important).** A PSLQ relation among `k` numbers at precision `D`
is only trustworthy when the coefficient bound `M ≪ 10^{D/k}`; otherwise a chance relation of
size `~10^{D/k}` appears. An initial run at `D=100`, `M=10^{15}` (the settings of searches 1–3)
produced false degree-3 relations with coefficients `~10^{11}` (`k≈8`, chance floor
`10^{100/8}≈10^{12.5}`). All such results are discarded. The reported run uses `D=160`,
`M=10^8` (`k≤14` ⇒ floor `10^{11.4}`) and **independently re-verifies every relation at
`D=350`**, requiring residual `< 10^{−280}`; a 160-digit coincidence survives only to
`~10^{−160}` and is rejected. A second bug worth recording: verification must rebuild the
modulus `c` at 350 digits from its exact rational (`1/2` is exact in binary, but `1/3`, `7/10`
are not, so passing a 160-digit `c` silently caps the verifier at 160 digits).

**Results** (`degQ` = degree over `ℚ`, `degZ[s]` = degree over `ℚ(√(1−c))`; `>6` = no relation
found with degree ≤ 6, `maxcoeff 10^8`, verified):

| `u` | `c=1/2` | `c=1/3` | `c=7/10` | covered by deg-≤6 engine? |
|---|---|---|---|---|
| `K/2` (`m=1,n=2`) | degQ 4, degZ[s] **2** | degQ 4, degZ[s] **2** | degQ 4, degZ[s] **2** | **yes** (`x²(1+s)=1`) |
| `K/3` (`m=1,n=3`) | degQ **4**, degZ[s] 4 | degQ **4**, degZ[s] 4 | degQ **4**, degZ[s] 4 | **yes** (quartic, see below) |
| `2K/3` (`m=2,n=3`) | >6 | >6 | >6 | no (single polynomial) |
| `K/4` (`m=1,n=4`) | >6 | >6 | >6 | no (but see note) |
| `3K/4` (`m=3,n=4`) | >6 | >6 | >6 | no |
| `mK/5`, `m=1..4` | >6 | >6 | >6 | no |
| `K/6`, `5K/6` | >6 | >6 | >6 | no |
| `K/7`, `2K/7` | >6 | >6 | >6 | no |
| `K/8`, `2K/8` | >6 | >6 | >6 | no |

**Positive partial results.**

* `u = K/2` **[symbolic + numeric, 350 digits]:** the universal identity
  `sn(K/2,c)² = 1/(1+√(1−c))` gives `(1+s)x² − 1 = 0`, degree 2 over `ℚ(s)`, at all three
  moduli. (Already known constructible; confirms the search calibrates.)
* `u = K/3` **[numeric, 350 digits]:** `sn(K/3,c)` is a root of a **quartic with rational
  coefficients** at each tested `c` (the `s`-generator does not lower the degree):
  `c=1/2: x⁴−2x³+4x−2 = 0`; `c=1/3: x⁴−2x³+6x−3 = 0`;
  `c=7/10: 7x⁴−14x³+20x−10 = 0`. All have the shape `x⁴−2x³+(linear in c)x−const`, suggesting a
  single quartic family with `P`-constructible coefficients; if so, `am(K/3)` is
  P-constructible for P-constructible `c`. This is the one **new** positive lead from X6. It is
  numerical at three moduli, not yet proved symbolically in `c`.

**Non-results, stated precisely.** For every other listed `(m,n)`, neither `sn(mK/n)` nor the
`ℚ(s)`-variant satisfies a degree-≤6 relation with coefficients below `10^8` (verified at 350
digits). This does **not** prove non-constructibility: the degree-≤6 engine can be applied in a
*chain*, and R3 §5 fact 4 constructs `am(K/2^j)` by iterated halving precisely this way (the
halving quartic is degree ≤6 even though the minimal polynomial of `sn(K/4)` alone exceeds
degree 6). The dyadic arguments `K/2^j` are therefore already known constructible, and their
`>6` entries here just mean the *single*-polynomial route is not what does it.

---

## 5. The precise negative statement

**Excluded class.** Let `ℒ` be the 48-name library of §2.2, all of whose members are
P-constructible from a P-constructible `u` and `c` by the moves of `Defs.lean` and the known
black boxes. Let `S` be the set of real functions of `u` that can be written either as

* a fixed real-coefficient linear combination of members of `ℒ` (or, for the greedy test, a
  sparse combination of at most 12 members), on an interval where all members are defined; or
* a composition `h(g(u))` with `g ∈ ℒ` and `h ∈ {sin, cos, arcsin, arccos, √, 2^·, log}`; or
* a degree-≤2 rational function of a single `g ∈ ℒ`.

Then no element of `S` equals `am(u,c)`, `sn`, `cn`, `dn` or `am(u,c) − uπ/(2K)` on
`[0.05,1.95]` at `c ∈ {1/2, 1/3, (√2−1)², 0.7}`. Equivalently, no such cheap formula was found;
every fitting candidate failed the extrapolation test.

**Which assumption would let a construction through.** An identity that is *nonlinear in
several* library functions at once (a product/quotient/composition of two or more different
special functions, not expressible as a single-variable rational of one library element), or
one using a function outside the documented 48 (`Pptc/Defs.lean` has no polar plot, no Jacobi
curve, no curve of pure first-kind arc length — the Serret gap). X1 proved `am` is not
D-finite, so any successful formula must live in the transcendental fragment; X3 and R3 show
that the named classical mechanisms supply at most forward `E/F` or an `E`-inverse, never the
inverse of `F`. Nothing here closes those doors; this note closes only the finite library above.

**Scope caveats.** (i) The verdict is numerical: PSLQ at 100 digits and double-precision fits
with an extrapolation filter; it is a search result, not a theorem. (ii) The full-library
real-coefficient membership question cannot be settled by a dense least-squares residual (it is
rank-deficient, §3.4); it is covered here by the greedy 12-term OMP and by the 100-digit PSLQ
over the full `CORE`, both negative. (iii) Non-integer real coefficients involving new
transcendental constants are not enumerated.

---

## 6. Scripts and verification index

| script | contents | status |
|---|---|---|
| `X6_lib.py` | 100-digit library (`CORE` 48, `PRIME` 16, `PRIME3` 10), `targets`, moduli/`u` sets, `EAm` by monotone root-finding | rerunnable, `python X6_lib.py` smoke test |
| `X6-01-pslq.py` | fixed-`u` PSLQ (search 1); args `[subset_max] [modulus]`; appends to `X6-pslq-results.json` | ran 4×; 15,372 calls, 0 hits |
| `X6-02-fits.py` | subset fits and greedy OMP (search 2); arg `[KSUB]`; includes the ill-conditioning demonstration | ran; all extrapolation residuals `≥10⁻⁵` |
| `X6-03-composition.py` | composition + degree-≤2 rational search (search 3) | ran; 0 hits |
| `X6-04-special.py` | special arguments `mK/n` (search 4): min degree over `ℚ` and `ℚ(√(1−c))`, spurious-relation control, 350-digit re-verification | ran; `K/2`, `K/3` positive, rest `>6` |
| `X6-pslq-results.json` | accumulated PSLQ hits | empty |

**Independent re-check.** The two decisive searches were re-run from the archived scripts on
this machine: the PSLQ sweep (all four moduli) again produced zero hits, and the fit script
again showed the train/off-grid vs extrapolation split (e.g. `c=1/2`, `am`: off-grid
`~3·10⁻¹⁴` in the rank-deficient full-`CORE` fit versus extrapolation `3.6·10⁻⁴`; small subsets
`>10⁻⁶`). No result here depends on a single unverified run.

**References.** DLMF §22.16 (amplitude), https://dlmf.nist.gov/22.16 ; prior programme notes
`NOTES-jacobi-R3.md` (composition test, loopholes), `NOTES-jacobi-X1.md` (`am` not D-finite),
`NOTES-jacobi-X3.md` (classical mechanisms), `NOTES-jacobi-X4.md` (constructor audit);
`Pptc/Jacobi.lean` (`ellipticEAm`, addition closure), `Pptc/Defs.lean` (moves).
