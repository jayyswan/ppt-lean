# NOTES-hypergeometric-R4c

**Inbound survey: `sine` / `exp_two` / `rectangle` arcs as ₂F₁ (R4).**

Research note, wave 2, task R4c. No `.lean` file was edited, created or deleted.
No lake build, no lean-lsp tool was used.

Every identity below is labelled:

* **[NC n]** numerically checked to `n` significant digits with the **Wolfram Language
  kernel** (script `archived files/hypergeometric-scripts/R4c-01-sine-exp-rect.wl`);
* **[SY]** proved symbolically here (the proof is written out);
* **[CL]** classical (from the literature, cited);
* **[SP]** speculative / not established.

Sources read: `AGENTS.md`; `PLAN-hypergeometric-00-overview.md` (§1, §2 V1–V7, §4 H6,
§5 B1/B6, §6 R4); `NOTES-hypergeometric-R1.md` (built on, not re-derived);
`Pptc/Defs.lean` (`speed` 68, `arcLengthOf` 72, `sine` 218, `exp_two` 203, `rectangle` 183,
`restrict` 295, `scale_x/scale_y` 267/270, `translate_x/translate_y` 251/254);
`Pptc/Basic.lean` (`rpow_two_Pconstructible` 1744, `cos_Pconstructible` 2645,
`sin_Pconstructible` 2650); class signatures `hyp_elliptic_class_Pconstructible`
(`EllipticClass.lean:521`) and `hyp_graphFamily_class_Pconstructible`
(`GraphsClass.lean:765`).

Conventions. Mathematica's `EllipticE[phi, m]` takes the **parameter** `m = k²`, matching
this repo's `c = k²` (`ellipticE c φ`). The prime is always `d/dz`.

Scripts (all in `archived files/hypergeometric-scripts/`):

| script | contents |
|---|---|
| `R4c-01-sine-exp-rect.wl` | all checks below (§1–§4) |

---

## 0. Answers in brief

1. **`sine` — no new ₂F₁.** The arc length is `∫ₐᵇ √(1+cos²t) dt = √2 (E(b|½) − E(a|½))`,
   an **incomplete** elliptic integral of the second kind, hence an **Appell F₁**
   (`sinφ·F₁(½; ½, −½; 3/2; sin²φ, ½ sin²φ)`) and *not* a ₂F₁ [PLAN §1], [NC 40]. The only
   ₂F₁ values it produces are the **complete** sub-arcs, where
   `√2 E(½) = (π/√2) ₂F₁(−½, ½; 1; ½)` [NC 40] — parameters `(−½, ½; 1)` with `c = 1`,
   already inside the landed **elliptic class** `(½+ℤ, ½+ℤ, 1+ℕ)`
   (`hyp_elliptic_class_Pconstructible`, `i = −1, j = 0, k = 0`, at `z = ½`). Affine images
   `y = A sin(Bx+C)+D` give the same class at the arbitrary P-constructible parameter
   `k² = A²B²/(1+A²B²)`, so they add no new family either.
2. **`exp_two` — no ₂F₁ at all.** The arc length
   `∫ₐᵇ √(1+(ln2)² 2^{2t}) dt` is **elementary**: with `u = (ln2)·2^t` it is
   `(1/ln2)[√(1+u²) − arsinh(1/u)]` between `u(a), u(b)` [SY], [NC 40]. There is no finite
   complete period (the integrand diverges as `x → ∞`). No ₂F₁.
3. **`rectangle` — no ₂F₁.** The boundary is four straight segments; `restrict` isolates an
   edge, whose length is a difference of P-constructible coordinates. Affine images of a line
   are lines. No ₂F₁.
4. **Endpoints are P-constructible**, so the results are usable: `(x, sin x)` and `(x, 2^x)`
   are P-constructible points for P-constructible `x` (`sin_Pconstructible`; `rpow_two_Pconstructible`),
   and rectangle corners are P-constructible by construction.
5. **No complete-period sub-arc sneaks in a new complete elliptic integral.** The only
   complete periods available are `√2 E(½)`, `2√2 E(½)`, `4√2 E(½)` (quarter, half and full
   period of the sine), all proportional to the single landed value
   `E(½) = (π/2) ₂F₁(−½,½;1;½)`; the exponential has none.

**Verdict: no new ₂F₁ source.** The obstruction is structural, not a missing trick: the sine
arc-length density is the *second-kind* density `√(1+cos²t)`, whose *incomplete* integral is a
two-variable Appell `F₁` (so it is not a ₂F₁ at all) and whose *complete* integral is the
already-landed Legendre `E = ₂F₁(−½,½;1;k²)`; and the exponential/rectangle densities are
elementary (Chebyshev's criterion, PLAN §2 [CL]), so they never leave the elementary class.

---

## 1. The arc-length integrals and their classification

### 1.1 `sine`: `y = sin x`

Parametrize the graph by abscissa: `γ(t) = (t, sin t)`, `y' = cos t`, so
`speed γ t = √(1 + cos²t)`. Over `[a, b]`,

```
∫ₐᵇ √(1 + cos²t) dt.
```

Use `cos²t = 1 − sin²t` and factor out the constant:

```
√(1 + cos²t) = √(2 − sin²t) = √2 · √(1 − ½ sin²t).
```

With `E(φ|m) = ∫₀^φ √(1 − m sin²θ) dθ` (`m = k²`),

> **sine arc length**  `∫ₐᵇ √(1+cos²t) dt = √2 (E(b|½) − E(a|½))`.   **[SY] + [NC 40]**

`R4c-01-sine-exp-rect.wl` compares this against `NIntegrate` at 40 working digits for
`[a,b] = [0,1], [1/3,5/4], [−2/5,7/3], [0,π/2], [0,π], [0,2π]`; every deviation is `0` at
40 digits (≤ `10^{-39}`).

**Classification: incomplete `E` is Appell `F₁`, not ₂F₁.** By PLAN §1,
`E(φ|m) = sinφ · F₁(½; ½, −½; 3/2; sin²φ, m sin²φ)`, a genuine two-variable function. Checked
here directly: at `φ = 7/10`, `m = ½`,

```
E(7/10 | ½) = 0.6731891745471288228679746848050535794582
sin(7/10)·F₁(½; ½, −½; 3/2; sin²(7/10), ½ sin²(7/10)) = 0.6731891745471288228679746848050535794582
```

difference `0` at 40 digits. **[CL] (PLAN §1) + [NC 40]**. So the *incomplete* sine integral
is out of the ₂F₁ programme, exactly as the incomplete `F`, `Π` cases are.

### 1.2 `sine`: complete-period values

Since `sin²` has period `π` and `√(1+cos²t) = √(2−sin²t)` is a function of `sin²t`, the
half-period integral repeats. With `E(m) = E(π/2|m)` the complete second-kind integral,

| interval | value | numeric |
|---|---|---|
| `[0, π/2]` | `√2 · E(½)` | `1.910098894513856008952381041085721645955` |
| `[0, π]` | `2√2 · E(½)` | `3.820197789027712017904762082171443291910` |
| `[0, 2π]` | `4√2 · E(½)` | `7.640395578055424035809524164342886583820` |

`[SY] + [NC 40]` (closed forms match quadrature to 40 digits).

By V1–V2 (`E(m) = (π/2) ₂F₁(−½, ½; 1; m)`, `PLAN §2`),

> **`∫₀^{π/2} √(1+cos²t) dt = √2 E(½) = (π/√2) ₂F₁(−½, ½; 1; ½)`.**   **[CL] + [NC 40]**

The right side is `1.910098894513856008952381041085721645955`, identical to `√2 E(½)` at
40 digits. The parameter `c = k² = ½` is P-constructible, so `E(½)` — equivalently this ₂F₁
value — is P-constructible; in fact `ellipticE` complete at a P-constructible parameter is
already in `Basic.lean`.

### 1.3 `sine`: affine images `y = A sin(Bx+C) + D`

`Defs.lean:205–210` states that the general `y = A sin(ωx+φ)+c` with P-constructible
`A, ω, φ, c` is reached from `sine` by `scale_y` (amplitude), `scale_x` (frequency),
`translate_x` (phase), `translate_y` (offset). For `γ(t) = (t, A sin(Bt+C)+D)` the slope is
`A B cos(Bt+C)`, so

```
speed = √(1 + A²B² cos²(Bt+C)).
```

Substituting `u = Bt + C` (for `B ≠ 0`, `du = B dt`) and using `cos²u = 1 − sin²u`,

```
1 + A²B² cos²u = 1 + A²B² − A²B² sin²u = (1 + A²B²)(1 − k² sin²u),
      k² := A²B² / (1 + A²B²)  ∈ [0, 1).
```

Hence

> **affine sine arc length**
> `∫ₐᵇ √(1 + A²B² cos²(Bt+C)) dt
>   = (√(1+A²B²)/|B|) (E(Bb+C | k²) − E(Ba+C | k²))`.   **[SY] + [NC 40]**

Checked at 40 digits for `(A,B,C,a,b) = (3/2, 2, 1/3, 0, 1)`, `(5/7, 3/2, −2/5, −1/3, 4/5)`,
`(1,1,0,0,π/2)`, `(1,1,0,0,π)`; all deviations `0`. The modulus `k² = A²B²/(1+A²B²)` is an
arbitrary P-constructible number in `[0,1)` (the map `A²B² ↦ A²B²/(1+A²B²)` is onto), so
this is *the* second-kind family with modulus ranging over P-constructible values.

The **complete** quarter-period value is

```
(√(1+A²B²)/|B|) · E(k²) = (√(1+A²B²)/|B|) · (π/2) ₂F₁(−½, ½; 1; k²),
```

again `(−½, ½; 1)` with arbitrary P-constructible modulus. **[SY] + [NC 40]** (checked at
`(A,B) = (3/2,2)`, `k² = 9/10`; `(5/7,3/2)`, `k² = 225/421`; `(1,1)`, `k² = ½`; deviation 0).

**Rotation adds nothing.** `rotate` is conformal (it is a Euclidean isometry), so it
preserves `speed` pointwise; the rotated sine graph has exactly the same arc-length density
along the corresponding arc. Only the anisotropic maps `scale_x`, `scale_y` change the
integrand, and they only produce the `A, B` above.

### 1.4 `exp_two`: `y = 2^x`

Parametrize `γ(t) = (t, 2^t)`. Since `d/dt 2^t = (ln2)·2^t`,

```
speed γ t = √(1 + (ln2)² 2^{2t}).
```

Substitute `u = (ln2)·2^t`; then `du = (ln2)² 2^t dt = (ln2)·u dt`, so `dt = du / ((ln2) u)`:

```
∫ √(1 + (ln2)² 2^{2t}) dt = (1/ln2) ∫ √(1+u²)/u du.
```

**Elementary antiderivative [SY].** With `w = √(1+u²)`, `dw = (u/w) du`, i.e.
`du = (w/u) dw` and `u = √(w²−1)`:

```
∫ √(1+u²)/u du = ∫ (w²/(w²−1)) dw = ∫ (1 + 1/(w²−1)) dw = w + ½ ln|(w−1)/(w+1)| + C.
```

Equivalently, since `(w−1)/u = u/(w+1)` (as `w²−1 = u²`), and `arsinh(1/u) = ln((1+w)/u)`
for `u > 0`:

> **`∫ √(1+u²)/u du = √(1+u²) − arsinh(1/u) + C
>                     = √(1+u²) + ½ ln((√(1+u²)−1)/(√(1+u²)+1)) + C`**   **[SY]**

The second form is the task's `artanh` form, `½ ln((w−1)/(w+1)) = −artanh(1/w)`. `FullSimplify`
of `d/du[√(1+u²) − arsinh(1/u)] − √(1+u²)/u` on `u > 0` returns exactly `0`.

Therefore

> **exp arc length**
> `∫ₐᵇ √(1+(ln2)² 2^{2t}) dt
>   = (1/ln2) [ √(1+u²) − arsinh(1/u) ]_{u=(ln2)2^a}^{(ln2)2^b}`.   **[SY] + [NC 40]**

Checked at 40 digits for `[a,b] = [0,1], [1/3,5/4], [−1/3,3/2]`; deviation `0` everywhere.
**Elementary, so no ₂F₁.** By Chebyshev's criterion (PLAN §2 [CL]), `∫ u^{p}(α+βu²)^{q}du`
is elementary when one of `(p+1)/m`, `q`, `(p+1)/m+q` is an integer; here `p = −1`, `m = 2`,
`q = ½`, and `(p+1)/m = 0 ∈ ℤ`, which is the present case.

**No finite complete period.** The integrand is increasing and `√(1+(ln2)²2^{2t}) → ∞` as
`t → ∞` like `(ln2)2^t`, so `∫₀^∞` diverges. There is no complete value, elliptic or
otherwise. **[SY]**

**Affine images.** For `(x,y) ↦ (σx+τ, Ay+δ)` the image is parametrized
`(σt+τ, A·2^t+δ)` with speed `|σ|√(1 + (A ln2/σ)² 2^{2t})` (`σ ≠ 0`), the same elementary
form with a rescaled constant; `σ = 0` or `A = 0` gives a straight segment. A rotation is
conformal and leaves `speed = √(1+(ln2)²2^{2t})` unchanged. No ₂F₁. **[SY]**

### 1.5 `rectangle`

The rectangle constructor (`Defs.lean:183–192`) is the **boundary**: four straight edges.
Isolate one with `restrict`. A straight edge parametrized `γ(t) = p + t·(q−p)` has constant
speed `|q−p|`, so

```
arcLengthOf γ 0 1 = |q − p| = √((q₁−p₁)² + (q₂−p₂)²),
```

a P-constructible number when the corners are (`dist_Pconstructible`). **[SY]** No ₂F₁, and
no complete elliptic integral. Affine images of a line are lines, so `scale_x`, `scale_y`,
`translate_x`, `translate_y`, `rotate` preserve straightness and the conclusion. **[SY]**

---

## 2. ₂F₁ verdict per curve

| curve | arc-length integral | closed form | ₂F₁? | parameter identity |
|---|---|---|---|---|
| `sine` (incomplete) | `∫ₐᵇ √(1+cos²t)dt` | `√2(E(b|½)−E(a|½))` | **no** — Appell `F₁` | `sinφ·F₁(½;½,−½;3/2;sin²φ,½sin²φ)` |
| `sine` (complete) | `∫₀^{π/2}` | `√2 E(½)` | **yes** | `(π/√2)₂F₁(−½,½;1;½)` |
| `sine` (affine, incomplete) | `∫ √(1+A²B²cos²(Bt+C))dt` | `(√(1+A²B²)/|B|)ΔE` | **no** — Appell `F₁` | same, modulus `k²=A²B²/(1+A²B²)` |
| `sine` (affine, complete) | `[Bx+C]` over quarter period | `(√(1+A²B²)/|B|)E(k²)` | **yes** | `(√(1+A²B²)/|B|)(π/2)₂F₁(−½,½;1;k²)` |
| `exp_two` | `∫ₐᵇ √(1+(ln2)²2^{2t})dt` | `(1/ln2)[√(1+u²)−arsinh(1/u)]` | **no** — elementary | — |
| `rectangle` edge | `∫₀¹|q−p|dt` | `|q−p|` | **no** — elementary | — |

The only ₂F₁ parameters that occur are `(a, b; c) = (−½, ½; 1)`; the only freedom is the
argument `z = k²` (resp. `½`). These are the Legendre `E` family, and no other parameter
combination arises from any of the three curves or their affine images.

---

## 3. Already covered by the landed classes?

The two landed classes are

* `hyp_elliptic_class_Pconstructible` (`EllipticClass.lean:521`):
  `₂F₁(½+i, ½+j; 1+k; z)` for `i, j : ℤ`, `k : ℕ`, P-constructible `z ∉ {0,1}`, `|z| < 1`;
* `hyp_graphFamily_class_Pconstructible` (`GraphsClass.lean:765`):
  `₂F₁(−½+i, 1/(2n−2)+j; 1+1/(2n−2)+k; −b²X^{2n−2})` for `n ∈ {3,…,6}` (so the power is
  `1/m` with `m = 2n−2 ∈ {4,6,8,10}`), with the indicated side conditions.

* **Sine, complete.** `(−½, ½; 1; k²)` is `(½+(−1), ½+0; 1+0)` — the elliptic class with
  `i = −1`, `j = 0`, `k = 0`. **Covered** (for any P-constructible modulus `k² ∈ (0,1)`,
  including `z = ½` from the standard sine). It is *not* in the graph family: that needs
  `b = 1/(2n−2)+j = ½`, i.e. `2n−2 = 2` (`n = 2`, excluded — `n = 2` is the degenerate case
  the class theorem excludes) and `c = 1 + 1/(2n−2) + k`, which is never `1`. The sine's ₂F₁
  also sits at a **positive** argument (`+½`), whereas the graph family's argument is
  `−b²X^{2n−2} ≤ 0`.
* **`sine`, incomplete.** Appell `F₁`, not a ₂F₁, so **neither class applies**; it is outside
  the programme's scope exactly as PLAN §1 states for `ellipticE c φ`.
* **`exp_two`, `rectangle`.** No ₂F₁ value at all.

So every ₂F₁ value these curves produce is already inside the elliptic class, and nothing new
appears. In particular the affine modulus `k² = A²B²/(1+A²B²)` ranges over the whole
P-constructible subset of `(0,1)`, but the *parameters* stay `(−½, ½; 1)`, so no new family
(unlike H6, where `b = 1/m` moves with the family).

---

## 4. Label ledger

| statement | label |
|---|---|
| sine density and reduction `√(1+cos²t)=√2√(1−½sin²t)` (§1.1) | [SY] + [NC 40] |
| `∫ₐᵇ√(1+cos²t)dt = √2(E(b\|½)−E(a\|½))` (§1.1) | [SY] + [NC 40] |
| incomplete `E` is Appell `F₁`, not ₂F₁ (§1.1) | [CL] (PLAN §1) + [NC 40] |
| complete periods `√2·2^{j}E(½)` (§1.2) | [SY] + [NC 40] |
| `E(m) = (π/2)₂F₁(−½,½;1;m)` (§1.2) | [CL] (V1–V2) + [NC 40] |
| affine sine closed form, modulus `A²B²/(1+A²B²)` (§1.3) | [SY] + [NC 40] |
| affine complete quarter-period `= (π/2)₂F₁(−½,½;1;k²)` (§1.3) | [SY] + [NC 40] |
| rotation is conformal / preserves speed (§1.3, §1.4) | [SY] |
| exp substitution `u=(ln2)2^t` (§1.4) | [SY] |
| `∫√(1+u²)/u du = √(1+u²) − arsinh(1/u)` elementary (§1.4) | [SY] (FullSimplify residual 0) + [NC 40] |
| exp arc length closed form vs quadrature (§1.4) | [SY] + [NC 40] |
| `∫₀^∞` of the exp density diverges (§1.4) | [SY] |
| Chebyshev elementarity, `p=−1, m=2, q=½`, `(p+1)/m=0∈ℤ` (§1.4) | [CL] |
| rectangle edge `= \|q−p\|`, affine image still straight (§1.5) | [SY] |
| endpoints P-constructible: `sin_Pconstructible`, `rpow_two_Pconstructible` (§0.4) | [SY] (Basic.lean) |
| sine family in elliptic class, not graph family (§3) | [SY] (parameter comparison) + [NC 40] |

No `sorry`, no Lean file touched. Every number above is from the Wolfram kernel
(`R4c-01-sine-exp-rect.wl`); no Python fallback was needed.

---

## 5. Scripts

| script | backend | contents |
|---|---|---|
| `archived files/hypergeometric-scripts/R4c-01-sine-exp-rect.wl` | Wolfram Language | symbolic antiderivative; Appell `F₁` form of incomplete `E`; `E(m)=(π/2)₂F₁`; sine closed form vs 40-digit quadrature; complete periods; affine sine closed form vs quadrature; affine complete reduction to ₂F₁; exp antiderivative `FullSimplify` residual; exp closed form vs quadrature; rectangle edge. |

---

## 6. Caveats

* **Only the elliptic class is touched.** The programme's other landed class (the graph
  family) is not reached by any curve here, because the sine/exponential/rectangle densities
  never produce `b = 1/m` with `m ∈ {4,6,8,10}`.
* **Incomplete `E` is out of scope by design.** This is not a negative result about
  P-constructibility — `E(φ|m)` *is* P-constructible for P-constructible `φ, m` (it is an arc
  length). It is simply an Appell `F₁`, so it neither uses nor feeds the ₂F₁ programme.
* **No coincidence loophole identified.** A single finite sine arc could in principle carry a
  value that coincides with some other ₂F₁, but the density is fixed (`√(1+cos²t)`, second
  kind) and no mechanism here selects such an arc; as in R1, the project cannot rule out a
  coincidence, and none is claimed.
* **The affine modulus is genuinely free** (`k²` any P-constructible value in `(0,1)`), so
  the sine does populate the elliptic `E` family at *every* P-constructible modulus. That is
  a statement about the argument `z`, not about new parameters, and the elliptic class
  already covers it uniformly.
