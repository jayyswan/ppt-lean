# NOTES-hypergeometric-R3

**Watson/Pólya reduction; check bcc/fcc formulas (B5).**

Research note, wave 0, task R3. No `.lean` file was edited, created or deleted.
Every identity below is labelled:

* **[NC n]** numerically checked to `n` significant digits (scripts in
  `archived files/hypergeometric-scripts/`, run with `py R3-*.py`);
* **[SY]** proved symbolically here (the proof is written out);
* **[CL]** classical (taken from the literature and cited, not re-derived);
* **[SP]** speculative / assessment, not a mathematical claim.

Sources read: `AGENTS.md`, `PLAN-hypergeometric-00-overview.md` (V11; B5),
`NOTES-hypergeometric-R1.md` (not duplicated), `NOTES-hypergeometric-R2.md`,
`pptc/Pptc/Hypergeometric/Polya.lean` (L8, already landed),
`pptc/Pptc/Gamma.lean`, `pptc/Pptc/Tactic.lean`, and `pptc/Pptc/Basic.lean`
(`ellipticF_pi_div_two_Pconstructible`, `rpow_Pconstructible`).

Literature: Watson, *Three triple integrals*, Quart. J. Math. **10** (1939)
266–276; Glasser & Zucker, *Extended Watson integrals for the cubic lattices*,
Proc. Nat. Acad. Sci. USA **74** (1977) 1800–1801; Montroll, *Random walks in
multidimensional spaces…*, J. SIAM **4** (1956) 241–260; Guttmann, *Lattice Green
functions in all dimensions*, J. Phys. A **43** (2010) 305205; Ishioka & Koiwa,
Phil. Mag. A **37** (1978) 517–533. Constants from OEIS A086230, A086231,
A091670, A091671, A091672, A293237, A293238.

Scripts (all in `archived files/hypergeometric-scripts/`):

| script | contents |
|---|---|
| `R3-01-sc-polya.py` | `u(3)`, `p(3)`: Gamma / K / theta / direct integral / return series / Bessel integral |
| `R3-02-bcc-fcc.py` | bcc and fcc Watson integrals, return numbers, K-forms, plan verdict |
| `R3-03-mods-and-k3.py` | quartic roots of `k₆`; `K(sin π/12)`; `K(m₊)=√3K(m₋)` |

> Note. A pre-existing draft `R3-watson-checks.py` was found in the scripts
> directory (no note or handoff accompanied it, so it is an aborted run). It is
> **superseded** and contains at least three defects: (i) it claims the simple-cubic
> return series tail after `n=90` is `< 10^{-40}`, but that partial sum is off by
> `0.049` (the terms decay like `n^{-3/2}`); (ii) it compares `p(3)` against a value
> `0.340537329550999142835175…` that is wrong from the **21st digit** (the correct
> value is OEIS A086230, `…142826273…`); (iii) its direct-integral section crashes
> with `ZeroDivisionError` (a `1-cos` cancellation at the endpoint). Its fcc
> *verdict* (that the plan's constant is `u_fcc/3`) happens to be correct.

---

## 0. Answers in brief

1. **Simple cubic.** The V11 closed forms are correct. The Gamma product, the
   `K(k₆)` form, the `θ₃` form and the defining integrals all agree to ~100 digits
   (§1). `p(3) = 0.340537329550999142826273184432902896…` is OEIS A086230.

2. **bcc candidate `Γ(1/4)⁴/(4π³)` is CORRECT.** It is Watson's first triple
   integral `I₁` **[CL]** and equals the bcc lattice return number `u_bcc`
   **[SY]** (OEIS A091670; escape probability A293238). See §2.

3. **fcc candidate `3Γ(1/3)⁶/(2^{14/3}π⁴)` is `I₂`, Watson's second triple
   integral — and is NOT the fcc return number.** The fcc return number is
   `u_fcc = 3 I₂ = 9Γ(1/3)⁶/(2^{14/3}π⁴)` **[SY]**, i.e. the plan's constant is
   **off by a factor 3**. The escape probability `1/u_fcc = 2^{14/3}π⁴/(9Γ(1/3)⁶)`
   is exactly OEIS A293237 **[NC 60]**. See §3.

4. **Formalizability.** Both Γ forms are directly `PConstructible` and the
   `pconstructible` tactic closes them (tested), as does the bcc K-form. The fcc
   K-forms are formalizable but the tactic does **not** discharge the side condition
   `(2−√3)/4 < 1`; they need an explicit `have` like L8's `k6_sq_lt_one`. The Watson
   integral itself is out of scope. Concrete L8 recommendation in §5.

5. **Defining Bessel integral.** `∫₀^∞(e^{−t/3} I₀(t/3))³ dt = u(3)`. Redirecting
   the quadrature over `[0,∞)` reaches ~52 digits; the finite-range-plus-asymptotic
   tail ("tail-limited") approach reaches only ~14 digits at `T = 1600` (§4).

**Why the three lattices differ.** For a lattice with neighbour set `Δ` and
coordination `z`, the number of `n`-step returns is the constant term
`a_n = CT[(Σ_{δ∈Δ} e^{i k·δ})^n]`, so
`u = Σ a_n/z^n = (1/(2π)³)∫_{[0,2π]³} dk / (1 − z^{-1}Σ_{δ} e^{i k·δ})` **[SY]**.
Reducing the denominator (sc takes `θ = k`; bcc and fcc take `θ = k/2`):

| lattice | `z` | `u = (1/π³)∫_{[0,π]³} (…) dθ` | equals |
|---|---|---|---|
| sc  | 6  | `(1 − (cosθ₁+cosθ₂+cosθ₃)/3)^{-1}` | `3 I₃` |
| bcc | 8  | `(1 − cosθ₁ cosθ₂ cosθ₃)^{-1}` | `I₁` |
| fcc | 12 | `(1 − (cosθ₁cosθ₂+cosθ₂cosθ₃+cosθ₃cosθ₁)/3)^{-1}` | `3 I₂` |

with `I₁,I₂,I₃` Watson's three triple integrals (all over `[0,π]³`):
`I₁ = (1/π³)∫∫∫ (1−cos u cos v cos w)^{-1}`,
`I₂ = (1/π³)∫∫∫ (3−cos v cos w−cos w cos u−cos u cos v)^{-1}`,
`I₃ = (1/π³)∫∫∫ (3−cos u−cos v−cos w)^{-1}`.
The **factor 3** for sc and for fcc comes from `1/(1/3)`; bcc has **no factor**
because its structure factor already carries coefficient `z^{-1}·8 = 1`. This
asymmetry is exactly where a naive transcription goes wrong.

---

## 1. Simple cubic: `u(3)` and `p(3)` (V11)

### 1.1 The three closed forms **[CL]** + **[NC ~100]**

```
u(3) = √6/(32π³) · Γ(1/24) Γ(5/24) Γ(7/24) Γ(11/24)                      (Glasser–Zucker)
     = (12/π²)(18 + 12√2 − 10√3 − 7√6) · K(k₆)²,
        k₆ = (2−√3)(√3−√2),  K with parameter m = k₆²               (Watson 1939)
     = 3(18 + 12√2 − 10√3 − 7√6) · θ₃(0, e^{−π√6})⁴                 (A273086)
     = 1.516386059151978018156012159681420779955387044452262676566980463658086…
```

`R3-01` §1 compares the three forms and Greubel's equivalent product
`(√3−1)(Γ(1/24)Γ(11/24))²/(32π³)` (OEIS A086231): **all agree to ≥ 100 digits**
(differences `~10^{-101}`). Mathlib's `ellipticF c (π/2)` takes the *parameter*
`c = k²`, so the K-form is `ellipticF (k₆^2) (π/2)` — matching `Polya.lean`.
`mpmath.ellipk` also takes the parameter, and the mismatch convention
(`ellipk(k₆)` instead of `ellipk(k₆²)`) gives `1.5792493…`, a useful trap to note
**[NC 60]**.

### 1.2 The modulus `k₆` **[NC 20]**

`k₆ = (2−√3)(√3−√2) = 0.0851642331747425876487993092982399687122142375235…` and
the quartic `x⁴ + 12x³ + 2x² − 12x + 1` vanishes there (residual `7·10^{-102}`).
The quartic is reciprocal (`x ↦ 1/x`), so it has **two** roots in `(0,1)`:
`k₆ ≈ 0.0851642` and `0.8430390`. The K-form needs the **smaller** root; the
larger does not reproduce `u(3)`. [The plan says merely "a root", which is true
but ambiguous; L8 picks the right one.]

### 1.3 `p(3)` **[NC 60]**

```
p(3) = 1 − 1/u(3) = 0.34053732955099914282627318443290289671060821712430209776…
```

matching OEIS A086230 to 60 digits. **Caution:** the value
`0.340537329550999142835175…` quoted in the superseded draft is wrong from digit 21.

### 1.4 Direct cross-checks

* `u(3) = 3 I₃` with `I₃ = 0.505462019…` **[SY]** (the factor 3 of the table).
* The 2D reduction `u(3) = (3/π²)∫₀^π∫₀^π ((2−cos x−cos y)(4−cos x−cos y))^{-1/2}`
  (after integrating out `z`) matches to **61 digits** (`R3-01` §3). The
  cancellation-free rewriting `2−cos x−cos y = 2sin²(x/2)+2sin²(y/2)` is needed.
* The exact return series `u(3) = Σ_k A002896(k)/36^k` (OEIS A002896 = number of
  `2k`-step returns) **[CL]**: a plain partial sum to `N=100` is still off by
  `0.046`, because the terms decay only like `k^{-3/2}` **[NC 2]**. The series is
  therefore a low-precision sanity check, not a verification route. This corrects
  the superseded draft's "tail `< 10^{-40}`" claim.

---

## 2. bcc: Watson's `I₁` and the return number `u_bcc`

### 2.1 The identities **[CL]** + **[NC 60–90]**

```
I₁ = (1/π³)∫₀^π∫₀^π∫₀^π du dv dw / (1 − cos u cos v cos w)
   = Γ(1/4)⁴/(4π³)
   = (4/π²) K(1/√2)²                      [K with parameter m = 1/2]
   = ₂F₁(1/2, 1/2; 1; 1/2)²
   = ₃F₂(1/2, 1/2, 1/2; 1, 1; 1)
   = 1.393203929685676859184246260325368242657481217515617878974…
```

`R3-02` §A verifies: Γ form vs K form differ by `2.5·10^{-91}`; vs `₂F₁²`
differs by exactly `0` (mpmath); vs the direct 2D reduction
`I₁ = (1/π²)∫₀^π∫₀^π (sin²x + cos²x sin²y)^{-1/2}` by `2.8·10^{-61}`.
The Clausen identity `₃F₂(1/2,1/2,1/2;1,1;1) = ₂F₁(1/2,1/2;1;1/2)²` and
`₂F₁(1/2,1/2;1;1/2) = Γ(1/4)²/(2π^{3/2})` are **[CL]**.

### 2.2 bcc return number **[SY]** + **[CL]**

`u_bcc = I₁` (the table above). OEIS A091670 is this number, and A293238
("escape probability for a random walk on the 3D bcc lattice") is
`1/u_bcc = 4π³/Γ(1/4)⁴ = 0.7177700110461299978211932236657794…`, matching to
60 digits **[NC 60]**. Hence

```
p_bcc = 1 − 1/u_bcc = 0.28222998895387000217880677633422057334287011066001562801…
```

`R3-02` §A also checks the exact closed-walk count `a_n = C(n,n/2)³` (the bcc
structure factor factorizes as `(u+u^{-1})(v+v^{-1})(w+w^{-1})`), so
`u_bcc = Σ_m C(2m,m)³/64^m` **[SY]**; the series itself converges like `m^{-3/2}`
(partial sums are low precision), which is the same slow tail as the sc case.

### 2.3 Plan verdict

The plan's bcc candidate `Γ(1/4)⁴/(4π³)` is **correct** — both as Watson's `I₁`
and as the bcc return number.

---

## 3. fcc: the plan's candidate is `I₂`, not `u_fcc`

### 3.1 Watson's second integral **[CL]** + **[NC ~90]**

```
I₂ = (1/π³)∫₀^π∫₀^π∫₀^π du dv dw / (3 − cos v cos w − cos w cos u − cos u cos v)
   = 3 Γ(1/3)⁶/(2^{14/3} π⁴)             [2^{14/3} = 16·2^{2/3}]
   = √3 K((2−√3)/4)²/π²                   [parameter m = (2−√3)/4 = sin²(π/12)]
   = √3 K(sin(π/12))²/π²
   = 0.448220394388381432116385450017485249569392201708120730491…
```

This is OEIS A091671, "Watson's second triple integral". `R3-02` §B: Γ form vs
K form differ by `1.8·10^{-91}`; vs the direct 2D reduction (MathWorld eq. 46)
`I₂ = (1/π²)∫₀^{π/2}∫₀^{π/2} (cos²θ + ¼ sin²θ sin²ψ)^{-1/2}` by `1.1·10^{-63}`.

### 3.2 The return number is `3 I₂` **[SY]** + **[NC 60]**

Repeating §0's reduction for fcc gives

```
u_fcc = (1/π³)∫_{[0,π]³} du dv dw / (1 − (cos u cos v + cos v cos w + cos w cos u)/3)
      = 3 I₂
      = 9 Γ(1/3)⁶/(2^{14/3} π⁴)
      = 3√3 K((2−√3)/4)²/π²
      = (3/π²) K((2−√3)/4) K((2+√3)/4)
      = 1.34466118316514429634915635005245574870817660512436219147…
```

All four expressions agree to ≥ 60 digits **[NC 60–90]**. Cross-checks:

* the escape probability `1/u_fcc = 2^{14/3}π⁴/(9Γ(1/3)⁶) = 0.74368176349535122890496981936537648050960225090512170566…`
  is **exactly** OEIS A293237 **[NC 60]**;
* `K((2+√3)/4) = √3 K((2−√3)/4)` **[NC 70]** (the two elliptic integrals differ by `0` at 70 dps), which is why the single-`K` and product-`K` forms agree;
* `K(sin(π/12)) = 3^{1/4} Γ(1/3)³/(2^{7/3}π) = 1.59814200211254014446096510539…`
  **[NC 70]**, exactly the `K(k₃)` formula independently verified in `NOTES-hypergeometric-R2`. Squaring it gives `I₂ = √3·3^{1/2}Γ(1/3)⁶/(2^{14/3}π⁴)`, consistent with the Γ form.

So the fcc return probability is

```
p_fcc = 1 − 1/u_fcc = 0.25631823650464877109503018063462351949039774909487829433…  [NC 60]
```

### 3.3 Plan verdict

The plan quotes `3Γ(1/3)⁶/(2^{14/3}π⁴) = 0.448220…` as "the face-centred cubic
Watson integral". That number is Watson's `I₂` **[CL]**, but it is **not** the fcc
return number and `1 − 1/I₂ ≈ −1.23` is not a probability. The correct fcc return
number is `3 I₂ = 9Γ(1/3)⁶/(2^{14/3}π⁴)`. **The plan's fcc formula is wrong by a
factor 3 and the corrected formula is `9Γ(1/3)⁶/(2^{14/3}π⁴)`.**

(Side remark, for orientation: A293237 records that the hcp escape probability
equals the fcc one, and the diamond escape probability is `3/4` of it, so the
diamond return number is `4 I₂ = 12Γ(1/3)⁶/(2^{14/3}π⁴)` **[CL]**.)

---

## 4. The defining Bessel integral and achievable precision

Montroll's formula `u(d) = ∫₀^∞ [I₀(t/d)]^d e^{−t} dt` at `d = 3` reads **[CL]**

```
u(3) = ∫₀^∞ (e^{−t/3} I₀(t/3))³ dt = ∫₀^∞ e^{−t} I₀(t/3)³ dt.
```

`R3-01` §5 evaluates it two ways (`I₀` = modified Bessel, from `mpmath.besseli`):

* **Infinite-range quadrature.** `mpmath.quadts(f, [0, ∞))` gives
  `1.5163860591519780181560121596814207799…`, differing from the closed form by
  `3.5·10^{-53}` — so the integral verifies `u(3)` to **~52 digits**.
* **Tail-limited finite range.** `∫₀^T` plus the asymptotic tail
  `∫_T^∞ c₀ t^{-3/2}(1 + b₁/t + b₂/t² + b₃/t³) dt`, with
  `c₀ = (3/(2π))^{3/2}`, `b₁ = 9/8`, `b₂ = 297/128`, `b₃ = 7587/1024`
  (the cube of `I₀(x) ∼ e^x(2πx)^{-1/2}(1 + 1/(8x) + 9/(128x²) + 225/(3072x³) + …)`),
  gives, with the three tail terms,
  `T = 800`: `4.8·10^{-11}`, `T = 1600`: `9.3·10^{-15}` — i.e. **~14 digits**.
  The tail is `c₀·2/√T` (`0.0165` at `T = 1600` before correction), and the
  asymptotic series is divergent, so a finite `T` caps the precision. Even with
  `T = 1600` the raw `∫₀^T` alone is off by `0.0165` (about 1.8 digits).

**Reported answer to point 4:** the integral equals `u(3)` and, being the actual
definition, was checked to **~52 digits** by infinite-range quadrature; the
**tail-limited finite-range** check is genuinely limited to **~14 digits** at a
practical `T ≈ 1600`, improving only like `T^{-1/2}` (times the optimal truncation
of the tail series).

---

## 5. Formalizability in Lean/Mathlib, and what L8 should state

### 5.1 What is directly `PConstructible`

The closed forms are *statements about `Real.Gamma` and `ellipticF`*, both of which
are already covered by the repo:

* `Γ(1/4)` — denominator-4 family, `Gamma_intCast_div_four_Pconstructible` (`Gamma.lean:1074`);
* `Γ(1/3)` — denominator-3/6 family, `Gamma_intCast_div_three_Pconstructible` (`Gamma.lean:810`); also `Γ(n/24)`, `Gamma_intCast_div_twentyfour_Pconstructible` (`Gamma.lean:1651`);
* `2^{14/3}` — `rpow_Pconstructible {a b} (ha) (hb) (0 < a)` (`Basic.lean:1759`, tagged `@[pconstructible_cond]`); the side goal `0 < 2` is discharged by the tactic's `sideTac` (`Tactic.lean:104–108`, `first | assumption | norm_num | positivity | linarith`);
* `ellipticF c (π/2)` — `ellipticF_pi_div_two_Pconstructible {c} (hcP : PConstructible c) (hc : c < 1)` (`Basic.lean:4090`).

**Tested** (`lean_multi_attempt` inside `Pptc/Hypergeometric/Polya.lean`, warm
environment — each term was added to the context without error):

| expression | `pconstructible` closes it? |
|---|---|
| `Real.Gamma (1/4)^4 / (4 * π^3)` | **yes** |
| `9 * Real.Gamma (1/3)^6 / ((2:ℝ)^(14/3) * π^4)` | **yes** |
| `Real.Gamma (1/3)^6 / ((2:ℝ)^(14/3) * π^4)` | **yes** |
| `9 * Real.Gamma (1/3)^6 / (16 * (2:ℝ)^(2/3) * π^4)` | **yes** |
| `1 - (Real.Gamma (1/3)^6 / (3 * (2:ℝ)^(14/3) * π^4))⁻¹` | **yes** |
| `4/π^2 * (ellipticF (1/2) (π/2))^2` | **yes** |
| `3/π^2 * ellipticF ((2−√3)/4) (π/2) * ellipticF ((2+√3)/4) (π/2)` | **no** |

The bcc K-form closes automatically, because its side goal `1/2 < 1` is
`norm_num`-able. The **fcc** K-forms fail **not** because `ellipticF` is
unreachable but because `sideTac` cannot prove the parameter inequality
`(2−√3)/4 < 1` (`norm_num` does not see through `√3`, and aesop stops at the
subgoal `PConstructible (ellipticF ((2−√3)/4) (π/2))`). They are still
formalizable: a single `have` does it —
`refine ellipticF_pi_div_two_Pconstructible (by pconstructible) ?_` followed by
`nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]`
(both steps tested), exactly the pattern L8 already uses for `k₆`
(`k6_sq_lt_one`).

### 5.2 What is out of scope

The Watson integral *itself*,
`(1/π³)∭_{[0,π]³} dx dy dz/(3 − cos x − cos y − cos z)` (and its bcc/fcc
analogues), is a separate programme. Mathlib has no packaged multidimensional
box-integral constant or Watson integral; a faithful statement needs (i) a triple
Bochner/`boxIntegral`, (ii) the Laplace/geometric-series interchange that produces
Montroll's Bessel form, (iii) the Glasser–Zucker evaluation as `K²`/Γ-products, and
(iv) the `₃F₂`/Clausen reduction. None of that belongs in `Polya.lean`. **[SP]**

### 5.3 Concrete recommendation for L8

Mirror the landed sc pattern: define each closed form, prove `PConstructible`, and
name the classical identity in the docstring **without** asserting it (no new
axiom, exactly as `Polya.lean` already does for `polyaReturn3` vs `polyaReturn3K`).
Use the **Γ forms** — they are test-clean and need no side-condition lemmas:

```lean
-- bcc: u_bcc = Γ(1/4)^4/(4π³)  (Watson I_1; OEIS A091670; escape A293238)
noncomputable def watsonBcc : ℝ := Real.Gamma (1 / 4) ^ 4 / (4 * Real.pi ^ 3)
theorem watsonBcc_Pconstructible : PConstructible watsonBcc
noncomputable def bccReturnProb : ℝ := 1 - (watsonBcc)⁻¹
theorem bccReturnProb_Pconstructible : PConstructible bccReturnProb

-- fcc: u_fcc = 9 Γ(1/3)^6/(2^(14/3) π⁴)  (3 * Watson I_2; OEIS A293237 for the escape)
noncomputable def watsonFcc : ℝ :=
    9 * Real.Gamma (1 / 3) ^ 6 / ((2 : ℝ) ^ ((14 : ℝ) / 3) * Real.pi ^ 4)
theorem watsonFcc_Pconstructible : PConstructible watsonFcc
noncomputable def fccReturnProb : ℝ := 1 - (watsonFcc)⁻¹
theorem fccReturnProb_Pconstructible : PConstructible fccReturnProb
```

Optional K-forms (only if a cross-check against `ellipticF` is wanted; each needs
an explicit parameter-inequality lemma in the style of `k6_sq_lt_one`):

```lean
noncomputable def watsonBccK : ℝ := 4 / Real.pi ^ 2 * (ellipticF (1 / 2) (Real.pi / 2)) ^ 2
noncomputable def watsonFccK : ℝ := 3 / Real.pi ^ 2
    * ellipticF ((2 - Real.sqrt 3) / 4) (Real.pi / 2)
    * ellipticF ((2 + Real.sqrt 3) / 4) (Real.pi / 2)
-- equivalently 3√3/π² * (ellipticF ((2−√3)/4) (π/2))², since K((2+√3)/4) = √3 K((2−√3)/4).
```

**Do not** state `u_fcc = 3Γ(1/3)⁶/(2^{14/3}π⁴)`: that is `I₂`, not the fcc return
number. If the docstring cites "Watson's second triple integral", cite it as the
quantity `u_fcc/3` to avoid propagating the factor-3 error.

Finally, if only one new statement is wanted, prioritise **fcc** (`watsonFcc`),
because it is the one place in B5 where the plan's claimed constant is wrong.

---

## 6. Label ledger

| statement | label |
|---|---|
| `u(3)` Gamma / `K(k₆)` / `θ₃` forms agree (§1.1) | [CL] (Watson; Glasser–Zucker) + [NC ~100] |
| `k₆` is the small root of the quartic; two roots in `(0,1)` (§1.2) | [SY] (root residual) + [NC 20] |
| `p(3)` = A086230 (§1.3) | [CL] (approx.) + [NC 60] |
| `u(3) = 3I₃`; direct 2D integral (§1.4) | [SY] + [NC 61] |
| return series `Σ A002896(k)/36^k` is tail-limited (§1.4) | [SY] + [NC 2] |
| `I₁ = Γ(1/4)⁴/(4π³) = 4K(1/√2)²/π² = ₂F₁(½,½;1;½)²` (§2.1) | [CL] + [NC 60–90] |
| `u_bcc = I₁`, `p_bcc`, escape = A293238 (§2.2) | [SY] + [CL] + [NC 60] |
| `a_n = C(n,n/2)³`, `u_bcc = Σ C(2m,m)³/64^m` (§2.2) | [SY] |
| `I₂ = 3Γ(1/3)⁶/(2^{14/3}π⁴) = √3K(sin π/12)²/π²` (§3.1) | [CL] + [NC ~90] |
| `u_fcc = 3I₂ = 9Γ(1/3)⁶/(2^{14/3}π⁴)`, `p_fcc`, escape = A293237 (§3.2) | [SY] + [CL] + [NC 60–90] |
| `K((2+√3)/4) = √3K((2−√3)/4)`; `K(sin π/12) = 3^{1/4}Γ(1/3)³/(2^{7/3}π)` (§3.2) | [CL] + [NC 70] |
| plan's fcc candidate `3Γ(1/3)⁶/(2^{14/3}π⁴)` is `I₂`, off by factor 3 (§3.3) | [SY] + [NC 60] |
| Bessel integral = `u(3)`; reachable precision (§4) | [CL] (Montroll) + [NC 52 / 14] |
| `PConstructible` of the Γ forms; K-forms need a side lemma (§5.1) | tested (`lean_multi_attempt`) |
| Watson integral itself is out of scope (§5.2) | [SP] |

No `sorry`, no Lean file touched.

Scripts: `archived files/hypergeometric-scripts/R3-01-sc-polya.py`,
`R3-02-bcc-fcc.py`, `R3-03-mods-and-k3.py`
(the superseded draft `R3-watson-checks.py` is left in place but flagged above).
