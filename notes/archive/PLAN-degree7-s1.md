# PLAN: degree 7, exactly one conjugate pair (`s = 1`, issue #6)

Status: **plan, not started in Lean.** The math below is checked numerically (section 5).
It has not been formalised, so treat every identity as something to re-prove, not as settled.

## 0. Target

```lean
-- monic, separable, exactly one conjugate pair {z, conj z}
theorem root_Pconstructible_of_one_conjugate_pair {q : ℝ[X]} (hmon : q.Monic)
    (hnat : q.natDegree = 7) (hsep : q.Separable) (hq : ∀ k, PConstructible (q.coeff k))
    {z : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0) (hzim : z.im ≠ 0)
    (hone : ∀ w : ℂ, (q.map (algebraMap ℝ ℂ)).eval w = 0 → w.im ≠ 0 →
      w = z ∨ w = starRingEnd ℂ z)
    {β : ℝ} (hβ : q.eval β = 0) : PConstructible β
```

Combined with `root_Pconstructible_of_two_conjugate_pairs` (split on whether a second non-real
root exists), `root_Pconstructible_of_nonSeparable` and the monic normalisation now in
`DegreeSeven.lean`, this gives the literal issue statement:

```lean
theorem root_Pconstructible_of_nonreal_root {q : ℝ[X]} (hnat : q.natDegree = 7)
    (hq : ∀ k, PConstructible (q.coeff k)) {z : ℂ}
    (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0) (hzim : z.im ≠ 0)
    {β : ℝ} (hβ : q.eval β = 0) : PConstructible β
```

## 1. Why the blocker in `DegreeSeven.lean` §3 / handoff §3 is not a blocker

The handoff argues that the only known reason `p₃` vanishes on the `(5,1)` light cone is the
conjugation symmetry `σ`, and that constructing `σ` is as hard as the theorem. That is true.
But nothing requires `σ`, or any sign certificate, to be P-constructible.
`PConstructible β` is an existence statement. A proof may use `σ`, continuity and density of
`ℚ` to show that *some rational* input exists, as long as the zero itself comes out of
constructible steps.

So the plan is to:

1. parametrise the light cone rationally, which makes a line in parameter space a degree-6
   curve;
2. use `σ` only in the proof, to show the cubic takes both signs;
3. perturb the two witnesses to rational points;
4. take a real root of the resulting sextic, which the sextic engine makes P-constructible.

## 2. Notation (all already in `ScratchS`)

* `x : Fin 6 → ℝ` are coordinates on `{p₁ = 0}` via `Lcomb q x`.
* `Q x := qform (Gram q) x` and `B x y := bilin (Gram q) x y`; `Gram` entries are
  P-constructible.
* `Cf x := p3vec q (Lcomb q x)`, the cubic `p₃`.
* For a polynomial `F`, `F(r)` means `(F.map (algebraMap ℝ ℂ)).eval r`. The spectral identity
  `companion7_trace_pow_aeval` gives `trace (N_F ^ k) = ∑_{r ∈ roots} F(r)^k`.

## 3. The construction

### Step 1: a P-constructible cone point `P₀`
Take rational `e` with `Q e < 0` and rational `f` with `Q f > 0`. They exist by density: the
witnesses from `exists_neg_trace` / `exists_pos_trace`, shifted into `{p₁ = 0}`, have strict
signs. `exists_pos_quadratic_root` (in `DegreeSeven.lean`) with `a = Q f`, `b = B e f`,
`c = Q e` gives P-constructible `t > 0`. Set `P₀ := e + t • f`. Then `Q P₀ = 0`, and `P₀ ≠ 0`
because `Q e < 0`.

### Step 2: rational parametrisation of the cone (stereographic projection from `P₀`)
```
v x := Q x • P₀ - (2 * B P₀ x) • x
```
This is the second intersection of the line `P₀ + t x` with `{Q = 0}`, scaled by `Q x`. No
square root is needed. Pure bilinear algebra (needs `Gram_symm` and `Q P₀ = 0`) gives:

* (S1) `Q (v x) = 0` for every `x`.
* (S2) `v (c • P₀ + ε • δ) = ε ^ 2 • v δ`, so `v` vanishes to order 2 along the ray of `P₀`.
* (S3) if `Q x = 0` then `v x = (-2 * B P₀ x) • x`, hence `Cf (v x) = -8 (B P₀ x)^3 Cf x`.

Define `Φ x := Cf (v x)`, a homogeneous form of degree 6 on `ℝ⁶`.

### Step 3: the sign certificate (uses `σ`, is not constructible, and doesn't need to be)
Let `x₁ ≠ x₂` be two real roots of `q`. With one pair there are five real roots. Put
`ω := -1/2 + (√3/2) i` and let `j ∈ {1, 2}`.

* Build `X_j` with `deg ≤ 6`, value `1` at `x_j`, `0` at the other real roots, `ω` at `z` and
  `ω̄` at `z̄`. It is the Lagrange polynomial `q /ₘ (X - C x_j)` scaled by `1/q'(x_j)`, plus
  `exists_poly_value_at_root … ω`.
* Build `X̄_j` the same way with `ω̄` at `z`. This is `σ X_j`.

Then `p₁ = 1 + 2 Re ω = 0`, `p₂ = 1 + 2 Re ω² = 0` and `p₃ = 1 + 2 Re ω³ = 3` for both. That
is `septicOnePairCubic` at `u = e_j`, which equals `3`.

Write `P₀`'s values as `y_r` at the real roots and `α + iγ` at `z`, and let `R := ∑_real y_r²`.
With `b₁ := B P₀ X_j` and `b₂ := B P₀ X̄_j`:
```
b₁ = y_j - α - √3 γ,   b₂ = y_j - α + √3 γ,   b₁ b₂ = (y_j - α)² - 3γ².
Q P₀ = 0  gives  γ² = α² + R/2,   and  R ≥ y₁² + y₂²,  so
b₁ b₂ ≤ -½ (y_j + 2α)² - (3/2) y_{3-j}².
```
If both `j = 1` and `j = 2` gave `b₁ b₂ = 0`, then `y₁ = y₂ = α = 0` and `γ = 0`, so `R = 0`.
Then `P₀` vanishes at all 7 roots, hence `P₀ = 0`, a contradiction. So for some `j`,
`b₁ b₂ < 0`, and by (S3)
```
Φ X_j = -24 b₁³   and   Φ X̄_j = -24 b₂³   have strictly opposite signs.
```

### Step 4: rational witnesses
`Φ` is a polynomial function on `ℝ⁶`, hence continuous. By density of rational vectors
(`Rat.denseRange_cast`, `DenseRange.piMap`, `Dense.exists_mem_open`) there are rational
`d⁺, d⁻ : Fin 6 → ℚ` with `Φ d⁺ > 0 > Φ d⁻`.

### Step 5: the sextic and its root
Let `δ := d⁻ - d⁺` and `x(m) := d⁺ + m • δ`. Then `m ↦ Φ (x m)` is a polynomial `Ψ` of
`natDegree ≤ 6`: `v(x m)` has entries of degree `≤ 2` in `m`, and `Cf` is cubic. Its
coefficients are P-constructible. The key formula is
```
p3vec q w = ∑ i j k, w i * w j * w k * trace (M ^ (i + j + k))
```
(`trace_pow_Pconstructible` exists in `ScratchS`). `Ψ.eval 0 > 0 > Ψ.eval 1`, so
`intermediate_value_Icc'` gives `m* ∈ (0,1)` with `Ψ.eval m* = 0`. `Ψ ≠ 0`, so
`root_Pconstructible_le_six_coeffs` makes `m*` P-constructible, and with it every entry of
`x* := x m*` and of `v x*`.

### Step 6: non-degeneracy, `v x* ≠ 0`
* **`x*` is not parallel to `P₀`.** If `x m₀ = c • P₀`, then `x m = c • P₀ + (m - m₀) • δ`, and
  (S2) gives `Ψ.eval m = (m - m₀)^6 · Φ δ` for all `m`. Then `Ψ.eval 0` and `Ψ.eval 1` have the
  same weak sign, a contradiction.
* **No totally isotropic plane when `s = 1`.** If `Q x = Q y = B x y = 0` with `y ≠ 0`, then
  `x = c • y`. Proof with `F, G` the polynomials of `x, y`: every `h = aF + bG` has
  `∑_real h(r)² + 2 Re (h(z)²) = 0`.
  - If `F(z), G(z)` are ℝ-dependent, some nonzero `h` has `h(z) = 0`, hence vanishes at all 7
    roots, hence `h = 0`.
  - Otherwise some `h` has `h(z) = 1`, which makes the sum `≥ 2`.
* **`v x* ≠ 0`.** If `v x* = 0` and `x*` is not parallel to `P₀`, then `B P₀ x* = 0` (otherwise
  `x*` would be parallel to `P₀`), so `Q x* = 0`. Now `span {P₀, x*}` is totally isotropic,
  and the previous bullet gives a contradiction.

### Step 7: finish
`φ := polyOfVec (Lcomb q (v x*))` has P-constructible coefficients and `natDegree ≤ 6`, with
`φ ≠ 0` (`Lcomb_injective`, `polyOfVec_ne_zero`). Its power sums are `p₁ = 0`
(`p1vec_Lcomb`), `p₂ = Q (v x*) = 0` (S1) and `p₃ = Ψ.eval m* = 0`. The tail of the `s ≥ 2`
proof then applies unchanged: `charpoly_aeval_coeff_6_5_4_eq_zero`, then `resolvent_powerLaw`,
then `root_Pconstructible_of_powerLaw`.

## 4. Lean work breakdown

Put it in a new file `Pptc/DegreeSevenOnePair.lean` importing `Pptc.DegreeSeven`. That avoids
an import cycle, since the tail lives in `DegreeSeven`. Items A–E are pure algebra or analysis
and independent of each other and of F. **F is the fiddly part.**

| # | Deliverable | Reuses | Difficulty |
|---|---|---|---|
| A | `root_Pconstructible_of_tschirnhaus`: factor the tail out of `root_Pconstructible_of_two_conjugate_pairs_monic` (inputs: monic separable septic, `φ ≠ 0`, `deg ≤ 6`, P-constructible coefficients, three traces zero). | existing proof | easy |
| B | `p3vec_eq_sum` (the triple-sum formula) and `p3vec` continuity in `w`. | `polyOfVec`, `aeval` linearity | medium |
| C | `stereo` definition plus (S1), (S2), (S3). | `bilin_*`/`qform_*` calculus, `Gram_symm` | easy |
| D | `exists_isotropic_Pconstructible` (Step 1), taking rational `e`, `f` with strict signs as input. | `exists_pos_quadratic_root` | easy |
| E1 | `exists_rat_vec_pos`: `Continuous g`, `g x > 0` gives `∃ r : Fin n → ℚ, g (↑r) > 0`. | Mathlib density lemmas above | easy |
| E2 | `exists_sextic_along_line`: `∃ Ψ : ℝ[X]`, P-constructible coefficients, `natDegree ≤ 6`, `∀ m, Ψ.eval m = Φ (d + m • δ)`. Build `Ψ` as a `Finset` sum of products of degree-`≤2` polynomials. | B, `coeff_mul_Pconstructible` (`ScratchSep`) | medium |
| F1 | `roots_eq_pair_add_real`: under `hsep`, `hone`, `qC.roots = z ::ₘ conj z ::ₘ (R.map ofReal)` with `R : Multiset ℝ`, `R.Nodup`, `card R = 5`. | `companionVecC`-style root facts, `Multiset.erase` | medium–hard |
| F2 | Trace split: `trace (N_F ^ k) = ∑_{r ∈ R} F(r)^k + 2 Re (F(z)^k)`; bilinear version via `aeval` of `F * G`. | F1, `companion7_trace_pow_aeval` | medium |
| F3 | Real-root Lagrange polynomial, then `X_j` and `X̄_j`, and their `p₁, p₂, p₃`. | `exists_poly_value_at_root`, `Separable` derivative at root | medium |
| F4 | Sign certificate: `P₀ ≠ 0`, `Q P₀ = 0` imply `∃ j, B P₀ X_j * B P₀ X̄_j < 0`. The inequality itself is `nlinarith`. | F2, F3 | medium |
| F5 | No totally isotropic plane when `s = 1`. | F2, "deg ≤ 6 vanishing at 7 roots is 0" (as in `StopTotallyReal`) | medium |
| G | Assembly of Steps 4–7, then `root_Pconstructible_of_one_conjugate_pair`, then `root_Pconstructible_of_nonreal_root`. | all | medium |

Suggested order: **A, C, D, E1** first (a short session), then **B, E2**, then **F1 → F2 →
(F3, F5) → F4**, then **G**. Write each as its own `theorem` with the `-- Theorem:` line,
checked by `lake env lean` before moving on.

Traps to expect:
* In F3 and F4, keep the complex values as `ℂ` and push to `Re`/`Im` only at the end. The
  `StopTotallyReal` note about `((φ.eval r : ℝ) : ℂ)` mis-elaborating applies here too.
* `svec q : Fin 7 → ℝ` only reaches `M^6`, but B needs `trace (M ^ n)` for `n ≤ 18`. Use
  `Matrix.trace (companion7 q ^ n)` directly.
* In Step 3, `ω` involves `√3`, but only `ω`'s *existence* is used. It never enters a
  constructibility claim, so no P-constructibility obligation arises.
* The simpler certificate `u = (1,1,1,1,1)` (value `1` at every real root) avoids the Lagrange
  polynomial but **fails** when `P₀ ∥ X`: the Cauchy–Schwarz equality case. That is why the
  plan uses two single real roots and picks `j`.

## 5. Numerical check (Python, double precision)

Script: `PLAN-degree7-s1-check.py` (run with `py -3`). Three cases:
`(x-1)(x-2)(x-3)(x+1)(x+2)(x²+1) + 1/3` with `j = 1`, and
`(x+3)(x-½)(x-2)(x+1)(x-4)(x²-x+3) + 2/7` with `j = 2` and `j = 4`. Each has 5 real roots
and one pair.

| check | case 1 | case 2 | case 3 |
|---|---|---|---|
| `Q P₀` | −2e−15 | −5e−15 | −5e−15 |
| `p₁,p₂,p₃` of `X_j` | 0, 0, 3 | 0, 0, 3 | 0, 0, 3 |
| `b₁ b₂` | −0.665 | −3.000 | −3.001 |
| `Φ X_j`, `Φ X̄_j` | +0.204, −831 | +116, −134 | +125, −125 |
| after rounding to 4 decimals | +0.199, −873 | +116, −148 | +103, −164 |
| degree-7 coefficient of `Ψ` (relative) | 3e−12 | 7e−13 | 5e−13 |
| root `m*` in (0,1) | 0.1153 | 0.6353 | 0.6075 |
| `‖v x*‖` | 0.263 | 0.425 | 0.728 |
| `p₁,p₂,p₃` of `φ` (relative) | ≤ 2e−13 | ≤ 8e−15 | ≤ 6e−15 |
| resolvent `y⁶,y⁵,y⁴` (relative) | ≤ 6e−14 | ≤ 3e−15 | ≤ 2e−15 |
| resolvent `y³..y⁰` | nonzero | nonzero | nonzero |

In every case the rounded rational witnesses keep the sign change, `Ψ` has degree `≤ 6`, the
sign-change root gives `v x* ≠ 0`, and the resolvent is `y⁷ + (cubic)`, which is what
`powerLaw_cubic_root_Pconstructible` consumes.
