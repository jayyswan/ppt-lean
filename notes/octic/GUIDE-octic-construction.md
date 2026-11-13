# Constructing a real root of an octic: a step-by-step guide

This is the recipe behind `root_Pconstructible_deg8_coeffs` (`Pptc/Octic/Main.lean`): given

    q(X) = a₈X⁸ + … + a₁X + a₀,   aᵢ P-constructible,   and a real root β of q,

it says which numbers to compute and which curves to cross, in order, to reach β.
`octic_construct.py` in this folder runs the whole recipe on seven sample octics and checks
every identity quoted below (`python3 octic_construct.py`, needs `mpmath`).

## 0. Read this first: what is and is not effective in the Lean proof

The Lean theorem is an existence statement proved classically. Three kinds of step in it do
not, as written, tell you what to do:

| In the proof | What it hides | What you do instead |
|---|---|---|
| case split on separable / splits / number of conjugate pairs | which branch you are in | compute `gcd(q, q′)` and count real roots (Sturm sequence, or numerically) |
| `exists_rat_vec_pos`, `exists_PC_inputs_s1` (density of ℚⁿ) | a rational vector with a strict sign, or inside an open set | take the explicit real witness the proof builds from the roots, **round it**, and check the strict inequality |
| IVT / `exists_rat_isolating` | which root of an auxiliary equation, and a window isolating it | locate the root numerically and pick rational window endpoints |

So approximate roots of q are used as **scaffolding**: to choose a branch, to find rational
seeds, and to know which crossing to read. Nothing approximate enters the construction itself.
Once the seeds are fixed, every number is obtained from the aᵢ by `+ − × ÷` and by reading a
crossing of two drawable curves, and every check is a strict inequality or a `≠`, so it
survives small errors in the scaffolding.

Notation: polynomials of degree ≤ 7 are identified with their coefficient vectors
`v = (v₀,…,v₇)`, `φ = Σ vᵢXⁱ`. `C` is the companion matrix of q, and `Tr φᵏ` means
`Tr(φ(C)ᵏ) = Σ_{roots r of q} φ(r)ᵏ`.

## 1. Triage

1. **Normalise.** Divide by `a₈`. If `a₈ = 0` the degree is ≤ 7: go to §8.
2. **Repeated roots.** Compute `d = gcd(q, q′)` (Euclid, field operations only). If `d ≠ 1`,
   β is a root of `d` or of `q/d`, both of degree ≤ 7: go to §8.
   (`root_Pconstructible_of_nonSeparable_eight`)
3. **Count real roots.** With `s` = number of conjugate pairs of nonreal roots:

   | real roots | s | branch | section |
   |---|---|---|---|
   | 8 | 0 | **R** (totally real) | §6 |
   | 6 | 1 | **N1** | §2, §3, §5 |
   | 4, 2 | 2, 3 | **N2** | §2, §3, §4 |
   | 0 | 4 | nothing to construct | |

All three branches have the same shape:

    find φ of degree ≤ 7  →  y = φ(β) is a root of a resolvent of special shape
                          →  read y off one crossing  →  recover β from φ(X) = y.

They differ only in how φ is found and in the shape of the resolvent.

## 2. Shared data for the nonreal branches (N1, N2)

Everything here is field arithmetic on the coefficients of q (`Pptc/Octic/TraceForm.lean`).

- **Power sums.** `s_k = Tr Cᵏ` for `k = 0..21`, by Newton's identities (`s₀ = 8`).
- **Trace forms on coefficient vectors.**

      Tr φ   = Σᵢ vᵢ sᵢ                      (p1vec8)
      Tr φ²  = Σᵢⱼ vᵢ vⱼ s_{i+j}             (Hmat8; write H(u,v) for the bilinear form)
      Tr φ³  = Σᵢⱼₖ vᵢ vⱼ vₖ s_{i+j+k}       (p3vec8; write T(u,v,w) for the trilinear form)

- **The trace-zero hyperplane.** A vector `x = (x₀,…,x₆) ∈ ℝ⁷` stands for

      L(x) = x₀X + x₁X² + … + x₆X⁷ − (1/8)·Σⱼ xⱼ s_{j+1}        (Lcomb8)

  which has `Tr = 0`. Conversely, a polynomial with trace 0 is `L` of its coefficients of
  `X¹..X⁷` (`coeff7`), so to move a polynomial into the hyperplane, just drop its constant term.
- **The form on ℝ⁷.** `B(x,y) = H(L x, L y)`, `Q(x) = B(x,x)` (`Gram8`). It has signature
  `(7 − s, s)`.
- **Goal.** A nonzero `v ∈ ℝ⁷` with `Q(v) = 0` and `Tr L(v)³ = 0`. Then `φ = L(v)` has
  `Tr φ = Tr φ² = Tr φ³ = 0`.

Two interpolation recipes produce the real witnesses that get rounded (`Pptc/Octic/Roots.lean`).
For a nonreal root z and a complex number c:

    I(z, c) = G·h,   G = q / ((X − z)(X − z̄)),   h = h₀ + h₁X real with h(z) = c / G(z)
              i.e.  h₁ = Im(c/G(z)) / Im z,   h₀ = Re(c/G(z)) − h₁·Re z.

It takes the value c at z, c̄ at z̄ and 0 at the other six roots, so `Tr I = 2 Re c` and
`Tr I² = 2 Re c²`. In particular `Q(coeff7 I(z, i)) = −2` and `Q(coeff7 I(z, 1)) = 3/2`.

## 3. A cone point P₀ (N1 and N2) — one square root

`exists_cone_point8`, `Pptc/Octic/Cone.lean`.

- **C1.** `e` := a rational rounding of `coeff7 I(z, i)`. Check `Q(e) < 0`.
- **C2.** `f` := a rational rounding of `coeff7 I(z, 1)`. Check `Q(f) > 0`.
  (Any rational `e`, `f` with these two signs will do; the interpolants are only a guaranteed
  place to look.)
- **C3.** With `a = Q(f)`, `b = B(e,f)`, `c = Q(e)`:

      t = (−b + √(b² − ac)) / a  > 0,        P₀ = e + t·f.

  Then `Q(P₀) = 0` and `P₀ ≠ 0`. The only non-rational operation is one `√`
  (`sqrt_Pconstructible`).

## 4. Branch N2 (two or more conjugate pairs) — one more square root, one cubic

`exists_tschirnhaus_traces_two_pairs8`, `Pptc/Octic/TwoPairs.lean`. Let z, w be nonreal roots
from two different pairs.

- **N2.1 Definite planes.** `v₁ = coeff7 I(z,i)`, `v₂ = coeff7 I(w,i)` span a plane on which
  Q is negative definite; `w₁ = coeff7 I(z,1)`, `w₂ = coeff7 I(w,1)` span one on which it is
  positive definite.
- **N2.2 Make them orthogonal to P₀.**

      e⁰ = B(P₀,v₂)·v₁ − B(P₀,v₁)·v₂          (Q(e⁰) < 0,  B(P₀,e⁰) = 0)
      f⁰ = B(P₀,w₂)·w₁ − B(P₀,w₁)·w₂          (Q(f⁰) > 0,  B(P₀,f⁰) = 0)

- **N2.3 Rationalise without losing orthogonality.** Pick a coordinate vector `u` with
  `c = B(P₀,u) ≠ 0` and let `π(y) = c·y − B(P₀,y)·u`; `π` maps everything into `P₀⊥` and
  fixes `P₀⊥` up to the factor c. Set

      e = π(rounding of e⁰),   f = π(rounding of f⁰),   check Q(e) < 0 < Q(f).

  (`exists_orth_projectionN`, `exists_orth_neg_PconstructibleN`.)
- **N2.4 A second isotropic vector.** As in C3: `t′` = the positive root of
  `Q(f)t² + 2B(e,f)t + Q(e)`, and `x = e + t′·f`. Now `Q(x) = 0`, `B(P₀,x) = 0`, and x is
  not parallel to P₀, so Q vanishes identically on `span(P₀, x)`.
- **N2.5 The binary cubic.** With `cv = L(P₀)`, `cw = L(x)`:

      a = T(cv,cv,cv),  b = 3T(cv,cv,cw),  c = 3T(cv,cw,cw),  d = T(cw,cw,cw).

  If `d = 0` take `(σ,τ) = (0,1)`; otherwise take `σ = 1` and τ a real root of
  `a + bτ + cτ² + dτ³` (a cubic always has one; `binary_cubic_zero`).
- **N2.6** `φ = σ·cv + τ·cw`. Go to §7.

## 5. Branch N1 (exactly one conjugate pair) — one sextic

`root_Pconstructible_of_one_conjugate_pair8`, `Pptc/Octic/OnePair.lean`. Here Q has signature
`(6,1)`, there is no isotropic plane, and the second cone point is found by stereographic
projection from P₀:

    σ(x) = Q(x)·P₀ − 2B(P₀,x)·x        (always Q(σ(x)) = 0;  stereoN)
    Φ(x) = Tr L(σ(x))³.

- **N1.1 Two directions with opposite signs of Φ.** Let `ω = −1/2 + (√3/2)i`. For a real root
  `x_j` and `c ∈ {ω, ω̄}` let `X_{j,c}` be the degree-≤7 polynomial that is 1 at `x_j`, 0 at
  the other five real roots, and c at z:

      X_{j,c} = q/((X − x_j)·q′(x_j)) + I(z, c),      d_{j,c} = coeff7 X_{j,c}.

  Each has `Q(d) = 0`, `Tr L(d)³ = 3`, and `Φ(d) = −24·B(P₀,d)³`. Compute the four values for
  two real roots `x₁, x₂`: for at least one j, `Φ(d_{j,ω})` and `Φ(d_{j,ω̄})` have opposite
  signs (`exists_sign_change8`). Call a positive one `d⁺` and a negative one `d⁻`.
- **N1.2 Rationalise.** `dp`, `dm` := rational roundings of `d⁺`, `d⁻`; check
  `Φ(dp) > 0 > Φ(dm)`. (Any rational pair with these signs will do.)
- **N1.3 The sextic along the line.** With `δ = dm − dp`,

      Ψ(m) = Φ(dp + m·δ)

  is a polynomial of degree ≤ 6 in m (σ is quadratic, `Tr ·³` is cubic) with P-constructible
  coefficients. Get the coefficients by expanding

      σ(dp + mδ) = (Q(dp) + 2B(dp,δ)m + Q(δ)m²)·P₀ − 2(B(P₀,dp) + B(P₀,δ)m)·(dp + mδ),

  or by evaluating Ψ at seven rational m and interpolating (`exists_sextic_along_line8`).
- **N1.4 Solve it.** `Ψ(0) > 0 > Ψ(1)`, so Ψ has a root `m* ∈ (0,1)`; construct it with the
  degree-≤6 engine (§9).
- **N1.5** `v* = σ(dp + m*·δ)`, `φ = L(v*)`. It is automatic that `v* ≠ 0`
  (`isotropic_plane_trivial8`). Go to §7.

## 6. Branch R (all eight roots real) — a cubic, a square root, a sextic, a quintic

`exists_oddTschirnhaus` (`Pptc/TotallyReal/Certificate.lean`) and
`root_Pconstructible_totallyReal_eight` (`Pptc/TotallyReal/Main.lean`). Here Q is positive
definite, so there is no cone. Instead the target is a φ with `Tr φ = Tr φ³ = Tr φ⁵ = 0`,
which kills all odd elementary symmetric functions but the last.

Label the roots `α₁,…,α₈` in any order. A polynomial `b` (coefficient vector) has the
**y-vector** `Y(b) = (b(α₁),…,b(α₈))`. All pairings below are symmetric in the roots, hence
computable from the `s_k`:

    S_k(u)     = Σᵢ Y(u)ᵢᵏ             = Tr uᵏ
    N_P(w)     = Σᵢ Y(P)ᵢ² Y(w)ᵢ       = T(P,P,w)
    Q_P(u)     = Σᵢ Y(P)ᵢ Y(u)ᵢ²       = T(P,u,u)
    ⟨P;u,v⟩    = Σᵢ Y(P)ᵢ Y(u)ᵢ Y(v)ᵢ  = T(P,u,v)

- **R.0 Six rational inputs near the certified centre.** The proof fixes six rational
  y-vectors (`centre8a, b, g, w1, w2, w3`; copied into `CENTRE8` in the script). For each,
  solve the Vandermonde system `Y(b) = centre` numerically, round the solution to a rational
  vector, then subtract `S₁/8` from its constant term so that `Tr = 0` exactly (`correctSlot`).
  Call the results `a, b, g, w₁, w₂, w₃`.
- **R.1 (cubic).** λ := the root of `S₃(a + λb) = 0` near 0. `P = a + λb`.
- **Projection.** Check `N_P(g) ≠ 0`, and put `w̃ⱼ = wⱼ − (N_P(wⱼ)/N_P(g))·g`, so
  `N_P(w̃ⱼ) = 0`.
- **R.2 (quadratic).** x := the root of `Q_P(w̃₁ + x·w̃₂) = 0` near 5/3. `q₀ = w̃₁ + x·w̃₂`.
- **R.3 (sextic).** With `d(μ) = μ·w̃₁ + w̃₃`, μ := the root near −5322/2915 of

      S₃( ⟨P;d,d⟩·q₀ − 2⟨P;q₀,d⟩·d ) = 0          (degree ≤ 6 in μ; chainStep3Cleared)

  Check `⟨P;d,d⟩ ≠ 0` and set `v = q₀ − (2⟨P;q₀,d⟩/⟨P;d,d⟩)·d`.
- **R.4 (quintic).** κ := the root of `S₅(P + κv) = 0` near −1.
- **R.5** `φ = P + κv`. Check that the eight values `φ(αᵢ)` are distinct.

Why it works: steps R.1–R.3 give `S₃(P) = N_P(v) = Q_P(v) = S₃(v) = 0`, and
`S₃(P + κv) = S₃(P) + 3κN_P(v) + 3κ²Q_P(v) + κ³S₃(v)`, so the whole line lies in
`{S₁ = S₃ = 0}`; R.4 cuts it with `S₅ = 0`.

What to expect: with exact (unrounded) inputs the roots are exactly `(0, 5/3, −5322/2915, −1)`
and `Y(φ) = (1, 2, 3, 4, −1, −2, −3, −4)`. So φ is a small perturbation of the Lagrange
polynomial sending the roots to ±1,…,±4, and the chain is the device that repairs the rounding
so that the odd power sums vanish exactly. The roots named "near …" are the ones the
certificate guarantees; any real roots for which the three `≠` checks pass are just as good.

- **R.6 Resolvent.** `χ` = characteristic polynomial of `φ(C)`. Its `t⁷, t⁵, t³` coefficients
  vanish, so

      χ(t) = Q₄(t²) − c·t,     Q₄(x) = x⁴ + χ₆x³ + χ₄x² + χ₂x + χ₀,     c = −χ₁.

- **R.7 Engine E8** (`half_quartic_root_Pconstructible`). The target value is `y = φ(β)`.
  - `y = 0`: nothing to do.
  - `c = 0`: `y²` is a root of the quartic `Q₄` (§9), and `y = ±√(y²)`.
  - otherwise: `x = y²` is the abscissa of a crossing of the quartic graph `Y = Q₄(X)` (§9)
    with the half-power curve `Y = sgn(y)·c·X^{1/2}` (`power_law 1 (1/2)` scaled in Y). Crop
    to a rational window that isolates x among the roots of `Q₄(X)² − c²X`, read x, and set
    `y = sgn(y)·√x`.
- **R.8 Recover β.** §8, applied to `φ(X) − y`.

## 7. The tail for N1 and N2: resolvent, power-law crossing

`root_Pconstructible_of_tschirnhaus8`, `Pptc/Octic/Resolvent.lean`, `Pptc/Octic/Engine.lean`.

- **T1 Resolvent.** `R` = characteristic polynomial of `φ(C)` (field operations). Because
  `Tr φ = Tr φ² = Tr φ³ = 0`, its `t⁷, t⁶, t⁵` coefficients vanish. With `c_k = −R_k`:

      y⁸ = c₄y⁴ + c₃y³ + c₂y² + c₁y + c₀        at y = φ(β).

- **T2 Read y off a crossing** (`powerLaw_quartic_root_PConstructible`).
  - `y = 0`: nothing to do.
  - `c₄ = 0`: cross `Y = X⁸` with the cubic graph `Y = c₃X³ + … + c₀`
    (`powerLaw_cubic_root_Pconstructible`).
  - `y > 0`: cross `Y = X⁸` (`power_law 1 8`) with the quartic graph
    `Y = c₄X⁴ + … + c₀` (§9). Crop the power curve to `[q₁, q₂] × [0, q₂⁸ + 1]` with rationals
    `q₁ < y < q₂` containing no other root of `X⁸ − (c₄X⁴ + … + c₀)`. The crossing is then the
    single point `(y, y⁸)`; read its abscissa.
  - `y < 0`: the power curve is only drawn for `X > 0`, so do the previous case for `−y`,
    with `(c₁, c₃)` replaced by `(−c₁, −c₃)`.

  To know which crossing is yours, evaluate `φ` at your approximation of β.
- **T3 Recover β.** §8, applied to `φ(X) − y`. This polynomial is not constant, because a
  nonzero constant has trace `8c ≠ 0`.

## 8. Recovering β from φ(β) = y, and the descent to degree ≤ 7

`ψ = φ − y` is nonzero, has degree between 1 and 7, P-constructible coefficients, and
`ψ(β) = 0`. The Lean proof now calls `root_Pconstructible_deg7_coeffs`
(`Pptc/TotallyReal/Main.lean`), which is this guide again one degree down:

| ψ | route | resolvent shape | crossing |
|---|---|---|---|
| degree ≤ 6 | §9 directly | | |
| degree 7, repeated root | `gcd(ψ, ψ′)`, both factors of degree ≤ 6 | | |
| degree 7, 7 real roots | chain R.0–R.5 at `centre7`, roots near `(0, 1/2, 8064/617, −1)` | `t·R₃(t²) = c` | cubic graph × `Y = sgn·c·X^{−1/2}` |
| degree 7, a nonreal root | cone point, then two-pairs / one-pair with ℝ⁶ in place of ℝ⁷ | `y⁷ = cubic(y)` | `Y = X⁷` × cubic graph |

and then recovers the root from a polynomial of degree ≤ 6 (§9).

**A shortcut that is not in the Lean proof.** β is a common root of q and ψ. If
`φ(β) ≠ φ(r)` for every other root r of q, then `gcd(q, φ − y) = X − β`, so Euclid's algorithm
on q and `φ − y` (field operations in y and the aᵢ) ends in a linear remainder
`r₁X + r₀` and `β = −r₀/r₁`. No further crossing is needed. In branch R the values `φ(αᵢ)`
are distinct by construction (R.5), so this always applies; in N1 and N2 it applies whenever
the values happen to be distinct, which they were at every real root of every sample in the
script. When it fails, fall back on the table above.

## 9. What is actually drawn: the engines

| To get | Draw and cross | Lean |
|---|---|---|
| `√x`, `x > 0` | — | `sqrt_Pconstructible` (`Basic.lean`) |
| a root of a polynomial of degree ≤ 3 | cubic graph (a cubic Bézier: endpoints plus handles at a third of the tangent) × the x-axis | `cubicVal_root_Pconstructible` |
| degree 4 | divide by the leading coefficient; `Y = X⁴` × cubic graph | `root_Pconstructible_le_six_coeffs` |
| degree 5 | shift to remove `X⁴`; `Y = X⁵` × cubic graph | same |
| degree 6 | shift by `p₅/(6p₆)` to remove `X⁵`, divide by `p₆`; then the Bézier `t ↦ (x(t), y(t))`, `y = t³ + a₄t/2`, × the sideways parabola `x = −y² − a₃y`; read `y`, then solve the cubic `t³ + a₄t/2 = y` | `sextic_root_Pconstructible` |
| monic quartic graph `Y = X⁴ + c₃X³ + c₂X² + c₁X + c₀` | depress with `z = X + c₃/4` to `z⁴ + az² + bz + c`; take `poly_graph` of `X⁴ + X²`, `X⁴ − X²` or `X⁴` (sign of a), scale x by `λ = √|a|` and y by `λ⁴`, shear by `bz`, translate | `quarticGraph_PConstructibleCurve` (`TotallyReal/Engines.lean`) |
| quartic graph with leading coefficient `c₄ ≠ 0` | the monic graph of `cᵢ/c₄`, scaled in y by `c₄` | `quarticGraph_general_PConstructibleCurve` |
| isolate one crossing | crop (`restrict`) to a rational window containing no other root of the difference polynomial | `exists_rat_isolating` |

## 10. Cost summary

| Branch | Auxiliary equations before the resolvent | Resolvent crossing | Then |
|---|---|---|---|
| N2 | √ (C3), √ (N2.4), cubic (N2.5) | `X⁸` × quartic graph | §8 |
| N1 | √ (C3), sextic (N1.4) | `X⁸` × quartic graph | §8 |
| R | cubic, √, sextic, quintic (R.1–R.4) | quartic graph × `X^{1/2}`, then √ | §8 |

## 11. Worked example: q = X⁸ − X − 1 (branch N2)

Two real roots (β ≈ 1.0970 and β ≈ −0.8117) and three conjugate pairs. With seeds rounded
to six decimals the script produces

    φ ≈ 0.53801 + 0.03527X − 0.01916X² + 0.71368X³ − 0.15423X⁴ + 0.12428X⁵ − 0.10115X⁶ − 0.61487X⁷

    y⁸ = −3.858256y⁴ + 1.825473y³ − 0.323808y² + 0.025525y − 0.000754      at y = φ(β),

and for both real roots `gcd(q, φ − y)` is linear, so β is a rational function of y and the
construction is: two square roots, one cubic, one crossing of `Y = X⁸` with a quartic graph,
then field operations. The numbers depend on the rounding of the seeds; the shape does not.

## 12. Where each step lives

| Guide | Lean |
|---|---|
| §1 | `root_Pconstructible_deg8_coeffs`, `root_Pconstructible_of_nonreal_root8` (`Octic/Main`) |
| §2 | `Octic/TraceForm`, `Octic/Roots` (`exists_poly_value_at_root8`) |
| §3 | `exists_cone_point8`, `exists_pos_isotropic_param8` (`Octic/Cone`) |
| §4 | `Octic/TwoPairs`; `neg_dir_of_pair8`, `pos_dir_of_pair8`, `exists_isotropic_orth_Pconstructible8` (`Octic/Cone`) |
| §5 | `Octic/OnePair` (`exists_lagrange_value8`, `exists_sign_change8`), `Octic/Sextic` |
| §6 | `TotallyReal/Certificate` (chain, `centre8`), `TotallyReal/Newton`, `TotallyReal/Engines` (E8), `TotallyReal/Main` |
| §7 | `Octic/Resolvent`, `Octic/Engine` |
| §8 | `root_Pconstructible_deg7_coeffs` (`TotallyReal/Main`), `DegreeSeven` |
| §9 | `Basic`, `TotallyReal/Engines` |
