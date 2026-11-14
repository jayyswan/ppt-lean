# Notation library: polynomials

Builds on `CORE.md`. Each entry is labelled **Definition**, **Fact** or **Convention**.
Facts name the Lean result they rest on where there is one.

Throughout, `q = Xⁿ + a_{n−1}X^{n−1} + ⋯ + a₀` is monic with coefficients in `𝒫`, and
`r₁, …, rₙ ∈ ℂ` are its roots, repeated by multiplicity.

---

## 1. Polynomials as objects

**Definition.** `𝒫[X]` is the set of polynomials whose coefficients are all in `𝒫`.
A polynomial is *legal* when it lies in `𝒫[X]`.

**Fact.** `𝒫[X]` is closed under `+`, `−`, `×`, composition `f ∘ g`, shifting `f(X + c)`
and scaling `f(cX)` for `c ∈ 𝒫`, and division with remainder:

```
f = (f div g)·g + (f mod g),    deg(f mod g) < deg g
```

`gcd(f, g)` is legal too. All of these are arithmetic on coefficients.

**Convention.** A second variable `T` may appear alongside `X`. `𝒫[T]` and `𝒫[X, T]` are
defined in the same way. Every operation below acts on `X` and treats `T` as a constant, so
an operation that returns a number for a polynomial in `X` returns a polynomial in `T` for a
polynomial in `X` and `T`.

---

## 2. Roots

**Definition.** `{f = 0}` is the set of real roots of `f`. `{f = g}` is `{f − g = 0}`.
`{f = 0}_{≈v}` is the real root nearest `v`; `{f = 0}_{(k)}` is the `k`-th from the left.
`{T : u(T) = 0}` names the variable when it is not `X`.

**Fact (roots of low degree).** If `f ∈ 𝒫[X]`, `f ≠ 0` and `deg f ≤ 8`, then `{f = 0} ⊂ 𝒫`.

| degree | Lean | route |
|---|---|---|
| ≤ 3 | `cubicVal_root_Pconstructible` | cubic Bézier × the x-axis |
| ≤ 6 | `root_Pconstructible_le_six_coeffs` | `Y = X⁴`, `X⁵` × cubic graph; sextic via Bézier × sideways parabola |
| 7 | `root_Pconstructible_deg7_coeffs` | `TotallyReal/Main` |
| 8 | `root_Pconstructible_deg8_coeffs` | `Octic/Main`; `notes/octic/GUIDE-octic-cookbook.md` |

These are Facts, not Definitions. `{f = 0}_{≈v}` is not shorthand for a single crossing,
because `Γ_f` itself is generally not drawable when `deg f ≥ 5` or the coefficients are
not rational.

---

## 3. Graphs

**Fact (drawable graphs).** `Γ_f` is a shape when

| `f` | Lean |
|---|---|
| `f ∈ ℚ[X]`, `deg f ≤ 6` | `poly_graph` (a constructor) |
| `f ∈ 𝒫[X]`, `deg f ≤ 3`, over any bounded interval | a cubic Bézier |
| `f ∈ 𝒫[X]`, `deg f ≤ 4` | `quarticGraph_general_PConstructibleCurve` |
| `f = a Xᵇ`, `a, b ∈ ℚ`, on `x ≥ 0` | `power_law` (a constructor) |

So `(f ⋔ g)` is available for these, and in particular `f(u) ∈ 𝒫` for `u ∈ 𝒫`.

---

## 4. Trace

**Definition.** For a polynomial `u`,

```
Tr_q(u) := u(r₁) + u(r₂) + ⋯ + u(rₙ).
```

Inside a construction where `q` is fixed, write `⟨u⟩` for `Tr_q(u)` (declare it once).

**Fact.** If `u ∈ 𝒫[X]` then `Tr_q(u) ∈ 𝒫`, although the roots `rᵢ` generally are not.
*Reason:* `Tr_q(u)` is the trace of the linear map "multiply by `u`" on polynomials
modulo `q`, an `n`-dimensional space; its matrix has entries that are arithmetic in the
coefficients of `q` and `u`. Equivalently, by Newton's identities (§5).

**Fact.** `Tr_q(u)` depends only on `u mod q`: if `q` divides `u − u′` then
`Tr_q(u) = Tr_q(u′)`.

**Fact.** `Tr_q` is linear: `Tr_q(αu + βv) = α Tr_q(u) + β Tr_q(v)`. With the `T`
convention, `Tr_q((P + TR)³) = Tr_q(P³) + 3Tr_q(P²R)·T + 3Tr_q(PR²)·T² + Tr_q(R³)·T³`.

---

## 5. Power sums and Newton's identities

**Definition.** `s_j := Tr_q(Xʲ) = r₁ʲ + ⋯ + rₙʲ`, the `j`-th power sum of the roots.

**Fact (Newton).** For `q = Xⁿ + a_{n−1}X^{n−1} + ⋯ + a₀` and `k ≥ 1`,

```
s_k + a_{n−1} s_{k−1} + ⋯ + a_{n−k+1} s_1 + k·a_{n−k} = 0       (k ≤ n)
s_k + a_{n−1} s_{k−1} + ⋯ + a₀ s_{k−n} = 0                         (k > n)
```

so each `s_k` is arithmetic in the coefficients, and conversely the coefficients are
arithmetic in `s_1, …, s_n`. This is how traces are computed in practice:
`Tr_q(Σ cⱼXʲ) = Σ cⱼ s_j`.

---

## 6. The trace form

**Definition.** `⟨u, v⟩_q := Tr_q(uv)`, a symmetric bilinear form on polynomials modulo `q`.
Without a second argument, `⟨u⟩` still means `Tr_q(u)`; so `⟨uv⟩ = ⟨u, v⟩_q`.

**Definition (centring).** `m_j := Xʲ − s_j / n`, so that `⟨m_j⟩ = 0`.

**Definition (Gram–Schmidt).** `GS_q(u₁, …, u_k) = (g₁, …, g_k; d₁, …, d_k)` where

```
g₁ := u₁,       g_k := u_k − Σ_{i<k} (⟨u_k g_i⟩ / d_i) g_i,       d_k := ⟨g_k²⟩.
```

Defined as long as no `d_i = 0`. The `g_k` are mutually orthogonal for `⟨·,·⟩_q`. The `d_k`
play the role of squared lengths but can be negative.

**Fact (Sylvester).** If `q` has `ρ` distinct real roots, `s` pairs of non-real roots and no
repeated roots, the trace form has `ρ + s` positive and `s` negative directions. On the
centred polynomials (orthogonal to `1`, which has `⟨1⟩ = n > 0`) it has `ρ + s − 1` positive
and `s` negative. So the signs of `d₁, …, d_{n−1}` from `GS_q(m₁, …, m_{n−1})` count the
real roots.

For an octic this is the case split of the cookbook:

| real roots `ρ` | pairs `s` | negative `d`'s | case |
|---|---|---|---|
| 2 | 3 | 3 | A |
| 4 | 2 | 2 | A |
| 6 | 1 | 1 | B |
| 8 | 0 | 0 | C (the form is definite, so a different method) |

**Definition.** `u` is *isotropic* when `⟨u²⟩ = 0`.

---

## 7. Characteristic polynomial (Tschirnhaus transform)

**Definition.** For a polynomial `φ`,

```
χ_{q,φ}(Y) := (Y − φ(r₁))(Y − φ(r₂)) ⋯ (Y − φ(rₙ)).
```

Write `χ_φ` when `q` is fixed. This is the characteristic polynomial of "multiply by `φ`"
modulo `q`; classically, the Tschirnhaus transform of `q` by `φ`.

**Fact.** If `φ ∈ 𝒫[X]` then `χ_φ ∈ 𝒫[Y]`. Its power sums are `⟨φ^k⟩`, so its coefficients
follow from `⟨φ⟩, ⟨φ²⟩, …, ⟨φⁿ⟩` by Newton (§5).

**Fact.** If `q(x) = 0` then `χ_φ(φ(x)) = 0`. So a root `x` of `q` gives a root `y = φ(x)`
of `χ_φ`, and if `y` can be found, `x` is recovered from `{φ = y}` (or `{q mod (φ − y) = 0}`).

**Fact.** `χ_φ` has no `Y^{n−1}, …, Y^{n−k}` terms exactly when `⟨φ⟩ = ⟨φ²⟩ = ⋯ = ⟨φᵏ⟩ = 0`.
This is the lever of the octic construction: choosing `φ` to kill `⟨φ⟩, ⟨φ²⟩, ⟨φ³⟩` turns
`χ_φ` into `Y⁸ − Q(Y)` with `deg Q ≤ 4`.

---

## 8. Resultant and discriminant

**Definition.** `Res_X(f, g) := ∏ g(rᵢ)` over the roots `rᵢ` of a monic `f`.
`disc(q) := ∏_{i<j} (rᵢ − r_j)²`.

**Fact.** Both are arithmetic in the coefficients, so they are in `𝒫` (or `𝒫[Y]`).
`χ_{q,φ}(Y) = Res_X(q, Y − φ)`. `disc(q) ≠ 0` exactly when `q` has no repeated root, and
its sign is `(−1)^s`, with `s` the number of pairs of non-real roots.

---

## Example: the opening of the octic construction

```
Given        q ∈ 𝒫[X] monic of degree 8, irreducible; x ∈ {q = 0}.
Convention   ⟨u⟩ := Tr_q(u).
Definition   mⱼ := Xʲ − sⱼ/8,                        j = 1, …, 7
Definition   (g₁, …, g₇; d₁, …, d₇) := GS_q(m₁, …, m₇)
Fact         #{k : dₖ < 0} = number of pairs of non-real roots       (Sylvester)

Case A       a, b, c, d :∈ {indices with d_a, d_b < 0 < d_c, d_d}
Definition   P := g_a + √(−d_a/d_c) g_c,    R := g_b + √(−d_b/d_d) g_d
Choice       τ :∈ {T : ⟨(P + TR)³⟩ = 0}
Definition   φ := P + τR
Fact         ⟨φ⟩ = ⟨φ²⟩ = ⟨φ³⟩ = 0, so χ_φ = Y⁸ − Q(Y) with deg Q ≤ 4
Definition   y := (X⁸ ⋔ Q)_{≈φ(x)}
Claim        x = {φ = y}_{≈x}
```
