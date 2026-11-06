# NOTES-nonic-meyer

**Conjecture N.** Every real root of a degree-9 polynomial with rational coefficients and at least
one non-real root is P-constructible.

**Verdict: PROVED.** The chain sketched in `PLAN-nonic-meyer.md` is correct after one repair: the
plan's suggested mechanism (rational `ψ` with *exact* collisions of real roots) is **impossible**;
the fix is to work first over `ℝ` (where collisions are one linear condition), obtain an *open,
nonempty* set of good real `ψ`, and then round to `ℚ` inside that open set. Meyer's theorem
(Hasse–Minkowski) turns the resulting indefinite rational quadratic form into a nonzero rational
`φ`. Everything else in the plan goes through. This lifts `root_Pconstructible_le_eight` past
degree 8 for every non-totally-real nonic.

Tags: **[proof]** mathematically proved here; **[Lean]** reuses/extends a Pptc lemma;
**[symbolic]** exact computer-algebra check; **[numeric, N digits]**.

---

## 0. Summary (12 lines)

1. Normalize `q` monic; if `q` is reducible or non-separable, a factor has degree `≤ 8`, so
   `root_Pconstructible_le_eight` (Basic.lean:632) finishes. Hence assume `q` irreducible, `r₂ ≥ 1`.
2. Let `A = ℚ[x]/(q)` (degree-9 field), `Tr` the field trace, `Q(f) = Tr(f²)`. By Hermite,
   `Q` on `A_ℝ` has signature `(r₁+r₂, r₂)`, and on `{Tr=0}` signature `(8−r₂, r₂)`. **[proof]**
3. For `ψ ∈ ℚ[x]`, `deg ≤ 6`, put `z = ψ(x)` and `V_ψ = {φ(z) : deg φ ≤ 6, Tr φ(z) = 0}`, a 6-dim
   ℚ-space when `z` generates `A`. A rational nonzero `f = φ(z) ∈ V_ψ` with `Q(f)=0` is what we need.
4. If `r₂ ≥ 3`, take `ψ = x`: `dim V = 6`, while the positive index of `{Tr=0}` is `8−r₂ ≤ 5`, so
   `Q|_V` is not definite; it is indefinite (Meyer) or has a rational radical (zero). **[proof]**
5. If `r₂ ∈ {1,2}`, choose real `ψ` with two collisions of real roots; interpolation gives
   `f₋, f₊ ∈ V_ψ` with `Q(f₋) < 0 < Q(f₊)`. **[proof]**
6. Indefiniteness is open in `ψ`; since `ℚ` is dense in `ℝ`, some **rational** `ψ` makes `Q|_{V_ψ}`
   indefinite. Meyer's theorem then gives `0 ≠ f = φ(z) ∈ V_ψ`, `φ ∈ ℚ[Y]`, with `Tr f = Tr f² = 0`.
7. Let `R = charpoly` of multiplication by `f` on `A`. Newton: `p₁=p₂=0 ⇒ e₁=e₂=0`, so
   `R(Y) = Y⁹ − p(Y)`, `p ∈ ℚ[Y]`, `deg p ≤ 6`. **[Lean]**
8. `y = f(β)` satisfies `y⁹ = p(y)`; `powerLaw_root_Pconstructible` (`n=9>6`, `a=1`) gives
   `y ∈ K`. **[Lean]**
9. `z` is a real root of `φ(X) − y`, degree `≤ 6` over `K`, so `root_Pconstructible_le_six_coeffs`
   gives `z ∈ K`. **[Lean]**
10. `β` is a real root of `ψ(X) − z`, degree `≤ 6` over `K`, so the same lemma gives `β ∈ K`. ∎
11. Totally real nonics are excluded structurally: `Q` is positive definite on `{Tr=0}` and
    `Tr f² = 0 ⇒ f = 0`. **[proof]**
12. Degree 10 would need `p₁=p₂=p₃=0` (a quadric and a cubic simultaneously) — no Meyer analogue.

---

## 1. Setup and the trace form

Let `q ∈ ℚ[x]` be monic of degree 9 with at least one non-real root, and let `β` be a real root.
Write `r₁` for the number of real roots and `r₂` for the number of non-real conjugate pairs, so
`r₁ + 2 r₂ = 9` and `r₂ ≥ 1`.

Assume from now on that `q` is **irreducible** over `ℚ`; then `q` is separable (char 0) and
`A := ℚ[x]/(q)` is a field of degree 9 over `ℚ`. We identify `A` with the ℚ-span of
`1, x, …, x⁸`. Let `Tr : A → ℚ` be the field trace. Since `q` is real, the real algebra
`A_ℝ := A ⊗_ℚ ℝ ≅ ℝ[x]/(q)` splits as

```
A_ℝ  ≅  ℝ^{r₁} × ℂ^{r₂},
```

one copy of `ℝ` per real root and one copy of `ℂ` per conjugate pair. Put

```
B(u,v) = Tr(uv),      Q(u) = B(u,u) = Tr(u²).
```

**Lemma 1.1 (Hermite).** `B` is a nondegenerate symmetric ℚ-bilinear form on `A`. Its signature
over `ℝ` is `(r₁+r₂, r₂)`. On the hyperplane `W = {u ∈ A : Tr u = 0}` the signature is
`(r₁+r₂−1, r₂)`. **[proof]**

*Proof.* On a real factor `ℝ` with root `λ`, the form is `u ↦ u(λ)²`, positive definite of rank 1.
On a complex factor, with `w = a+bi`, the form is `2Re(w²) = 2(a²−b²)`, of signature `(1,1)`, no
kernel. Adding gives `(r₁+r₂, r₂)`; there is no kernel because each factor is nondegenerate. The
vector `1` has `Q(1) = 9 > 0`, and `W = 1^⊥`, so restricting removes exactly one positive direction.
Since `r₁ ≥ 1`, `r₁+r₂−1 ≥ r₂`. ∎

The Gram entries are the power sums `s_m = Tr(x^m) = Σ_roots λ_i^m ∈ ℚ`, so `B, Q` are
*polynomials with rational coefficients* in the coordinates. In particular they are computed by
exact rational arithmetic from `q` alone. **[symbolic]**

**Meyer's theorem.** *Let `Q` be a quadratic form in `n ≥ 5` variables over `ℚ`. If `Q` is
indefinite over `ℝ` (takes both signs), then `Q` has a nonzero rational zero. If `Q` is degenerate,
any nonzero radical vector is a zero.* **[proof]** It follows from Hasse–Minkowski (Serre, *A Course
in Arithmetic*, Ch. IV, Thm. 8 and Cor. 2): over `ℚ_p` every form of dimension `≥ 5` is isotropic,
so the only obstruction is the real place, where indefiniteness is exactly isotropy. (The statement
is sharp: `x₁²+x₂²−p x₃²−p x₄²` with `p ≡ 3 (4)` is an anisotropic indefinite 4-variable form; see
the references in §8.) Degenerate case: the radical is defined by rational linear equations. ∎

---

## 2. The Tschirnhaus space `V_ψ`

Fix `ψ ∈ ℚ[x]` (later `ψ` may be real) with `deg ψ ≤ 6`, and put `z = ψ(x) ∈ A`. Define

```
V_ψ := span_ℚ{1, z, …, z⁶} ∩ W,     W = {Tr = 0}.
```

As long as `1, z, …, z⁶` are linearly independent (equivalently `z` generates `A` over `ℚ`, since
`dim ℚ[z] ∈ {1,3,9}` for a degree-9 field), we have `dim V_ψ = 7−1 = 6`. Any `f ∈ V_ψ` is
`f = φ(z)` for a unique `φ ∈ ℚ[Y]` of degree `≤ 6`, and `Tr f = 0`.

The plan's **Step 2** asks for a nonzero `φ` with `Tr φ(z) = Tr φ(z)² = 0`, i.e. a nonzero
`f ∈ V_ψ` with `Q(f) = 0`. Since `V_ψ` is a 6-dimensional ℚ-space and `Q|_{V_ψ}` is a rational
quadratic form, Meyer's theorem (§1) applies *provided `Q|_{V_ψ}` is indefinite*.

### 2.1 The plan's collision mechanism does not give rational `ψ` **[proof]**

The plan suggests choosing `ψ` with `ψ(ρ₁) = ψ(ρ₂)` for two real roots. Suppose `ψ ∈ ℚ[x]` had
`deg ≤ 6` and `ψ(ρ₁) = ψ(ρ₂) = t`, with `ρ₁ ≠ ρ₂` conjugate (both roots of the irreducible `q`).
Because `σ(ψ(ρ₁)) = ψ(ρ₂)` for the isomorphism `σ : ℚ(ρ₁) → ℚ(ρ₂)` with `σ(ρ₁) = ρ₂`, the value
`t` is fixed by `σ`, so `t ∈ ℚ(ρ₁) ∩ ℚ(ρ₂)`. If `ℚ(β)` has no cubic subfield — in particular if
the Galois group is `S₉` — then `ℚ(ρ₁) ∩ ℚ(ρ₂) = ℚ`, so `t ∈ ℚ`, and `ψ(X) − t ∈ ℚ[X]` vanishes
at `ρ₁`; since `q` is irreducible of degree 9 and `deg(ψ−t) ≤ 6 < 9`, `ψ` is constant. (If
`ℚ(β)` does have a cubic subfield, a nonconstant rational collision can exist, but no uniform
choice is available, and it is not needed.)

Thus the plan's §3.2 mechanism cannot be run over `ℚ`. The obstruction is purely rational,
however: over `ℝ`, `ρ₁^k − ρ₂^k` are *real numbers*, so each collision is **one** real linear
condition on the seven coefficients of `ψ`, and the solution space is 5-dimensional. This is the
key repair. **[symbolic]** (A separate tensor-ring computation shows that the stronger condition
`ψ(ρᵢ) = ψ(ρ_j)` for *all* pairs has solution space exactly the constants, in
`ℚ[a,b]/(q(a),q(b))`; but the single-pair condition above is the relevant one.)

### 2.2 The repair: real collisions, then round

Let `r₂ ∈ {1,2}`, so `r₁ = 9 − 2r₂ ≥ 5` and there are at least four real roots. Choose
`ψ₀ ∈ ℝ[x]`, `deg ψ₀ ≤ 6`, satisfying the two real linear conditions

```
ψ₀(ρ₁) = ψ₀(ρ₂),        ψ₀(ρ₃) = ψ₀(ρ₄).
```

The solution space over `ℝ` has dimension `≥ 5`, hence contains nonconstant `ψ₀`; choosing `ψ₀`
generically in it, we may assume:

* the distinct real `z`-values `w₁,…,w_D` (`D = r₁ − 2`) are distinct;
* the complex values `z_{c,k} = ψ₀(λ_k)` (`k = 1,…,r₂`) are non-real, distinct, and different
  from the `w_j`;
* `z₀ = ψ₀(x)` generates `A` (so `dim V_{ψ₀} = 6`).

(Each failure is a proper algebraic subset of the coefficient space, and the 5-dimensional collision
space is not contained in such a subset.)

**Lemma 2.1.** `Q|_{V_{ψ₀}}` is indefinite. **[proof]**

*Proof.* Count conditions: `D + 2r₂ = (r₁−2) + 2r₂ = 7`. Since a nonzero real polynomial of
degree `≤ 6` cannot vanish at seven distinct complex points, the evaluation map
`ℝ[Y]_{≤6} → ℝ^D × ℂ^{r₂}` is injective, hence an isomorphism. For the prescribed values
`φ₋(w_j) = 0` and `φ₋(z_{c,1}) = i`, `φ₋(z_{c,k}) = 0` (`k ≥ 2`), let `φ₋` be the unique
interpolant, and set `f₋ = φ₋(z₀)`. Then `f₋ ∈ V_{ψ₀}` and

```
Tr f₋ = Σ_{real} φ₋(w) + Σ_k (φ₋(z_{c,k}) + φ₋(z̄_{c,k})) = 0,
Q(f₋) = Σ_{real} φ₋(w)² + Σ_k 2Re(φ₋(z_{c,k})²) = 2Re(i²) = −2 < 0.
```

For the positive direction take `φ₊` with `φ₊(w_j) = 0`, `φ₊(z_{c,1}) = 1`, `φ₊(z_{c,k}) = 0`
(`k≥2`), and `g = φ₊(z₀)`. Then `Tr g = 2`, `Q(g) = 2`, and the projection
`f₊ := g − (2/9)·1 ∈ V_{ψ₀}` satisfies `Q(f₊) = Q(g) − (Tr g)²/9 = 2 − 4/9 = 14/9 > 0`.
So `Q|_{V_{ψ₀}}` takes both signs. ∎

*(Numerical confirmation: at 120 dps the unique interpolant indeed gives `φ₋(w_j)=0`,
`φ₋(z_c)=i`, hence `Q(f₋)=−2` and `Tr f₋=0`; the earlier apparent failure was floating-point
conditioning, since the real collision forces some `z`-values to be large. **[numeric, 120 digits]**)*

**What goes wrong over ℚ, and why it does not matter.** A rational `ψ` near `ψ₀` will *not* have
exact collisions. But indefiniteness is **open**:

**Lemma 2.2.** The set `S = {ψ ∈ ℝ⁷ : dim V_ψ = 6 and Q|_{V_ψ} is indefinite}` is open and
nonempty, hence contains a rational `ψ`. **[proof]**

*Proof.* Nonempty by Lemma 2.1. For openness, the elements `g_k(ψ) = z^k − (Tr z^k/9)·1`
(`k = 1,…,6`, `z = ψ(x)`) are continuous in the coefficients of `ψ` and form a basis of `V_ψ` when
`dim V_ψ = 6`. Write `f₋ = Σ a_k g_k(ψ₀)`, `f₊ = Σ b_k g_k(ψ₀)`; then
`f₋(ψ) = Σ a_k g_k(ψ)` and `f₊(ψ) = Σ b_k g_k(ψ)` are again in `V_ψ`, depend continuously on `ψ`,
and satisfy `Q(f₋(ψ)) < 0 < Q(f₊(ψ))` for all `ψ` near `ψ₀`. Since `ℚ⁷ ⊆ ℝ⁷` is dense, `S`
contains a rational point. ∎

Applying Meyer's theorem to this rational `ψ`, we obtain

> **Corollary 2.3.** There exist `ψ, φ ∈ ℚ[Y]`, `deg ψ, deg φ ≤ 6`, `φ ≠ 0`, with
> `Tr φ(ψ(x)) = Tr φ(ψ(x))² = 0`. Equivalently, there is a nonzero rational
> `f = φ(ψ(x)) ∈ A` with `Tr f = Tr f² = 0`. **[proof]**

---

## 3. The reduction chain (Steps 3–6) **[proof]**

Assume `q` irreducible and `r₂ ≥ 1`.

**Step 3 (resolvent).** Take rational `f = φ(ψ(x)) ∈ A` from Corollary 2.3 (for `r₂ ≥ 3` use
`ψ = x`, see §4; for `r₂ ∈ {1,2}` use §2). Let `C` be the companion matrix of `q` (so
multiplication by `x` on `A`), and `M_f = φ(ψ(C))` the 9×9 rational matrix of multiplication by
`f`. Let `R(Y) = charpoly(M_f) = ∏_{i}(Y − f(λ_i)) ∈ ℚ[Y]`, monic of degree 9. Its power sums are
`p_k = Tr(f^k)`. Newton's identities give `p₁ = e₁`, `p₂ = e₁p₁ − 2e₂`; since `p₁ = p₂ = 0`, also
`e₁ = e₂ = 0`. Writing `R = Y⁹ − e₁Y⁸ + e₂Y⁷ − e₃Y⁶ + ⋯`, we get

```
R(Y) = Y⁹ − p(Y),      p(Y) = e₃Y⁶ − e₄Y⁵ + e₅Y⁴ − e₆Y³ + e₇Y² − e₈Y + e₉ ∈ ℚ[Y],
```

so `deg p ≤ 6`. **[symbolic]** (Newton's identities are available in Mathlib via
`Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities`, already imported by
`DegreeSeven.lean`; the `DegreeSeven` development runs exactly this argument for `n = 7`.)

**Step 4 (`y ∈ K`).** Put `y = f(β) = φ(ψ(β)) ∈ ℝ`. Since `β` is a root of `q`, `y` is an
eigenvalue of `M_f`, so `y` is a root of `R`: `y⁹ = p(y)`. If `y = 0` then `y ∈ K`. Otherwise
`y ≠ 0`, `p ∈ ℚ[x]`, `deg p ≤ 6 < 9 = n`, and `powerLaw_root_Pconstructible`
(Basic.lean:561) with `a = 1`, `n = 9` gives `y ∈ K`. **[Lean]**

**Step 5 (`z ∈ K`).** Put `z = ψ(β) ∈ ℝ`. Then `z` is a real root of `Φ(X) = φ(X) − y`. Here
`φ ∈ ℚ[X]` has degree `≤ 6`, so `deg Φ ≤ 6`; `Φ ≠ 0` because `φ` is nonconstant (a constant `c`
would give `Tr φ(z) = 9c = 0`, hence `f = 0`, contrary to Corollary 2.3). Its coefficients are
rational except the constant term `−y ∈ K`, hence all P-constructible. By
`root_Pconstructible_le_six_coeffs` (Basic.lean:1372), `z ∈ K`. **[Lean]**

**Step 6 (`β ∈ K`).** `β` is a real root of `Ψ(X) = ψ(X) − z`. Since `ψ` is nonconstant of degree
`≤ 6`, `deg Ψ ≤ 6` and `Ψ ≠ 0`; its coefficients are rational except the constant term `−z ∈ K`.
By `root_Pconstructible_le_six_coeffs`, `β ∈ K`. **[Lean]**

**Theorem 3.1 (Conjecture N).** *Every real root of a degree-9 polynomial with rational coefficients
and at least one non-real root is P-constructible.* **[proof]**

*Proof.* Normalize to monic. If `q` is reducible, `q = q₁q₂` with `1 ≤ deg q_i ≤ 8`, and `β` is a
root of `q₁` or `q₂`, so `root_Pconstructible_le_eight` (Basic.lean:632) applies. If `q` is
non-separable over `ℚ` (a repeated factor), the same reduction works. Otherwise `q` is separable;
split on `r₂ ≥ 3` versus `r₂ ∈ {1,2}`, apply §4 resp. §2 to obtain `f`, then Steps 3–6. ∎

The hypothesis "non-real root" is essential and is used exactly once — to make the trace form
indefinite; compare §6.

---

## 4. Indefiniteness for `r₂ ≥ 3`: the dimension count **[proof]**

Let `ψ = x`, so `z = x`, `V = span{1,x,…,x⁶} ∩ W`, `dim V = 6` (since `q` irreducible of degree 9).
By Lemma 1.1, `W` has signature `(8−r₂, r₂)`. A positive-definite subspace of `V` is also
positive definite in `W`, so the positive index `π` of `Q|_V` satisfies `π ≤ 8 − r₂`. For
`r₂ ≥ 3` this is `≤ 5 < 6 = dim V`. Likewise the negative index is `≤ r₂ ≤ 4 < 6`. Hence
`Q|_V` is neither positive nor negative definite. Therefore:

* if `Q|_V` is indefinite, Meyer's theorem gives a nonzero rational `f ∈ V` with `Q(f)=0`;
* otherwise `Q|_V` is semidefinite; since it is not definite it has nonzero radical, which is a
  rational subspace (defined by rational linear equations) and yields a nonzero rational `f ∈ V`
  with `Q(f)=0`.

In both cases `Tr f = 0` (as `f ∈ W`) and `Q(f) = Tr f² = 0`, and `f = φ(x)` with `φ ∈ ℚ[Y]`,
`deg φ ≤ 6`. **[proof]**

This is why `r₂ = 3` is the first case where the *simplest* `ψ = x` always works, matching the seed
numerics (0 failures for `r₂ ≥ 3`; occasional failures for `r₂ ≤ 2`).

---

## 5. Indefiniteness for `r₂ ∈ {1,2}`

Section 2.2 gives the complete proof. For the record:

* `r₂ = 1`, `r₁ = 7`: two real collisions, `D = 5`; conditions `5 + 2 = 7`.
* `r₂ = 2`, `r₁ = 5`: two real collisions, `D = 3`; conditions `3 + 4 = 7`.

In both cases `Q|_{V_{ψ₀}}` is indefinite over `ℝ` (Lemma 2.1), the good set is open (Lemma 2.2),
and a rational good `ψ` exists. No explicit choice of `ψ` uniform in the configuration is needed:
existence follows from openness and density.

The plan's §3.2 "suggested mechanism" (routing `ψ(r₁) ≈ ψ(r₂)` etc.) is therefore superseded: the
correct statement uses *exact* real collisions, which the plan's own numerics could not
see because over `ℚ` they are invisible.

### 5.1 When `z` does not generate (§3.3 resolved)

For a degree-9 field `ℚ(β)`, `dim ℚ[z] ∈ {1,3,9}`. Our `ψ` is chosen generically, so
`ℚ[z] = ℚ(β)` and `dim V_ψ = 6`. Thus the case `ℚ[z] ⊊ ℚ(β)` **does not arise**. It is worth
noting that the *recovery* steps 5–6 would still work even for a cubic `ℚ(z)` (β would have degree
3 over it, and `root_Pconstructible_le_six_coeffs` handles degree ≤ 6); only Meyer's existence step
needs `dim V_ψ ≥ 5`. Since generating `ψ` is generic and open, we simply choose one.

---

## 6. Why totally real nonics are excluded (§2) **[proof]**

If `q` is totally real, then `r₂ = 0` and Lemma 1.1 gives that `Q` is positive definite on `A`
(hence on `W`). The reduction requires a nonzero `f ∈ W` with `Tr f² = Q(f) = 0`, which forces
`f = 0`; then `φ` is the zero polynomial and Steps 4–6 collapse. No change of Tschirnhaus degree
helps: the requirement `R(Y) = Y⁹ − p(Y)`, `deg p ≤ 6`, is equivalent to `e₁ = e₂ = 0`, i.e.
`Tr f = Tr f² = 0`, and the second equation is impossible for nonzero `f ∈ W`. A different engine
for Step 4 is irrelevant, because the obstruction is at Step 2 (producing `f` at all). So the
non-real root is not a technical convenience but exactly what supplies the negative directions.

---

## 7. Worked examples (§3.5) **[symbolic] [numeric, 120 digits]**

For all three we use `ψ = X` (these are generic configurations for which `Q|_V` is already
indefinite); `z = β`. The rational isotropic vector `a = (a₁,…,a₆)` is the Meyer zero, giving
`φ(X) = Σ_{k=1}^{6} a_k X^k − (Σ a_k s_k)/9` (so `Tr φ = Tr φ² = 0`). The resolvent
`R(Y) = Y⁹ − p(Y)` was computed exactly from the 9×9 multiplication matrix (using
`s_m = Tr(C^m)` from the companion matrix `C` of `q`). `c₈ = c₇ = 0` confirms `e₁ = e₂ = 0`.

### Example 1 — `r₂ = 1` (7 real roots)

```
q(X) = X⁹ + X⁸ − 6X⁷ − 5X⁶ + 6X⁵ + 2X⁴ + 5X³ + 4X² − 6X − 1
φ(X) = −4X⁶ − 5X⁵ + 22X⁴ + 25X³ − 14X² − 30X − 18
```
`a = (−30, −14, 25, 22, −5, −4)`, `p(Y) = −89993Y⁶ + 1682098Y⁵ + 167114677Y⁴ + 636379207Y³
− 53731078373Y² − 617049675875Y − 1226014817119`.
`β ≈ −2.16153586003744713390685988583`, `y = φ(β) ≈ 37.1636163719503604377654714393`,
`|y⁹ − p(y)| < 2.2·10⁻¹⁰⁶`, `Tr φ = 0`, `Tr φ² = 0` (exactly, and `~10⁻¹¹⁹` numerically).

### Example 2 — `r₂ = 2` (5 real roots)

```
q(X) = X⁹ − 5X⁷ + X⁶ + 2X⁵ − 2X⁴ − 6X³ − X² + 4X − 1
φ(X) = 9X⁵ + 5X⁴ − 28X³ − 30X² − 30X + 47/3
```
`a = (−30, −30, −28, 5, 9, 0)`,
`p(Y) = −(11507878/9)Y⁶ + (471272119/3)Y⁵ − (52299576928/9)Y⁴ + (19295463835124/243)Y³
− (26666013713147/81)Y² − (1347593229958660/243)Y + 41757373726307792/19683`.
`β ≈ −2.24859264957403362851590715666`, `y = φ(β) ≈ −139.761284957337083117632086671`,
`|y⁹ − p(y)| < 2.9·10⁻¹⁰¹`.

### Example 3 — `r₂ = 4` (1 real root)

```
q(X) = X⁹ + 6X⁸ − 4X⁷ + X⁶ − X⁵ − 5X⁴ − 2X³ + 5X² + X + 1
φ(X) = −4X⁶ − 25X⁵ + 9X⁴ − 10X³ − 25X² − 30X + 7/3
```
`a = (−30, −25, −10, 9, −25, −4)`,
`p(Y) = (864577/9)Y⁶ + (24414046/3)Y⁵ + (17942103709/9)Y⁴ − (13300621641397/243)Y³
+ (101851610123033/81)Y² − (3221785618549159/243)Y + 1885056216866768503/19683`.
`β ≈ −6.62738164424675597988673222875`, `y = φ(β) ≈ 76.7132311591600577129538678011`,
`|y⁹ − p(y)| < 9.1·10⁻¹⁰¹`.

### Galois evidence

All three `q` are irreducible (so every root has degree exactly 9, already outside the degree-≤8
class). The discriminant is a non-square (`disc < 0` for Example 1; positive non-square otherwise),
so the Galois group is not contained in `A₉`. Each polynomial has a Frobenius element of cycle type
`(2,1⁷)` (a transposition): primes `13` for Example 1, `3917` for Example 2, and `2096374652970107`
for Example 3. A transitive group containing a transposition is the full symmetric group, so all
three have **Galois group `S₉`**. (Cycle types observed modulo small primes include
`(9,)`, `(8,1)`, `(7,2)`, `(5,4)`, `(4,4,1)`, `(3,3,3)`, `(2,2,2,2,1)`, ….) **[numeric, exact
finite-field arithmetic]**

These examples are "generic" in that `ψ = X` already succeeds; the purpose of §2.2 is to cover the
exceptional configurations (observed in the float signature search: about `0.2–0.7 %` of `r₂ = 1`
configurations, and rare `r₂ = 2` ones) where `ψ = X` alone fails.

---

## 8. Scope and novelty (§3.6)

### 8.1 Degree 10

To reach `R(Y) = Y^{10} − p(Y)` with `deg p ≤ 6`, Newton forces `e₁ = e₂ = e₃ = 0`, i.e.

```
Tr f = Tr f² = Tr f³ = 0.
```

On the 6-dimensional Tschirnhaus space this is a *quadric and a cubic simultaneously* (a
codimension-2 complete intersection in `ℙ⁵`). There is **no Meyer analogue**: Hasse–Minkowski
applies to one quadratic form, and its power comes from `n ≥ 5`. For two forms, rational points can
fail (Brauer–Manin obstructions for del Pezzo surfaces / complete intersections of quadrics), and
even the dimension count is unfavourable (no longer a single indefinite form). Using Tschirnhaus
maps in two generators gives more variables but couples the recovery of `β` and does not remove the
`p₁=p₂=p₃=0` requirement. This is the precise obstruction. **[proof / survey]**

### 8.2 Other results

* The degree-≤ 8 theorem is already complete over ℚ, so no octic gain from this method.
* The same "real Tschirnhaus + Meyer over ℚ" pattern could sharpen any existing result where a
  *rational* map killing the top coefficients of a resolvent is the blocker, provided the relevant
  trace form has dimension `≥ 5` and is indefinite. For the septic-over-`K` theorem
  (`root_Pconstructible_of_nonreal_root`) the trace form is over the constructible field `K`, not
  `ℚ`, so Meyer as stated does not apply; extending it would need a local–global theory over `K`.
  **[lead]**

### 8.3 Novelty and references

The ingredients are classical; the combination appears not to be in the standard literature.

* **Tschirnhaus / Bring–Jerrard.** The reduction of a polynomial by a Tschirnhaus map killing the
  top coefficients is classical (Tschirnhaus 1683; Bring 1786; Jerrard 1852). Standard treatments
  work over `ℂ` and concern radical solvability: V. Adamchik, D. J. Jeffrey, *Polynomial
  transformations of Tschirnhaus, Bring and Jerrard*, ACM SIGSAM Bull. **37** (2003) 90–94,
  https://doi.org/10.1145/1093528.1093530 ; T. Piezas III, *The Bring–Jerrard quintic*,
  https://www.oocities.org/titus_piezas/Tschirnhausen.pdf ; Wikipedia, *Tschirnhaus transformation*.
* **Meyer / Hasse–Minkowski.** J.-P. Serre, *A Course in Arithmetic*, Ch. IV (Thm. 8, Cor. 2);
  Wikipedia, *Meyer's theorem*, https://en.wikipedia.org/wiki/Meyer%27s_theorem ;
  Wikipedia, *Hasse–Minkowski theorem*.
* **Effective rational zero (the plan's §3.4).** D. Simon, *Quadratic equations in dimensions 4, 5
  and more* (dimension-5 algorithm, `qfsolve`), https://simond.users.lmno.cnrs.fr/maths/Dim4.pdf ;
  P. Castel, *Solving quadratic equations in dimension 5 or more without factoring*, ANTS X (2013),
  https://doi.org/10.2140/obs.2013.1.213 ; J. W. S. Cassels' search bound, surveyed in
  L. Fukshansky, *Heights and quadratic forms: Cassels' theorem and its generalizations*,
  https://arxiv.org/abs/1204.1938 . For our examples the zero was found by clearing denominators,
  rational congruence-diagonalising the 6×6 Gram matrix, and searching the diagonal form.
* **Trace forms.** Serre, *L'invariant de Witt de la forme Tr(x²)*, Comment. Math. Helv. **59**
  (1984); Conner–Perlis, *A Survey of Trace Forms of Algebraic Number Fields*; A. Prestel, *On trace
  forms of algebraic function fields*; A. Candel–D. Rota, "Computing multidimensional residues"
  (trace form signature counts real roots), https://arxiv.org/abs/alg-geom/9404011 . Kraft–Procesi
  and Hilbert's 13th are the surrounding "constructibility / rational maps" literature; no source
  found deduces rational constructibility of high-degree real algebraic numbers from Meyer.
* **Conclusion.** The use of Meyer's theorem to obtain a *rational* (not merely real) Tschirnhaus
  polynomial with `Tr f = Tr f² = 0`, and hence to push the power-law construction past degree 8,
  appears to be new.

---

## 9. Lean feasibility report (§3.7)

**Search results (Mathlib at Lean 4.33).**

* `lean_local_search "HasseMinkowski"` / `"Minkowski"` → **nothing**.
* `lean_local_search "isotrop"` → only `Pconstructible.isotropic_plane_trivial` in
  `Pptc/DegreeSeven.lean`. `QuadraticMap.Anisotropic`, `QuadraticMap.not_anisotropic_iff_exists`
  and `QuadraticMap.PosDef.anisotropic` exist in `Mathlib/LinearAlgebra/QuadraticForm/Basic.lean`,
  but there is **no** Hasse–Minkowski, no local-field form theory, no Meyer's theorem.
* `Algebra.traceForm` exists (`Mathlib/RingTheory/Trace/Defs.lean`) with basic symmetry/`toMatrix`
  lemmas, but nothing about signatures or isotropy.
* Pptc's `Pptc/DegreeSeven.lean` already contains the trace-form infrastructure:
  `companion7`, `companion7'`, `companion7'_trace_pow`, `companion7'_trace_aeval`,
  `companion7_trace_aeval` (trace = sum over roots), `companion7_charpoly_aeval_isRoot`, the
  coefficient-killing lemma at ~l.271 (`e₁=e₂=e₃=0`), `trace_pow_eq_sum_eigen`, and
  `isotropic_plane_trivial`; it imports
  `Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities`.

**Assessment.**

* *Cheap:* the companion-matrix / trace / Newton parts are dimension-agnostic and generalise from
  `Fin 7` to `Fin 9` by mechanical editing (`companion7` → `companion9`, sums over `Fin 9`, the
  `n=9` power law). `powerLaw_root_Pconstructible` and `root_Pconstructible_le_six_coeffs` are
  already there. The final theorem is a short assembly.
* *Expensive:* the one real missing ingredient is **Meyer's theorem over ℚ for `n ≥ 5`**, and behind
  it Hasse–Minkowski and the `p`-adic form theory. Mathlib has `QuadraticMap` over arbitrary rings
  but essentially none of the arithmetic theory. A special-case proof for the concrete trace form
  would still need local solvability at `2` and at primes dividing the discriminant, i.e. Hensel's
  lemma for quadratic forms and the Hilbert symbol — a substantial development (comparable to the
  existing analytic-number-theory efforts) rather than a few lemmas.
* **Implemented (with Meyer as the single `sorry`).** Four new files, all compiling:
  * `Pptc/NonicResolvent.lean` — `companion9`, `companion9'`, `companionVec9`, the eigenvector
    lemmas and `companion9_charpoly_aeval_isRoot` (mechanical `Fin 7 → Fin 9` generalisation).
  * `Pptc/NonicRecovery.lean` — `rat_eval_root_Pconstructible` and `nonic_recovery` (steps 5–6).
  * `Pptc/NonicPowerLaw.lean` — `resolvent_powerLaw9` and `resolvent_y_Pconstructible9`: the
    rational resolvent `Y⁹ − p(Y)` with `deg p ≤ 6`, then the `n = 9` power law.
  * `Pptc/Nonic.lean` — `root_Pconstructible_of_rat_nonic_nonreal` (general) and `..._sep`
    (monic separable), with the single `sorry` isolated in `exists_tschirnhaus9`. The general
    statement is reduced to the monic separable one by normalising and passing to `minpoly ℚ β`.
  `lake_check Pptc/Nonic.lean` passes with exactly one `sorry` warning.

```lean
-- the single gap (Meyer/Hasse–Minkowski); equivalent to Tr f = Tr f² = 0 by Newton:
theorem exists_tschirnhaus9 {q : Polynomial ℚ} (hmon : q.Monic) (h9 : q.natDegree = 9)
    (hsep : q.Separable)
    (hrel : ∃ z : ℂ, (q.map (algebraMap ℚ ℂ)).eval z = 0 ∧ z.im ≠ 0) :
    ∃ ψ φ : Polynomial ℚ, ψ.natDegree ≤ 6 ∧ 1 ≤ ψ.natDegree ∧
      φ.natDegree ≤ 6 ∧ 1 ≤ φ.natDegree ∧
      ((aeval (companion9' q) (φ.comp ψ)).charpoly).coeff 8 = 0 ∧
      ((aeval (companion9' q) (φ.comp ψ)).charpoly).coeff 7 = 0 := by
  sorry

-- fully proved from the above:
theorem root_Pconstructible_of_rat_nonic_nonreal {q : Polynomial ℚ} (hq : q ≠ 0)
    (h9 : q.natDegree = 9)
    (hrel : ∃ z : ℂ, (q.map (algebraMap ℚ ℂ)).eval z = 0 ∧ z.im ≠ 0)
    {β : ℝ} (hβ : aeval β q = 0) : PConstructible β
```

* **What remains for a sorry-free proof.** Fill `exists_tschirnhaus9`, i.e. formalise §3–§5: the
  Hermite signature `(r₁+r₂, r₂)` of the trace form, the `r₂ ≥ 3` dimension count
  (`indefinite_or_radical`), and the `r₂ ∈ {1,2}` real-collision/openness argument, then Meyer.
  The Newton equivalence `charpoly.coeff 8 = 0 ∧ coeff 7 = 0 ↔ Tr f = Tr f² = 0` is the bridge
  between the statement above and the trace-form formulation.

---

## 10. Side discoveries and leads

* **The plan's central mechanism was wrong but repairable.** Over `ℚ`, a degree-`≤ 6` Tschirnhaus
  map cannot collide two distinct roots of an irreducible nonic unless the root field has a cubic
  subfield (in particular it cannot for `S₉`). The entire strategy survives because the obstruction
  is rational and indefiniteness is open.
* **`r₂ ≥ 3` needs no Tschirnhaus map.** `ψ = x` always works there, by a pure dimension count on
  the trace form. The hard cases are `r₂ = 1` and `r₂ = 2`, exactly where the positive index of
  `{Tr=0}` is `≥ 6`.
* **Reducible nonics are free.** Any factorization has a factor of degree `≤ 8`, so the "hard"
  irreducible case is the only one.
* **Lead:** the same openness/density trick might replace constructible-but-irrational engines in
  `Offset.lean` / `DegreeSeven.lean`, wherever a *real* existence proof plus an open good set could
  be rounded to `ℚ`.
* **Lead:** for totally real nonics the trace form is positive definite; the only hope for those
  roots would be a genuinely different engine (arc length, offsets, or the `gamma` machinery), not a
  Tschirnhaus reduction. Worth stating as the sharp limit of the power-law method.
* **Lead:** degree 10 needs a rational point on a quadric ∩ cubic in 6 variables. A concrete
  counterexample-search (integer decics with a non-real root) would test whether the method is
  genuinely blocked; no Meyer analogue is available, but special configurations might still be
  reachable by a quadratic Tschirnhaus map followed by a second (non-polynomial) step.
