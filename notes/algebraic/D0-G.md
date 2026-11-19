# D0-G: degree of row G's hypersurface (Bézier × P-quartic graph)

2026-11-19. Follow-up to `D0.md` row G. Research only. Backend: Singular 4.3.2 (exact, mod p).
Scripts and outputs: `scripts/G_deg.py`, `scripts/G_ctl.sing`, `scripts/G_irr.py`, `*_out.txt`.

## Result

> **The row-G locus `Z ⊂ K ⊗ ℂ ≅ ℂ⁹` of good generators is a hypersurface of degree 180,
> irreducible over ℚ.** [Computed, exact mod p; irreducibility by factorisation patterns]

So the tangent-line idea (one P-point on `Z`, then a P-line tangent there, residual points of
degree ≤ 8) does not apply: a line through a point of `Z` meets it in 179 further points, a
tangent line in 178. Scoped negative: this kills Lemma-A-style use of row G at n = 9; it says
nothing about curves of low gonality on `Z`.

## Set-up

- Carrier: cubic Bézier `(X(t), Y(t))`; partner `y = Q(x)`, `Q` quartic. `N = Y − Q∘X`, degree 12.
- Normalise `X = t³ + a t² + b t` (the `x`-affine maps are absorbed by `Q`; leading coefficient 0
  gives crossing degree ≤ 8, impossible for a generator). The `t`-affine maps act on `τ` and make
  `Z` a cone: invariant under `τ ↦ λτ + μ𝟙`.
- `τ` lies on `Z` iff for some `(a, b)` there are `(c₂ : c₃ : c₄)` with
  `c₂X² + c₃X³ + c₄X⁴ mod χ_τ` of degree ≤ 3 (then `Y` is that remainder, `Q = Σ c_k x^k`; `N ≠ 0`
  because it has degree ≥ 6). So: the 5 × 3 matrix of the `t⁴ … t⁸` coefficients of
  `X^k mod χ_τ` (k = 2, 3, 4) has rank ≤ 2. Codimension 3 in `(τ, a, b)`, hence a hypersurface
  in `τ` (matches D0's `c_τ = 1`, effective fibre 0).
- Degree: restrict to a random line `τᵢ = τ₀ᵢ + s τ₁ᵢ` in conjugate coordinates (random in
  `F_p⁹`), `χ = ∏(t − τᵢ(s))`, and solve the 3 × 3 minors in `(a, b, s)`.

## Numbers

| p | line | dim | solutions `(a,b,s)` | deg of eliminant in `s` | squarefree | collision points `τᵢ = τⱼ` among roots |
|---|---|---|---|---|---|---|
| 32003 | seeds 1, 2, 3 | 0 | 180 | 180 | 180 | 0 |
| 1000003 | seed 4 | 0 | 180 | 180 | 180 | 0 |
| 65521 | seed 5 | 0 | 180 | 180 | 180 | 0 |

- One `(a, b)` per `s`: the fibre over a good generator is a single point (generically).
- No root sits at a coincidence of conjugates, so all 180 are genuine (`χ | N` with `χ` squarefree).

**Positive control** (`G_ctl.sing`). Planted `X₀ = t³ + 16801 t² + 31491 t` and random `Y, Q` mod
32003, factored `N`, took a squarefree degree-9 factor `χ₀`, and ran the same code on the line
`τ = τ₀ + s·g(τ₀)` (`g` random of degree 8). Output: 180 solutions, `s = 0` is one of them, and
the fibre over `s = 0` is exactly `(a, b) = (16801, 31491)`.

**Irreducibility** (`G_irr.py`). One integer line (entries in [−20, 20]) reduced mod 16 primes.
The intersection of the possible factor-degree subset sums is `{0, 180}` from p = 32057 on, so
the restriction is irreducible over ℚ and `Z` has no ℚ-component of smaller degree.

## Comparison

| row | hypersurface degree in `τ` |
|---|---|
| E (Bézier `(t², cubic)` × ℚ-sextic) | 10 |
| F (egg × ℚ-sextic) | 26 |
| **G (Bézier × P-quartic)** | **180** |
