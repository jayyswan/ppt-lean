# D1E: row E, the Bézier `(t², cubic)` against a rational sextic graph

Stream E of `PLAN-degree9.md` (the D1 sub-stream D0 ranked first), 2026-11-13. Research only: no
`.lean` edits, no `Defs` changes. Backend: Wolfram (wolfram MCP) for every number; Python not used.
Labels: [Proof], [Proof sketch], [Computed, exact], [Heuristic], [Open]. Every negative is scoped
to this route. Log: `HANDOFF-alg-D1E.md`.

**Verdict: open.** The condition is now explicit and much simpler than D0 had it (§1, §2). E-solvable
fields are exactly the root fields of an explicit rational 8-parameter family (§2). The remaining
problem is one ℚ-point on a degree-10 hypersurface in `ℙ(K)`, i.e. versality of that family (§6).
- A height-2 search on `q₃` is null; a comparable positive control was found by the same code (§4).
- `X_{q₃}` is locally soluble at ∞, at 2 and at every checked odd prime (§6).

## 0. Findings

1. **The E condition sees only `Tr τ`, `Tr τ³`, `Tr τ⁵`, `Tr τ⁷` [Proof].**
   `4725 · s₍₄,₃,₂,₁₎(τ) = H(p₁, p₃, p₅, p₇)`, where

   > `H = p₁¹⁰ − 15p₁⁷p₃ − 175p₁p₃³ + 63p₁⁵p₅ + 315p₁²p₃p₅ − 189p₅² − 225p₁³p₇ + 225p₃p₇`.

   For centred `τ` (`Tr τ = 0`) this is **`25 p₃ p₇ = 21 p₅²`**. The even power sums drop out. The
   odd engine needed `p₁ = p₃ = p₅ = p₇ = 0` (4 conditions); E needs one relation among the
   same four numbers.
2. **Normal form [Proof].** A monic nonic `χ` is an E polynomial (cofactor of degree 3) iff

   > `χ(t) = σ(t)·E(t²) + r(t)`,  `σ` monic cubic, `E` monic cubic, `deg r ≤ 1`,

   and then `N = χ(t)·σ(−t)` is the crossing polynomial. Over ℚ, `σ, E, r` are rational whenever
   `χ` is. The map `(σ, E, r) ↦ χ` is dominant onto the (irreducible) E hypersurface [Computed,
   exact: Jacobian rank 8]. So **K is E-solvable iff K is the root field of some rational
   `σ(t)E(t²) + r(t)`**: an explicit 8-parameter rational family of nonics.
3. **Old frontier, odd engine and both controls are special cases.**
   - `σ = t³`, `r` constant gives the odd engine.
   - D0's S₉ control decomposes this way (checked).
   - So does the new integer control below.
4. **New control [Computed, exact].** `q_c = ∏_{a∈A}(x − a) + x + 1` with
   `A = {−10, −9, −8, −7, 1, 6, 8, 9, 10}`, i.e.
   `x⁹ − 288x⁷ + 42x⁶ + 30219x⁵ − 10290x⁴ − 1364812x³ + 826728x² + 22291201x − 21772799`.
   - It is irreducible and totally real.
   - Gal = S₉: it has Frobenius types (9), (4,5) and (1,8).
   - The crossing polynomial is integral: `N = q_c(t)·(−(t − 7)(t + 1)(t + 6))`, with
     `Y = −t³ + 993244219t² + 85t − 914457558` and
     `g(u) = u⁶ − 331u⁵ + 42603u⁴ − 2665993u³ + 81410297u²`.
5. **Search [Computed, exact].** Directions `τ` of the trace-zero part of `ℤ[β]`, in an LLL-reduced
   basis, with coefficients in `{−2, …, 2}⁸` (195,312 directions). The shift `h` is free over ℚ.
   - On `q₃`: **no hit**.
   - On `q_c`: exactly the planted solution, through the same code.

   This is a height-2 null on one field, nothing more. §5 says why the search cannot be expected
   to succeed.
6. **Correction to D0 §3.4 [Proof].** "P-points do not help E" is too strong. With `g` fixed
   rational in advance, `τ ∈ K ⊗ F` and `Y ∈ F[t]` give a valid construction. But this turns E into
   an all-P row with 3 conditions on the generator, which M1/G/J (1 condition each) dominate
   (§7).

## 1. The power-sum form

**Derivation.** Write `χ(t) = A(t²) + t·B(t²)`. D0's 4 × 4 determinant equals the Hankel
determinant `c₁c₃ − c₂²` of the expansion `A(u)/B(u) = c₀ + c₁/u + c₂/u² + …` at `u = ∞`:
- the identity is exact and symbolic in `e₁ … e₇`;
- it is the Padé condition that `A/B` agrees with a `(1, 1)` rational function to order `u⁻³`.

Since `χ(−t) = A − tB` and `χ(−t)/χ(t) = −exp(2S)` with `S = Σ_{k odd} p_k/(k·t^k)`, one has
`A/B = −t·tanh S`. So the `c_k` are polynomials in the odd `p_k` only:
- `c₀ = −p₁`;
- `c₁ = (p₁³ − p₃)/3`, and so on.

Substituting gives `H/4725`.

**Proof status.** The identity `4725·s_λ(e(p)) = H(p₁, p₃, p₅, p₇)` was checked as a polynomial
identity in `p₁ … p₇` (Newton's identities, `p₂, p₄, p₆` free): the difference expands to 0. Since
`p₁ … p₇` are algebraically independent in 9 variables, this is a proof.

**Consequences.**
- `H` is linear in `p₇`, with coefficient `225(p₃ − p₁³)`.
- In centred form, `25p₃p₇ − 21p₅²` is the determinant of `[[25p₃, 21p₅], [p₅, p₇]]`. So the
  locus in `ℙ(K₀)` (`K₀` = trace zero) contains both `{p₃ = p₅ = 0}` (the old frontier) and
  `{p₅ = p₇ = 0}` (new; a (5,7) complete intersection, `K = O(4)`, worse).
- **Pencil.** Through the Padé form, a solution has cofactor `ρ` whose odd part is
  `∝ t(t² − μ)`, `μ = c₂/c₁`.
  - `μ = ∞` (`c₁ = c₂ = 0`): exactly the shift orbit of `{p₁ = p₃ = p₅ = 0}`. There `ρ` is
    linear: if `χ_σ` has `e₁ = e₃ = e₅ = 0`, then `t·χ_σ(t)` has no `t⁵, t⁷, t⁹` terms.
  - `μ = 0` (`c₂ = c₃ = 0`): the other end.
  - `μ` is a weight-2 invariant, so scaling `τ` moves it by squares. A search over the pencil is
    the same search; it is not a reduction.
- **Abelian fixed points [Proof sketch].** The fixed-point necessary condition for a uniform
  (versal) formula, in the Reichstein–Youssin going-down form, is that every abelian
  `A ⊂ S₉` fixes a point of `X = {s_λ = 0} ⊂ ℙ⁸`.
  - If `A` is not transitive, its fixed set in `ℙ⁸` is a positive-dimensional linear space,
    which meets `X`.
  - If `A` is transitive, it is regular (`ℤ/9` or `(ℤ/3)²`). Every eigenvector has
    `p₁ = p₅ = p₇ = 0`, so it lies on `X`.

  So this test gives **no obstruction**. (The cited theorem is quoted from memory.)

## 2. Normal form `χ = σ(t)E(t²) + r(t)`

**Proof (⇒).** Let `χρ = N` with `N` in the support `{0,1,2,3,4,6,8,10,12}`, `deg ρ = 3`. Put
`σ(t) = ±ρ(−t)`, monic, and divide: `χ = σQ + R`, `deg R ≤ 2`. The odd polynomial

`χ(t)σ(−t) − χ(−t)σ(t) = σ(t)σ(−t)·(Q(t) − Q(−t)) + (R(t)σ(−t) − R(−t)σ(t))`

has degree ≤ 3, because `N` has no odd terms above `t³`.
- The first term has degree `6 + deg(odd part of Q)` if that odd part is nonzero, and the second
  has degree ≤ 5. So `Q` is even: `Q = E(t²)`.
- The `t⁵` coefficient of the second term is `−2·R₂`, so `R` is linear.

**(⇐).** Direct: `χ(t)σ(−t) = σ(t)σ(−t)E(t²) + r(t)σ(−t)`. The first term is even and the second has
degree 4, so its odd part has degree ≤ 3. ∎

**Remarks.**
- `σ` is the kernel line of the linear system, so it is rational when `χ` is.
- Dominance: the Jacobian of `(σ, E, r) ↦ (e₁ … e₉)` has rank 8 at a random point, and `s_λ` is
  irreducible in `ℚ[e₁, …, e₇]`. So the family is birational to the E hypersurface.

**In K.** `τ` is a solution iff there are a rational cubic `σ` and a rational linear `r` with
`−r(τ)/σ(τ) ∈ τ⁶ + span_ℚ(1, τ², τ⁴)`.

**Why the integer controls exist.** If `A = S ∪ (−S′) ∪ S′` with `|S| = 3` and `S′` a 3-set,
then `∏_{a∈A}(x − a) = σ(x)E(x²)` with `σ = ∏_{s∈S}(x − s)` and `E = ∏_{b∈S′}(u − b²)`.
Adding any linear `r` keeps the form. D0's warning that `∏(x − aᵢ) + c` is degenerate is the case
where `A` is symmetric up to 3 elements. `q_c` is built this way on purpose; `q₃` is not.

## 3. What E needs from a field

E closes T9Q iff every totally real nonic field K with group A₉, S₉, PSL(2,8) or PΓL(2,8) has a
rational generator `τ` with `H(Tr τ, Tr τ³, Tr τ⁵, Tr τ⁷) = 0`.

**Geometric non-degeneracy.** `τ²` must generate K, which is automatic for primitive groups and
irrational `τ`.

**Drawing it.** As in D0 §3.1:
- the Bézier `(t², Y(t))` and `poly_graph g`;
- `restrict` to a rational box isolating one crossing, then `inter_x` gives `τᵢ²`;
- then `√`, and `β = R(τ²)` with `R ∈ ℚ[x]` of degree ≤ 8.

**The variety.**
- `X_K = {τ ∈ ℙ(K) : H = 0}` is a degree-10 hypersurface in `ℙ⁸`, twisted by K.
- If its singularities are mild, `K_X = O(1)`: general type, by a margin of one.
- Rational points are not expected to be Zariski dense [Heuristic, Bombieri–Lang].
- Known subvarieties: the cone over `{p₁ = p₃ = p₅ = 0}` (CY base) and `{c₂ = c₃ = 0}`
  ((5,7) complete intersection, general type). Neither is known to have points.

## 4. The search

**Lattice.**
- Embed `9βᵏ − Tr βᵏ` (`k = 1 … 8`) in `ℝ⁹` and LLL-reduce. The rays of this lattice are exactly
  the trace-zero projections of `ℤ[β]`.
- Directions are `c ∈ {−2..2}⁸`, first nonzero coefficient positive.
- For each `τ`: `p₂ … p₇` exactly (160-digit embeddings, rounded); then
  `f_τ(h) = H(p(τ + h)) ∈ ℤ[h]` of degree 10, with leading coefficient `4725 · 608256`.

**Filter.**
- `f_τ` must have a root mod each of the 14 primes 13, 17, …, 73. These do not divide the
  leading coefficient, so a rational root survives.
- Survivors (about 0.2%, as for random polynomials) go to exact `FactorList`.

**Results.**

| field | directions | after mod filter | rational shift found |
|---|---|---|---|
| `q_c` (control) | 195,312 | 378 | `c = (1,0,…,0)`, `h = 0` (the planted `τ = 9β`; also `2×` it) |
| `q₃` | 195,312 | 364 | **none** |

The control's solution is the first reduced basis vector, at the same scale as `q₃`'s (roots in
`[−10, 10]`). Run time is about 6 s per 24k directions.

## 5. Why a search is not the way forward [Heuristic]

- Points of height ≤ B in `ℙ⁸` number about `B⁹`.
- `H` takes values of size about `B¹⁰` on them, and the shift adds one dimension of freedom.
- So the expected number of solutions grows at best like `B⁰`, and in practice it decays.
- The controls work only because they are built from structure (§2).

A search can confirm a structural family but cannot replace one. This is the same lesson as R3
and F1.

## 6. The exact remaining problem [Open]

**Versality question.** Is the rational family `σ(t)E(t²) + r(t)` (8 parameters) versal for the
totally real fields with groups A₉, S₉, PSL(2,8) and PΓL(2,8)? Equivalently: for each such K, does
K have a rational element `τ` with `−r(τ)/σ(τ) ∈ τ⁶ + ℚ⟨1, τ², τ⁴⟩` for some rational `σ`, `r`?

**What is known.**
- 8 parameters is at least `ed(S₉) ≥ 4`, so the count does not forbid it.
- The abelian fixed-point test passes (§1).
- There is no known point-producing structure: no ℚ-point of multiplicity 9 to project from, and
  no low-degree rational subvariety.

**What a "yes" would need.** A Tschirnhaus formula rational in the coefficients of K's polynomial,
or a field-by-field argument.

**What would kill E (scoped).** A field K for which `X_K(ℚ_p) = ∅` for some p (a local
obstruction), or a proof that the family is not versal. Neither was looked for here.

**Local solubility of `X_{q₃}` [Computed, exact].** A degree-10 form in 9 variables over `ℚ_p` need
not have a nontrivial zero, so this was a genuine kill test. It found nothing.
- `ℝ`: real points exist (§0.3 of D0).
- Every odd prime `p ≤ 97`, and `p = 271` (which divides `disc q₃`): there is a smooth
  `𝔽_p`-point of `F(c) = s_λ(Σ c_j βʲ)` on `ℤ[β]/p`. It lifts by Hensel.
- `p = 2`:
  - `F ≡ 0 mod 2` on all of `ℤ[β]/2`. Here `q₃ ≡ (x+1)³(x²+x+1)³`, and the 2-content of `F` is
    exactly 1.
  - `c = (−8, 22, −27, 10, 14, 38, 2, −40, −5)` has `v₂(F/2) = 13 > 2·v₂(∇(F/2)) = 12`, so
    Hensel gives a 2-adic zero.
- `p > 97`: expected from Lang–Weil once `X` is absolutely irreducible. That was not verified,
  and the large factor of `disc q₃` was not factored.

So no local obstruction is visible for `q₃`. The problem really is global.

## 7. P-valued dials (correction to D0 §3.4)

Fix `g ∈ ℚ[x]` (degree ≤ 6) in advance. Draw the graph, optionally moved by `scale_x`/`translate_x`
with P-values `a, b`.
- `τ ∈ K ⊗ F` and `Y ∈ F[t]` give a Bézier with P control points. The construction of §3 goes
  through: `β ∈ F[τ²]`.
- The rational unknowns are gone, so D0's objection does not apply.

**Count.**
- Dials over F: `Y` (4), the scale of `g` (1), and `a, b` (2), minus a joint scaling: rank ≤ 6.
- So `c_τ ≥ 3`. The locus `V_g ⊂ ℙ(K ⊗ F)` has codimension 3, with real points as soon as
  `g(t²)` oscillates, e.g. `g(u) = T₁₂(√u)`.
- Over ℚ̄ it is a cover of the rational 4-fold `{(σ, s)}` (§2 with `E` fixed by `g`).

**Comparison.** M1 (Bézier × Bézier), G and J leave 1 condition on the generator over F, with
hypersurface degrees about 111 and 180 (NOTES-general). So the F-version of E is dominated, unless
some special rational `g` makes `V_g` reducible with a low-degree component [Open; not looked
for].

## 8. Recommendation

- **E** stays open, with the remaining problem stated in §6. Do no more box searches. Local
  solubility on `q₃` passes (§6), so there is no cheap kill either.
- **D1 on `q₃`.** E is D1's boundary. Check first whether D1's condition also factors through a few
  power sums; that is the analogue of §1 and costs one symbolic run.
- **H** (two rational sextics, one rotated) is next as planned.

## 9. Reproduction (Wolfram)

```mathematica
(* §1 identity *)
ps = {p1,p2,p3,p4,p5,p6,p7}; e[0] = 1;
Do[e[k] = Expand[1/k Sum[(-1)^(i-1) e[k-i] ps[[i]], {i,1,k}]], {k,1,7}];
sl = Det[{{e[4],e[5],e[6],e[7]},{e[2],e[3],e[4],e[5]},{1,e[1],e[2],e[3]},{0,0,1,e[1]}}];
H = p1^10-15p1^7 p3-175p1 p3^3+63p1^5 p5+315p1^2 p3 p5-189p5^2-225p1^3 p7+225p3 p7;
Expand[4725 sl - H]   (* 0 *)

(* §2 dominance *)
chi = Expand[(t^3+s2 t^2+s1 t+s0)(t^6+f2 t^4+f1 t^2+f0) + r1 t + r0];
MatrixRank[D[CoefficientList[chi,t][[1;;9]], {{s2,s1,s0,f2,f1,f0,r1,r0}}] /. random]  (* 8 *)

(* §4 search: prep/run as in HANDOFF-alg-D1E.md; f_tau(h) built from *)
psh[k_] := Sum[Binomial[k,j] P[j] h^(k-j), {j,0,k}];
coefP = CoefficientList[Expand[H /. {p1->psh[1],p3->psh[3],p5->psh[5],p7->psh[7]}] /. {P[0]->9,P[1]->0}, h];
```
