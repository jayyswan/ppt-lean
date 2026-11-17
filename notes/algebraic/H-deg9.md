# H (degree 9): rational sextic graph × rational sextic graph rotated 90°

Stream H of `PLAN-degree9.md` (D0 row H; H1's "graph against rotated graph"), 2026-11-13. Research
only. Backend: Wolfram (wolfram MCP). Log: `HANDOFF-alg-H-deg9.md`. (Named `H-deg9` to avoid
clashing with the general-n notes `H1.md` … `H5.md`.)

**Verdict: dominated, do not pursue.**
- Over ℚ the fibre over each generator is a 3-fold of degree 266 in `ℙ⁵`, with no structure found.
- Over F the row leaves 3 conditions on the generator.
- Its low-degree special cases are dominated by E.

## 1. Formulation [Proof]

The curves are `y = P(x)` and `x = R(y)`, with `P, R ∈ ℚ[x]` of degree ≤ 6 (`poly_graph`, then
`rotate` by 90°). They cross at the roots of `R(P(x)) − x`, of degree 36.

A generator `τ ∈ K` works iff, with `σ = P(τ)`, one has `τ = R(σ)`. That is:

> `σ ∈ ℚ[τ]_{≤6}` and `τ ∈ ℚ[σ]_{≤6}`: a pair of generators, each a polynomial of degree ≤ 6 in
> the other.

Generically each is a polynomial of degree 8 in the other. So this is 2 conditions on the pair.

**Recovery.** `inter_x` gives `τ` directly (the crossing's x-coordinate), after `restrict` to a
rational box isolating it; then `β ∈ ℚ[τ]`.

**Capacity.** Real capacity 36, attained by `T₆ ∘ T₆` (D0).

## 2. Over ℚ: the fibre over a generator [Proof sketch]

Fix `τ`. The admissible `σ` form

`Φ_τ = {σ ∈ ℚ[τ]_{≤6} / affine : rank [1, σ, …, σ⁶, τ] ≤ 7}`, a subset of `ℙ⁵`.

- The matrix is 9 × 8: rows are the conjugates, columns have degrees
  `(0, 1, 2, 3, 4, 5, 6, 0)` in the coefficients of `P`.
- The rank-≤ 7 locus has expected codimension 2, so `dim Φ_τ = 3`. This matches D0's measured
  fibre dimension 3.
- By Thom–Porteous it has degree `h₂(0,1,…,6,0) = (21² + 91)/2 = 266`. Hilbert–Burch gives the
  same number from the eight degree-21 maximal minors.

A 3-fold of degree 266 in `ℙ⁵`, twisted by K, is far from anything Lemma A or a rational-curve
argument can use. The total space `{(τ, σ)}` is 10-dimensional, but every fibre is of this kind.

**Special cases are dominated by E.**
- `P` cubic: the fibre over each `τ` is finite, the same Porteous count in `ℙ²` (266 points). Compare
  E's finite fibre of degree 10.
- `P` quadratic: after a shift `σ = τ²`, the condition is `τ ∈ ℚ[τ²]_{≤6}`. That is 2 conditions
  on `τ`, i.e. 8 of the vectors `1, τ, τ², τ⁴, …, τ¹²` dependent. E asks for 9 of the 10 vectors
  `1, τ, τ², τ³, τ⁴, …, τ¹²` to be dependent: 1 condition. E contains this case and dominates it.
- `P = R` (a sextic against its own reflection) needs `P(P(τ)) = τ` with `P(τ) ∈ K`: 9 equations
  on 7 unknowns. Worse.

## 3. Over F [Computed, numeric rank]

- **Dials.** Fix `P, R` rational. The P-affine moves `scale`/`translate` on both graphs give 8
  dials, of which 7 are effective after normalisation.
- **Rank.** The root-Jacobian rank (120 digits) is **6**, so **`c_τ = 3`**.
- D1 over F (`D1.md` §2) has `c_τ = 1` with real capacity 18, so it dominates H over F.
- Check: with every coefficient of `P, R` free, the rank is 9, reproducing D0's row H.

## 4. Consequence for the order

Stage 1 of PLAN-degree9, as D0 ranked it (E, D1, H), is now done. None of the three closes T9Q.

**What survives.**
- E's versality question (`D1E.md` §6): is the 8-parameter family `σ(t)E(t²) + r(t)` versal for
  totally real A₉/S₉ nonics? It is the cleanest open statement this stage produced.
- D1 over F: a single-condition F-row with a free rational choice of `g`. Its hypersurface degree
  has not been measured.
- D3 (offset towers with a spare parameter) is untouched and is the plan's other step-2 stream.
