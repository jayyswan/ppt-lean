# PLAN-jacobi-R3: the composition route

Read `PLAN-jacobi-00-overview.md` first. Research task: **no `.lean` edits**.
Log: `HANDOFF-jacobi-R3.md`. Deliverable: `NOTES-jacobi-R3.md` (repo root).

## Question

Can `am(u, c)` be written as a finite composition of operations already known to be
P-constructible, without any single curve having first-kind arc length? The available operations
(all proved in `Pptc`): `+ − × ÷`, `√`, real roots of degree ≤ 6 polynomials, `sin`, `cos`,
`arccos`, `2^x`, `log`; `ellipticF`, `ellipticE`, `ellipticPiInc` (for `n > 1`) forwards;
`ellipticEAm` (the inverse of `E`) at any modulus; the inverse arc length of **any** drawable
curve (Bézier, polynomial graph, sine, offset chains); crossings of drawable curves, which solve
equations like `sin x = a x + b`. Curve parameters may be computed from `u` itself.

## The derivative test (use it to kill candidates fast)

Suppose on an interval `am(u) = G(T(u))` with `T(u) = s_C⁻¹(L(u))`, with `G`, `L` smooth and
built from the operations above. Then `s_C(T) = L(F(G(T)))`. Drawable speeds are algebraic in
the point, `sin`/`cos` and `2^x` of things, and never contain `F`. Differentiating therefore
forces `L` to be affine, and so `s_C = α F∘G + β`, which is the single-curve route. Your
job is to make this precise and find where it **fails**:

* **Parameter dependence:** the curve `C_{p(u)}` depends on `u` through its parameters. Then
  `s_{p(u)}(T) = L(u)` and the test gains `∂s/∂p` terms. Complete integrals as functions of the
  modulus (`K(c)`, `E(c)`) live here.
* **Several inversions in sequence**, e.g. `am = G(T₂)`, `T₂ = s_{C₂}⁻¹(L₂(T₁, u))`,
  `T₁ = s_{C₁}⁻¹(L₁(u))`.
* **Mixed E/F at different moduli:** Landen and Gauss transformations, the imaginary-modulus
  and reciprocal-modulus transformations (e.g. for `k > 1`, `E(φ,k) = k E(β,1/k) − (k − 1/k)
  F(β,1/k)` with `k sin φ = sin β`), and Legendre's relation. Can an `E`-amplitude at one
  modulus be an `F`-amplitude at another after an algebraic change of angle? (Expect no:
  a holomorphic differential pulls back to a holomorphic one. Check that the argument is airtight
  when the map is only transcendental-constructible, not algebraic.)
* **Non-uniform constructions:** different `u` constructed in genuinely different ways. Say
  what, if anything, the test says here.

## Steps

1. Write the derivative test as a lemma with explicit hypotheses and a proof.
2. For each loophole above, either extend the test to exclude it or produce a candidate
   formula. Test every candidate numerically against `mpmath.ellipfun` at 3 moduli and
   5 arguments.
3. Record partial facts that could matter later, for instance for which `u` the amplitude is
   already known constructible: `u ∈ F(P)`; `u = r·K` for dyadic `r`, via halving formulas; the
   set is closed under addition by (F4) (task L2 proves this in Lean).
4. Notes: the lemma, the loophole table with verdicts, any candidates, and the remaining open
   loopholes, ranked by plausibility.

## Stop

Stop after step 4. Do not spend more than a third of your budget on literature.
