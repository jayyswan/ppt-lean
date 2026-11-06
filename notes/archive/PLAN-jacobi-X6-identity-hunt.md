# PLAN-jacobi-X6: computer hunt for a formula

Read `PLAN-jacobi-X0-overview.md` first. Log `HANDOFF-jacobi-X6.md`; deliverable
`NOTES-jacobi-X6.md`.

## The idea

Brute force. Build a large library of cheap-to-construct functions of `u`, and check numerically
whether `am(u)`, `sn(u)`, `cn(u)` or `dn(u)` is a simple combination of them. Most searches
like this find nothing. But an unexpected exact identity would be a breakthrough, and a clean
negative with a documented search space is still informative.

## Setup

* Fix a few moduli: `c ∈ {1/2, 1/3, (√2−1)², 0.7}`. `1/2` is the lemniscatic case and
  `(√2−1)²` is a singular modulus, where extra identities are most likely.
* **Library `ℒ(u)` of depth ≤ 2** (each entry must be genuinely P-constructible from `u` and `c`
  by the moves in the overview; say which move for each family):
  * depth 1: `u`, `√u`, `sin u`, `cos u`, `2^u`, `log u`, `arccos` of algebraic expressions;
    `F(u, c)`, `E(u, c)`, `F(u, c′)` and `E(u, c′)` for a few algebraic `c′(c)` (Landen,
    complementary, reciprocal); `EAm(u, c)` and `EAm(u, c′)`; `K(c)`, `E(c)` constants;
  * depth 2: the depth-1 functions composed with each other, with `F`, `E`, `EAm` at modulus
    `c` or a Landen modulus; moving-modulus integrals `E(φ₀, c·u)`, `F(φ₀, u)`; the arc length of
    `y = u·sin x` over `[0, π/2]`; the positive root of a small polynomial with coefficients in
    depth 1.
* **Targets**: `am(u)`, `sn(u)`, `cn(u)`, `dn(u)`, and `am(u) − u·π/(2K)` (the periodic part).

## Searches

1. **Integer-relation search (PSLQ, `mpmath.pslq` or `mpmath.identify`)** at fixed `u` (several
   values, e.g. `u = 1/2, 1, 3/2`) between the target and small subsets of `ℒ(u)` evaluated at
   100 digits. Any relation found at one `u` must be re-tested at 5 other `u` before it counts;
   relations that hold at a single `u` are coincidences.
2. **Function-level fits.** On a grid of `u`, fit the target as a linear combination of library
   functions and products of pairs; accept only fits whose off-grid residual falls with precision
   (as in `NOTES-jacobi-R3.md` §4.3).
3. **Composition search.** For each library `g`, test whether the target is `h(g(u))` for `h` in
   a small elementary set (`sin`, `arcsin`, `arccos`, `√`, rational of degree ≤ 2), by checking
   that the target is a well-defined function of `g` numerically (monotone dependence, smooth
   interpolation, then symbolic guess).
4. **Special arguments.** At `u = K/3`, `2K/5` etc., `sn` is algebraic over `c`; at those points
   check the degree and whether the degree-≤-6-roots engine covers them. These would be cheap
   partial results worth passing to Lean.

## Deliverable

Notes with the plain summary, the exact search space (so it can be extended later), every relation
found with its multi-`u` verification status, and a list of the special-argument partial results.
Put the scripts in `archived files/jacobi-scripts/X6-*.py` and make them rerunnable.
