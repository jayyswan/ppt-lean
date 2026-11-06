# L: named problems for the spiral classes and the box families

Stream L of `pptc/PLAN-spiral.md`. Labels: [Wolfram] checked in Wolfram Language (30-50 digit roots);
[Lit-memory] standard textbook fact that this session's searches did not confirm (searches returned abstracts or
nothing; OEIS blocks fetching; Wolfram|Alpha constant lookups returned nothing); [Heuristic]; [Open].
No Lean touched, no Python used.

## Findings summary

1. **Only the box families have real named matches, and each is a tangent condition of the spiral itself.**
   `x' = cos t - t sin t = 0` is `t tan t = 1`; `y' = sin t + t cos t = 0` is `tan t = -t` [Wolfram]. These are the
   vertical and horizontal tangents of `r = theta` (also the extremum of `x sin x` for the second).
2. **`x tan x = 1`, root 0.86033358901937976248389342413766233341188...** is the plane-slab Robin/Biot eigenvalue
   equation `zeta tan zeta = Bi` at `Bi = 1` (first root; Incropera Table 5.1 lists 0.8603 at Bi = 1.0 [Lit-memory]).
   Equivalent forms: `cot x = x`; rod fixed at one end with a tip mass equal to the rod mass, `kL tan kL = m_rod/M`
   [Wolfram derivation below; a search hit (Aktas et al. 2019, Uludag) confirms the fixed-rod-tip-mass problem
   but its equation was not visible]. A Michigan Tech notes file gives 1.2558 for "Bi = 1"; that is a different
   equation or Bi convention, not a conflict.
3. **`tan x = -x`, root 2.02875783811043422357697112473471437610838...** is the rod `X(0)=0, X'(1)+hX(1)=0` with `h=1`
   (`tan k = -k/h`, [Wolfram derivation]; textbook attribution [Lit-memory], search could not confirm), the extremum of
   `x sin x`, and the horizontal tangent of the spiral.
4. **No named match** for: generic conic, aligned conic (parabola `y = k x^2`, `y^2 = 4x`), off-centre hyperbola, power
   laws with b not in {0,-1,1}, odd/even graphs, loop and cusp Beziers, focal cubic Bezier, the `exp_two` and `sine`
   families (including 0.75986...), general `tan y + y = k`, `(x+beta) tan x = 1` with beta != 0, and the spiral
   offset-inversion equation. This rests on a few searches (MathWorld Archimedean spiral page: no tangent or
   intersection content; scroll-compressor and spiral-intersection queries) so it is [Heuristic], not proof.
5. **Constants.** No computed root was found as a named constant. OEIS was not fetchable; a search for 0.8603335890193797
   returned only Kimberling's "least x with polynomial = tan x" sequences (A2003xx-A2006xx), none matching. [Open]: check
   `oeis.org` by hand for digits `8603335890193797`, `2028757838110434`, `2215221443126364`, `1309136178207162`.
6. **Parabola class** `sin x = k x cos^2 x` (`x = tan x sec x` at k = 1): no source; it is `sec'(x) = k x`, the critical
   points of `sec x - k x^2/2`. A search for "x = tan x sec x" found nothing relevant. [Heuristic: unnamed.]

## Table: family -> named problem -> substitution -> verified root -> route

Routes use F2's window law (Arch: Warped Down ▲ edge window `[pi/6, 2pi/3]`; Arch: Warped ▲ edge `[pi/2, pi]`).
They are derived here from F2's formulas, not measured: [Heuristic] pending a PowerPoint check.

| family | named problem | substitution | root [Wolfram, 50-digit working precision] | route |
|---|---|---|---|---|
| box `(x+beta) tan x = 1`, beta = 0 (T6, b = 1) | slab `zeta tan zeta = Bi`, Bi = 1; spiral vertical tangent; tip-mass rod | `X = cos kx`, `X'(1) = -Bi X(1)` gives `k sin k = Bi cos k`; `d/dt(t cos t) = 0` | 0.860333589019379762483893424137662333 | xmax of `t cos t` on Down ▲ window `[pi/6, 2pi/3]`; NMaximize there returns t = 0.8603335890193792, value 0.561096338191045 = `t^2/sqrt(1+t^2)`, so it is the global max on the window |
| box `tan y + y = k`, `y = pi/2 - x`, `beta = k - pi/2` | k = pi gives `tan x = -x`; other k: none | stationary point of `t cos(t - beta)` | k = 3: y = 1.08874792349856086933952529998718230, `t^2/sqrt(1+t^2)` = 1.69345946020889479055425186098 | box in direction beta; window per F2 section 6 |
| box `tan x = -x` | rod with `h = 1`; extremum of `x sin x`; spiral horizontal tangent | `k cos k + h sin k = 0`; `d/dt(t sin t) = 0` | 2.02875783811043422357697112473471437610838 | ymax of `t sin t` on Up ▲ window `[pi/2, pi]` or Down ▲ `[pi/6, 2pi/3]`; NMaximize gives 1.81970574115965 at t = 2.0287578381 on both |
| box `x tan x = b`, b rational (T6) | slab Bi = b; tip-mass rod, m_rod/M = b | same | b = 3: 1.1924588293364287 | power spiral only (M.md T6), not Archimedean |
| I1/I2 parabola `y = k x^2`, k = 1 | `x = tan x sec x`: none | `u = sin x`: `k x (1-u^2) = u` | 2.2152214431263645714504004781459598 | spiral meets parabola, `restrict` to Up ▲ window `[pi/2, pi]`; `Reduce` of `sin t = t cos^2 t` on `[pi/6, pi]` gives only t = 2.2152214431263646, so one crossing |
| I3 exp `th sin th = 2^(th cos th)` | none | normal form of I3 | 1.3091361782071628805908899419236339458 | any window containing 1.309 and not 3.104, e.g. Down ▲ `[pi/6, 2pi/3]` (2pi/3 = 2.094 < 3.104) |
| I3 sine `th sin th = sin(th cos th)` | none | trivial roots `m pi` excluded by window | 0.75986237989815059970609525812795898651 | Down ▲ window, no `m pi` inside |
| I1 generic/aligned conics, off-centre hyperbola | none | I1 master equation | I1 tables | I1 |
| offset-inversion `1/2(sinh u cosh u + u) - d(sinh u + gd u) = x` | none (d = 0 is the parabola arc-length inverse, already R) | `theta = sinh u`, `psi = theta + arctan theta` | stream O | stream O |

Verification (Wolfram, one call each):
- end-mass rod `E A X'(L) = M w^2 X(L)` with `X = sin kx` gives `m cos k = k M sin k`, i.e. `k tan k = m/M`;
- convective rod gives `k cos k + h sin k`; slab gives `Bi cos k - k sin k`; spiral derivatives as above;
- the box roots equal the named-equation roots to under 1e-39 (vertical-tangent root vs `x tan x = 1`; extremum of
  `x sin x` vs `tan x = -x`); `x tan x = 1` and `cot x = x` agree to 1e-49; `sin x = x cos^2 x` and `sec x tan x = x` agree to 1e-49.

## Families with no named match, and the plan's engineering candidates

All of finding 4 above. Candidate by candidate:
- Cam and gear profiles: Archimedean cam pressure angle is algebraic (`tan phi = h/(beta r)`) [Heuristic]; the gear
  involute function is the catenary row of `R5-named.md`, not a spiral one.
- Spiral antenna: active-region condition `2 pi r = lambda` is `theta = rho` (E).
- Theodorus spiral, spiral springs, record grooves: arc-length or angle-sum quantities, no intersection equation of
  these shapes found [Heuristic].
- Scroll compressors: Archimedean wraps are studied (a search found a 1997 comparison with involute wraps and a Russian
  two-part paper deriving the conjugate generator by the envelope method); the offset-wrap-meets-circle problem would
  sit in the off-centre-circle (R) or generic-conic (?) stratum. Equations not visible in abstracts. [Open]
- Kepler and Dottie are R (I1); Fresnel/Euler spiral collapses (R5 row 5).

## Other things noticed

- Both named box roots come from one mechanism, the spiral's own tangent. The "named" content is classical calculus; the
  project's contribution is only that the bounding box reads it out.
- Only Bi = 1 is hit by Archimedean boxes. Other rational Bi needs power spirals (M.md T6).
- `tan x = -x` is Bi = -1 in the slab convention; no standard table was found for it. [Open]
- Web access was intermittent (a usage limit interrupted the first pass); the OEIS and Incropera-table checks remain
  [Lit-memory]/[Open].
