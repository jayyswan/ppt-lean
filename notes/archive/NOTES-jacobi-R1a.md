# NOTES-jacobi-R1a: arc lengths of ellipse-based offset/affine chains

Status: COMPLETE. Verdict: useful negative (no breakthrough). No `.lean` edits. Scripts under
`archived files/jacobi-scripts/` with `R1a-` prefix.

**One-paragraph summary.** The overview's chain formula (F3) is confirmed for depth 3 by exact
Taylor-jet computation but must be corrected by `sign(S_k)` once the running factor crosses zero.
With that formula, the ellipse-chain arc-length differential is `[sqrt(q_n) − Σ c_k sqrt(q_n)/q_k^{3/2}] dt`.
The leading term is a second-kind (E) form on the mapped ellipse, and every correction is
non-holomorphic: an order-`3/2` pole at the complex zeros of `q_k`, or (when `q_k ∝ q_n`) a
third-kind `1/q_n` with nonzero residues. By the holomorphic-pullback property of first-kind
forms, no chain in this class has `ds ∝ dφ/Δ`. The Landen "same curve, different phase"
loophole and the sign-flip loophole are both closed by the parameter-free pole test; only
parameter-dependent constructions (R3) remain.

Scope: only curves from an ellipse/circle by finite chains of `translate`, `scale_x`,
`scale_y`, `rotate`, `offset` (any constructible `A ∈ GL₂` reachable via scaling+rotation).
Other bases belong to R1b/R1c.

## Step 1 — Verify the depth-3 chain formula (F3)

**Scripts:** `R1a-02-chain-symbolic.py` (sympy, exact), `R1a-03-chain-jet.py` (mpmath jets, 30 dps).
No nested `mp.diff` was used.

**One-step identity (exact, sympy).** For a curve `g` with velocity `v = g'`, `Q = |v|²`,
`K = det(v, v')`, matching `Defs.unitNormal = J g'/|g'|` (`J(x,y)=(-y,x)`):

    (d/dt) unitNormal(g) = -(K / Q^{3/2}) · v ,      and hence
    (d/dt) (g + d·unitNormal(g)) = (1 - d·K/Q^{3/2}) · v .

The offset tangent is always parallel to the original tangent. Verified symbolically
(`sp.simplify` returned the zero vector), generic `v`.

**Depth-3 chain (jet verification, 30 dps).** Build the chain
`A₃∘off_{d₂}∘A₂∘off_{d₁}∘A₁∘off_{d₀}` acting on the ellipse, using truncated Taylor jets
(so all derivatives up to order 14 are carried exactly; no nested finite differences).
Compare the true chain velocity at `t` with the prediction. With cumulative linear parts
`A_(k) = A_k⋯A_1` (`A_(0)=I`), `q_k = |A_(k) v|²`, `detA_(k)`:

    S_0 = 1 ,   S_{k+1} = S_k  −  d_k · sign(S_k) · detA_(k) · K / q_k^{3/2} ,
    final velocity = S_n · A_(n) v ,   speed = |S_n| · sqrt(q_n) .            (F3-correct)

Results (b = 1.7, random rational 2×2 maps, `t=1`):

| case | err (sign-correct recurrence) | err (plain F3 sum) |
|---|---|---|
| generic, S stays > 0 | 1.1e-30 | 1.1e-30 |
| `d₀=1.5` forces S₁ < 0 | 2.4e-30 | 1.80 |

**Conclusion.** The overview's (F3) plain sum is only the `sign(S_k) ≡ +1` branch. As soon as the
running factor `S_k` crosses zero (a cusp of the current offset curve, where speed → 0), every later
correction flips sign. The correct recurrence is the `sign(S_k)` version above.
Since `speed` in `Defs.lean` is `|S_n| sqrt(q_n)`, on each interval between consecutive cusps the
arc-length differential is a *fixed-sign* combination of the terms below; across a cusp the
relative signs of the corrections change. (This is the "past a cusp" loophole of step 4.)

## Step 2 — Base velocity, Q_k, phases

**Script:** `R1a-04-qk.py` (sympy exact + mpmath 30 dps).

Base ellipse `(cos t, b sin t)`, so `v = (−sin t, b cos t)` and `K = det(v,v′) = b` (constant).
For a linear map `A = [[p,q],[r,s]]`:

    q_A(t) = |A v|² = α + β cos 2t + γ sin 2t ,
    α = (|col₁|² + b²|col₂|²)/2 ,  β = (b²|col₂|² − |col₁|²)/2 ,  γ = −b (col₁·col₂) ,
    |col₁|² = p²+r² ,  |col₂|² = q²+s² ,  col₁·col₂ = pq+rs .

Equivalently, with `ρ = √(β²+γ²)` and `ψ = atan2(γ,β)`,

    q_A = α + ρ cos(2t − ψ) = μ (1 − κ² sin²(t − ψ/2)) ,
    μ = α + ρ ,   κ² = 2ρ/(α+ρ) = 2ρ/μ .                                (phase form)

All three identities verified **symbolically** (sympy returned `True`) and to 30 dps on random
maps. Since `q_A(t) > 0` for all real `t` (an ellipse's speed), `α > ρ`, hence `0 < κ² < 1`.

**Cumulative stages.** With `A_(k) = A_k⋯A_1` (`A_(0)=I`), each `q_k = |A_(k) v|²` has its own
`(α_k, β_k, γ_k, κ_k, ψ_k)`. Two facts used below:

* `A_(k)` a **similarity** (`c·(rotation)`) ⟹ `q_k = c² q_0`: all `q_k` proportional.
* `q_j`, `q_k` **proportional** with a constant factor ⟺ `A_(k) A_(j)⁻¹` is a similarity on the
  plane spanned by the ellipse's velocities. So "same elliptic curve" (equal `κ`) is in general
  weaker than "proportional"; the generic chain has pairwise-non-proportional `q_k`.

Weierstrass variable `z = tan t`: `q_k = N_k(z)/(1+z²)` with
`N_k(z) = (α_k+β_k) + 2γ_k z + (α_k−β_k) z²`, a positive-definite quadratic.

## Step 3 — Term-by-term decomposition on elliptic curves

**Script:** `R1a-05-reductions-poles.py` (sympy exact + mpmath 30 dps), `R1a-06-special-cases.py`.

By (F3-correct), `ds_n/dt = speed = |S_n|·sqrt(q_n)`, and
`S_n = 1 − Σ_{k=0}^{n-1} d_k·sign(S_k)·detA_(k)·K/q_k^{3/2}`. On an interval where all the
`sign(S_k)` and `sign(S_n)` are constant, this expands to

    ds_n = [ ± sqrt(q_n)  ∓  Σ_{k=0}^{n-1} c_k · sqrt(q_n)/q_k^{3/2} ] dt ,
    c_k = d_k · sign(S_n) · sign(S_k) · detA_(k) · K  > 0 or < 0, constant on the interval.

Only the *signs* of the `c_k` can change from interval to interval (through `sign(S_n)` and
`sign(S_k)`); the pole structure used below does not. There are three building blocks.

**(B1) Leading term `sqrt(q_n) dt` — second kind.** With the phase form
`q_n = μ_n (1 − κ_n² sin²(t−ψ_n/2))`,

    ∫₀ᵀ sqrt(q_n) dt = √μ_n · E(T − ψ_n/2, κ_n²) ,      E = incomplete elliptic integral, 2nd kind.

Numeric check (30 dps): for `b=1.7`, `∫₀^T sqrt(q_0) = b·E(T, 1−1/b²)` to the last digit (`R1a-05`).
So the leading term carries a **nonzero second-kind class** unless `q_n` is constant (then it is
elementary, `const·T`).

**(B2) `1/q_k dt` — elementary / third kind.** For `q_k = a_k + b_k cos 2t`,

    ∫ dt/q_k = (1/√(a_k²−b_k²)) · arctan( √((a_k−b_k)/(a_k+b_k)) · tan t ) .

Verified **symbolically** (`R1a-05`). This is the correction shape of every **similarity** chain
(`q_k = c_k² q_0`): there `sqrt(q_n)/q_k^{3/2} = √λ_n/(λ_k^{3/2} q_0)`, i.e. `1/q_0`.

**(B3) Mixed term `sqrt(q_n)/q_k^{3/2} dt` — not holomorphic.** `q_k` is a positive-definite
quadratic in `(cos 2t, sin 2t)`, so its two zeros `t₀` are simple and non-real. Near `t₀`,
`q_k ∼ q_k′(t₀)(t−t₀)`, hence

    sqrt(q_n)/q_k^{3/2} ∼ C · (t−t₀)^{−3/2}  dt ,   C = √q_n(t₀)/q_k′(t₀)^{3/2} ≠ 0  generically.

In the algebraic local coordinate `s` with `t−t₀ = α s²` this is `∝ ds/s²`: a **double pole with
residue 0**, i.e. a second-kind differential. The one exception is `q_k ∝ q_n` (so `q_n(t₀)=0`
too): then `sqrt(q_n)/q_k^{3/2} = λ^{−3/2}·(1/q_n)`, which has a **simple pole with nonzero
residue** `1/q_n′(t₀)` — a third-kind, not first-kind, form. In both cases the correction is
non-holomorphic. Numeric check (`R1a-05`, `R1a-06`): `|f(t₀+ε)|·ε^{3/2}` is constant (`0.169`,
resp. `0.177`) for `ε = 10⁻²…10⁻⁴`, whereas a first-kind density `1/√q` is bounded there.

When `q_n` and `q_k` share a phase (`γ_n = γ_k = 0`, "all phases equal" case), the mixed term can be
reduced explicitly with the same integration-by-parts trick:

    ∫ dt/q_k^{3/2} = ( ∫ sqrt(q_k) dt − b_k·sin 2t/√q_k ) / (a_k² − b_k²) ,
    ∫ sqrt(q_n)/q_k^{3/2} dt = [ ∫ sqrt(q_n q_k) dt − ... ] / (a_k² − b_k²) ,

the first identity verified **symbolically** (`R1a-05`). The second integrand `sqrt(q_n q_k)` is a
square root of a *quadratic in `cos 2t`*, i.e. an elliptic (second-kind) object on the quartic curve
`y² = (1−C²)(a_n+b_nC)(a_k+b_kC)`, `C = cos 2t`. So even the shared-phase case is second kind + an
algebraic boundary term, never the holomorphic first-kind form.

## Step 4 — Verdict table over the cases

Let a **first-kind target** mean `ds = α dφ/Δ(φ,c)` with `φ` an algebraic function of
`(cos T, sin T)` for some constructible parameter `T`. A first-kind form is *holomorphic*; its
pullback under an algebraic map is holomorphic. Since first-kind is the only thing the inverse
constructor `arc_of_length` can invert to reach `F`, this is exactly the target of the
single-curve route.

| case | integrand `ds/dt` | class decomposition | can it be `α/Δ`? |
|---|---|---|---|
| generic (pairwise non-proportional `q_k`) | `sqrt(q_n) − Σ c_k sqrt(q_n)/q_k^{3/2}` | 2nd kind on `E_n` + corrections with poles at the zeros of each `q_k` | **No.** `sqrt(q_n)` is finite at finite `t₀`; each correction with `q_k ∉ ℝq_n` has a pole at zeros of its own `q_k` (distinct sets), and if `q_k ∝ q_n` the correction is `∝1/q_n`, a third-kind form (simple pole, nonzero residue). Neither can be cancelled by the holomorphic leading term. |
| similarity chain (`q_k ∝ q_0`) | `s_n[ sqrt(q_0) − D/q_0 ]`, `D = K Σ d_k sign(S_k)/c_k` | 2nd kind `E_0` (`s_n ≠ 0`) + elementary arctan | **No.** Nonzero `E`-coefficient survives; elementary part cannot cancel it. |
| all phases equal (`γ_k=0`), `κ_k` differ | `sqrt(q_n) − Σ c_k sqrt(q_n)/q_k^{3/2}` | 2nd kind + third/second kind | **No.** zeros of `q_k` are `t₀(k)=½ arccos(−a_k/b_k)`; equal only if `a_k/b_k` equal (proportional). |
| same elliptic curve (`κ_n=κ_k`), different phases (`ψ_n≠ψ_k`) — the Landen loophole | leading on the common `E` + `sqrt(q_n)/q_k^{3/2}` with shifted angles | 2nd kind (common `E`) + the order-`3/2` pole of (B3) | **No.** The pole is phase-independent (`R1a-06`); Landen/addition is an identity among `E`, `F` and shifted `dn`, it cannot turn a form with a pole into a holomorphic one. |
| `Q_n` constant (circular base `b=1` + conformal final map) | `const − Σ c_k / q_k^{3/2}` | elementary + 2nd kind via (B3) reduction | **No.** Verified `q_0,q_2` constant, `q_1` non-constant (`R1a-06`). |
| sign flips (interval where `S_k<0`; `d_k` large) | same terms, all `c_k` for later stages sign-reversed | pole structure identical; leading coefficient `|S_n| ≠ 0` | **No.** |
| `detA_(k)=0` (singular map) | collapses the curve to a segment/point | elementary | **No** |

## Step 5 — Verdict and assumptions

**Verdict: no breakthrough; useful negative.** No finite chain of `translate`, `translate`-free
`scale_x/scale_y`, `rotate` (i.e. any constructible `A ∈ GL₂`) and `offset` applied to an
ellipse/circle has an arc-length differential proportional to a first-kind form
`dφ/Δ(φ,c)`. Hence no curve in this class realises `s_C(T) = α F(φ(T),c) + β` with `c ≠ 0` by the
single-curve route, for any `T` algebraic in `(cos T, sin T)`.

**What is genuinely new here.** (i) The overview's chain formula (F3) is verified for depth 3 by
exact Taylor-jet computation, and is corrected: once the running factor `S_k` has crossed zero the
sign of every later correction flips, `S_{k+1} = S_k − d_k·sign(S_k)·detA_(k)·K/q_k^{3/2}`. The
plain sum is only the `S_k>0` branch. (ii) The obstruction is sharpened from "different cohomology
classes" to a **parameter-free pole test**: every non-leading correction `sqrt(q_n)/q_k^{3/2}`
is non-holomorphic at the (complex) zeros of `q_k` (order-`3/2` pole, or a third-kind `1/q_n`
when `q_k ∝ q_n`), while the leading term and every first-kind form are holomorphic there.
This does not depend on choosing the elliptic curves to coincide, so
the Landen / "same curve, different phase" loophole is closed, not merely argued away.

**Assumptions the verdict uses.**
1. *Fixed chain*: the curve and its parametrisation are chosen before the length is requested, so
   `A_k`, `d_k`, `b` are constants (constructible but independent of the length variable). A
   curve/parameter that depends on `u` is the composition loophole and is owned by R3.
2. The base is a genuine ellipse/circle; `q_k > 0` on the real axis and its zeros are simple and
   non-real (true for every non-degenerate `A_(k)` and `b>0`).
3. "`= αF+β`" is read as an identity of analytic functions, so complex poles off the real axis are
   genuine obstructions (analytic continuation). This also excludes an algebraic reparametrisation,
   since pullback of a holomorphic form stays holomorphic.
4. At least one correction has a nonzero coefficient; if all corrections vanish the chain is just a
   mapped ellipse and the length is `E` (second kind), still not `F`.

**Loopholes this does *not* cover (stated, not claimed).**
* Parameter-dependent constructions (`A_k` or `d_k` a function of `u`): R3's L1, the top open
  candidate.
* A base curve outside this scope (polynomial/`power_law`/`sine`/`exp_two`): R1b/R1c.
* Anything needing a third-kind inverse (`ellipticPiInc`) or a new constructor: no constructor
  inverts it; R2's `Serret` family is the known minimal extension.
* Degenerate/singular chains produce elementary lengths, so they are excluded but not interesting.
No impossibility of `PConstructible (jacobiAm c u)` is claimed; only that this class of curves is
closed to the single-curve route.

## References / scripts

* `R1a-02-chain-symbolic.py` — sympy proof of the one-step offset identity (exact).
* `R1a-03-chain-jet.py` — truncated-Taylor (jet) verification of the depth-3 chain, 30 dps,
  including the `sign(S_k)` correction.
* `R1a-04-qk.py` — structure/phase form of `q_k`, exact + 30 dps.
* `R1a-05-reductions-poles.py` — reductions (B1)–(B3) and the pole-order test.
* `R1a-06-special-cases.py` — same-curve-different-phase and `Q_n`-constant cases.
* Context: `PLAN-jacobi-00-overview.md` (F3), `Defs.lean` (`speed`, `unitNormal`, `offsetParam`),
  `NOTES-jacobi-R2.md` §B.3 (offsets, abelian-decomposition uniqueness),
  `NOTES-jacobi-R3.md` §3 (loophole table L1–L11).
