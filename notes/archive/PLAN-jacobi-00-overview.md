# PLAN-jacobi: shared context (read this first, every task)

Goal of the programme: decide whether the Jacobi amplitude `jacobiAm c u` (and so `sn`, `cn`,
`dn`) is P-constructible for P-constructible `c < 1` and `u`, and bank whatever partial results
come out along the way. Everything already proved is in `pptc/Pptc/Jacobi.lean`. The four
functions stand or fall together (`jacobiAm_Pconstructible_iff_sn/cn/dn`), so the one question
is the amplitude.

Task files (each one is **one agent run** with **one deliverable**):

| file | kind | deliverable | depends on |
|---|---|---|---|
| `PLAN-jacobi-R1a-ellipse-chains.md` | math research | `NOTES-jacobi-R1a.md` | none |
| `PLAN-jacobi-R1b-polynomial-chains.md` | math research | `NOTES-jacobi-R1b.md` | none |
| `PLAN-jacobi-R1c-transcendental-chains.md` | math research | `NOTES-jacobi-R1c.md` | none |
| `PLAN-jacobi-R2-serret-and-extensions.md` | math + literature | `NOTES-jacobi-R2.md` | none |
| `PLAN-jacobi-R3-compositions.md` | math research | `NOTES-jacobi-R3.md` | none |
| `PLAN-jacobi-L1-derivatives.md` | Lean | new file `Pptc/JacobiAddition.lean`, phase 1 | none |
| `PLAN-jacobi-L2-addition.md` | Lean | same file, phase 2 | L1 |
| `PLAN-jacobi-L3-local-to-global.md` | Lean | same file, phase 3 | L2 |

The R tasks are independent and can all run at once, and in parallel with L1.
L1 → L2 → L3 must run in that order.

Research tasks: **do not edit any `.lean` file.** Write only your NOTES file and your HANDOFF log.
Numerics: Python 3.12 with `mpmath`, `sympy`, `numpy`, `scipy` is at
`C:\Users\jason\AppData\Local\Programs\Python\Python312\python.exe` (not on the bash PATH).
Put scripts in `archived files/jacobi-scripts/` so they survive, and cite them from the notes.
Every identity you state in the notes must be checked numerically to ≥ 15 digits or proved
symbolically, and must say which.

Every task keeps a progress log `HANDOFF-jacobi-<task-id>.md` at the repo root
(`C:\dev\Powerpoint\lean`). Create it first, and append one line after every step.

## 1. Why the amplitude is hard (the current understanding)

The operations that produce numbers: field arithmetic; coordinates of a unique crossing of two
drawn curves; `arc_length` (forward integral between constructible endpoints); `arc_of_length`
followed by the abutting-arcs trick (`ellipticEAm_Pconstructible_of_mem_Icc`). The last one is
the only way to **invert** a transcendental function, and it inverts exactly one thing: the
arc-length function `s_C` of a drawable curve `C`. Drawn curves are fixed sets. Their equations
contain `sin`, `2^x` and algebraic operations but never an integral. So integrals only ever enter
at single constructible inputs.

* `E` **is** an arc length (of the ellipse), so its amplitude `ellipticEAm` is constructible
  (proved).
* `F` is reached forwards only (`ellipticF_Pconstructible`), as Bézier arc length **minus** a
  multiple of `E` **minus** an algebraic boundary term. `arc_of_length` inverts `s`, but not
  `s − B`.

So there are two conceivable routes to the amplitude:

1. **Single-curve route.** Find a drawable curve `C` and an algebraic (or otherwise
   constructibly invertible) reparametrisation such that `s_C(T) = α·F(φ(T), c) + β` **exactly**:
   no `E` part and no boundary term. Equivalently, the arc-length differential `ds` is a constant
   multiple of the holomorphic differential `ω = dφ/Δ(φ)` on the relevant elliptic curve.
2. **Composition route.** Express `am(u)` through several inversions and forward integrals,
   possibly with curve parameters computed from `u`.

## 2. Verified facts you may rely on

These were checked numerically to 30 digits
(`archived files/jacobi-scripts/00-overview-checks.py`).

**(F1) The lemniscate is rational.** `x = t(1+t²)/(1+t⁴)`, `y = t(1−t²)/(1+t⁴)` traces
`(x²+y²)² = x² − y²`, with speed² `= 2/(1+t⁴)`. Its arc length is **exactly** a first-kind
integral (modulus² `1/2`). The paragraph "Why the first kind resists" at the end of
`Jacobi.lean` is therefore wrong where it says that curves with first-kind arc length "are not
rationally parametrized". The real obstruction is not rationality but membership in the
drawable class. It is not a proof either way.

**(F2) Cubic graph.** For `y = x³`,
`∫₀ˣ √(1+9t⁴) dt = (1/3)·x√(1+9x⁴) + (2/3)·∫₀ˣ dt/√(1+9t⁴)`.
The arc length is a pure first-kind integral **plus** a boundary term. Geometrically,
`x√(1+9x⁴)` is the length of the tangent segment from `(x, x³)` to the y-axis. This is the
cleanest instance of the "s − B" obstruction.

**(F3) Offset then linear map.** For a curve with velocity `v(t)`, offset by `d` (normal
`(−v_y, v_x)/|v|`, as in `Defs.unitNormal`), then a linear map `A`:
`speed = √(Q_A(v)) · |1 − d·(v × v′)/|v|³|`, where `Q_A(v) = |A v|²` and
`v × v′ = v_x v′_y − v_y v′_x`.
Iterating (derived by hand, **not yet checked numerically**: R1a must check it) gives, for a
chain `A_n ∘ off_{d_{n-1}} ∘ … ∘ A_1 ∘ off_{d_0}` with cumulative linear parts `A_(k)`
(`A_(0) = I`) and `Q_k(v) = |A_(k) v|²`:
`ds_n = √Q_n(v) · [1 − Σ_k d_k · det A_(k) · (v×v′) / Q_k(v)^{3/2}] dt`.
Translations, rotations, `restrict` and `arc_of_length` do not change the shape class. Rotations
are isometries but do change `Q_k` for later scalings.

**(F4) Addition theorem (numerically checked, c ∈ {0.3, −2.5, 0.93}).**
`cn(u+v) = (cn u cn v − sn u sn v dn u dn v)/(1 − c sn²u sn²v)`, where
`sn′ = cn dn`, `cn′ = −sn dn`, `dn′ = −c sn cn`, and `am′ = dn`.

## 3. Heuristic obstruction to the single-curve route (to be confirmed or broken by R1)

A holomorphic differential integrated along a path to a point at infinity of an algebraic curve
stays finite. So an **unbounded** algebraic drawable curve (graph, power law, Bézier extended,
hyperbola) has an arc length with poles, which means a second-kind part or a boundary term.
For **bounded** ones (ellipse chains) the leading term `√Q_n(v) dt` is `E`-type (non-zero
second-kind class) unless `Q_n` is constant, and then the corrections `dt/Q_k^{3/2}` give only
`E` plus a boundary term (`∫dθ/Δ³ = (E − c sinθ cosθ/Δ)/(1−c)`). Different `Q_k` live on
different elliptic curves, whose cohomology classes cannot cancel. That is only a sketch, and
finding the hole in it is the most valuable outcome.

## 4. What counts as success

* **Breakthrough:** an explicit drawable curve (in the constructor language of `Defs.lean`)
  plus a parametrisation with `s_C = α F(φ(T)) + β`, for **every** `c < 1` or at least for an
  explicit infinite family of `c`, numerically verified. Or an explicit composition formula for
  `am(u)` using only operations already known P-constructible, numerically verified.
* **Useful negative:** a clean argument, with its assumptions stated, that a given class cannot
  work, and a precise list of the loopholes it does not cover.
* Do not claim impossibility of `PConstructible (jacobiAm c u)` outright. Nobody expects a proof
  of that; say what class of constructions is excluded.
