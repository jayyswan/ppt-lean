# Offset inversion: summary (stream S)

This is the synthesis of `pptc/PLAN-offset-inversion.md` (2026-11-03). It draws on W0, R0–R5 and the
Lean files L0–L2 in `pptc/Pptc/OffsetInversion/`.

The labels are those of the stream notes: [Proof], [Wolfram], [Heuristic], [Open].

## 1. The mechanism

The construction has four steps:

1. Make an arc a curve of its own, using `restrict` or `arc_of_length`.
2. `offset` the whole arc by `d`. This is the whole-curve axiom (PLAN-offset-soundness).
3. Lay a length `x` along the offset with `arc_of_length`.
4. Read the endpoint with `box_xmax` / `box_ymax`.

On a stretch with no cusp (`1 − dκ > 0`), the endpoint's tangent angle ψ solves

> `R(ψ) − R(ψ₀) − d(ψ − ψ₀) = x`  (OI),

where `s = R(ψ)` is the Whewell function. In the variable `u = asinh(tan ψ)` this becomes
`A(u) − d·gd u = x` with `A = ∫ ds/du du`.

- **Speed identity [Proof, R0; Lean, L1 `Speed.lean`].**
  `speed(offsetParam γ d) = |1 − dκ|·speed γ`, so the offset's arc length is `ΔR − dΔψ`.
- **Cusps are legal [Proof, R0].** `arc_of_length` can cross an ordinary cusp. Only the box
  readout fails there, because no coordinate is monotone across a cusp.

## 2. Catalogue: what (OI) gives for each drawable curve (R1, R2)

| Base curve (any affine image) | Whewell class | Equation family | Status |
|---|---|---|---|
| parabola | genus 0, elementary | `sinh 2u/4 + u/2 − d·gd u = x` | **new family [Proof, R3]; in Lean (L2)** |
| odd-`n` power laws `y = x^{1+1/n}` | genus 0 | elementary, with an explicit `gd⁻¹ψ` term | new |
| Neile `y = x^{3/2}` | genus 0 | `sec³ψ = αψ + β` | collapses: R |
| cubic graph, cubic Bézier, ellipse, sheared sine | genus 1 | elliptic plus `dψ` (third kind) | one new family each; none collapses |
| graphs of degree 4–6; power laws with `num(p−1) ≥ 3` | hyperelliptic, genus ≥ 2 | — | formally new; unusable |
| `exp_two` | genus 0 | irreducibly transcendental in ψ | new |
| lines, rectangle | — | degenerate | nothing |

General facts:

- **`d` never changes the genus [Proof].** The term `dψ` is always elementary and is the
  third-kind part.
- **Genus is invariant under affine maps** and is read off `z² = speed²`.
- **The tower** (R2, R4):
  - A non-conformal affine step adds a second-kind elliptic term `σ₁E(φ|k)`. There is at most
    **one** bare arctan per equation [Proof].
  - So the genuinely new tower class is "elliptic + elementary, with independent coefficients".
    Its best instance is R2's N1, which R4 checked as a legal route.
  - R4 corrected R2's cusp-free condition to `1 − d₁ − d₂c > 0`.
- **Composition is triangular [Proof, R4].** Feeding outputs back in as `d`, `x`, start points,
  crop bounds or affine data only extends the parameters; no new equation shapes appear.
  - Two offsets add (`d₁ + d₂`).
  - **Chains of two offset inversions are triangular [Proof, R6].** Same-word chains collapse to a
    single entry (lengths add, or a P-constructible constant shift if an offset or affine sits
    between the links). Re-based chains are one-step entries whose data lie in the field of the
    first root, so they add numbers, not equation shapes. No separate depth-6 separation theorem
    is needed; the remaining question is the data-dependence gap (R2 Q3.4, R3 §3.9(2)–(3)).
    See `notes/offset-inversion/R6-chains.md`.

## 3. Separation theorems (R3, R4)

- **Parabola family [Proof, R3].**
  - Its function `F(u) = sinh 2u/4 + u/2 − d·gd u` has infinitely many finite logarithmic
    branch points (`u = iπ(m+½)`).
  - The graph function of every drawable tower curve has only finitely many.
  - So for `d ≠ 0`, **no single intersection** and no single box with affine dependence on `x`
    solves the family uniformly.
  - Separation survives depth ≤ 2. The construction itself has depth 3
    (`offset → arc_of_length → box`).
  - The case `d = 0` is [Open].
- **`am` stays out of reach [Proof + Wolfram, R4].** `dψ` and every weighted angle form are
  holomorphic at `∞±`, so offsets cannot cancel the residue obstruction.
- **Rigidity [Proof, R2].** To match the beam spectrum, or `tan x = λx`, for all parameters,
  the curve must be parallel to the log-cosine, or to the catenary. No base curve is.
- **Sheared sine [Proof sketch, R4].** An offset sheared sine never meets an algebraic
  offset/affine word in a way that gives `tan x = x` uniformly.

## 4. Named problems (R5)

| Reachable now (R) | In the class with a drawable curve | Needs a missing curve (M) |
|---|---|---|
| optimal projectile angle `sin θ·gd⁻¹θ = 1` (**Lean, L0**); Laplace limit `z tanh z = 1`; Neile; clothoid; catenary of given length; rainbow angle | the parabola family (no classical name) | `tan x = λx`, `j₁` zeros, clamped–hinged beam (**catenary**); gear involute `tan α − α = k` (**catenary**); cantilever and clamped beams, rhumb line, pendulum separatrix (**log-cosine**); goat problem (**`tan ψ − (π/2)sec ψ`**, plus a pole/fold obstruction); tractrix; elastica (elliptic) |

R4's search found nothing: 288 PSLQ tests at 130 digits found no relation between the
`tan x = x`, beam or goat roots and the drawable families.

## 5. Missing curves, ranked by what each unlocks

1. **Catenary.** `tan x = λx` for every λ, the involute function, `j₁` zeros, the clamped–hinged
   beam.
2. **Log-cosine `y = ln sec x`.** Both beam spectra, rhumb lines, the separatrix.
3. **Curve with `R = tan ψ − (π/2)sec ψ`.** The goat problem (with an extra obstruction).
4. **Tractrix and elastica.** Their own families only.

None has a PowerPoint route yet. This ranking goes to `PLAN-ppt-tan-curves.md`, stream M.

## 6. Lean status

- **L0** `Projectile.lean`: the projectile angle.
- **L1** `Speed.lean`: the speed identity and the arc-length corollary.
- **L2** `Parabola.lean`: `parabola_offset_root_Pconstructible` and its `arsinh` corollary.

All three were repaired to the whole-curve `offset` axiom (commit 875a294). None contains
`sorry`.

## 7. Open

- The `d = 0` separation case.
- Separation for the full tower beyond the base catalogue, and in particular whether a catenary
  or log-cosine parallel curve lies in the tower.
- ~~Chains of two offset inversions~~ **Resolved as a reduction (R6).** Same-word chains collapse to
  a single entry; re-based chains are one-step entries with data in the first link's field. They
  add numbers, not equation shapes, so no depth-6 separation theorem is needed — only the
  data-dependence gap (R2 Q3.4, R3 §3.9(2)–(3)), which chains do not close. See
  `notes/offset-inversion/R6-chains.md`.
- Arithmetic (non-uniform) coincidences with named roots. These are not excluded; nothing was
  found.

**Bottom line.** Offset inversion is a genuine new mechanism. It is proved separate from
intersections and is formalized for the parabola. Its *named* payoff is gated on two curves
PowerPoint does not draw: the catenary and the log-cosine.
