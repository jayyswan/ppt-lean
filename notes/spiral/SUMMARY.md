# Archimedean spiral: summary of the survey

Orchestrator summary of `pptc/PLAN-spiral.md`, written 2026-11-03. Sources are the stream notes in
this folder:
- W, I1–I4, O, B, C, D, L;
- the follow-ups F1–F4.

Labels: [Proof], [Wolfram], [Heuristic], [Open], as in the stream notes. Class codes:
- **E**: elementary or algebraic;
- **R**: already reachable without the spiral;
- **N**: new and named;
- **?**: new and unnamed.

The spiral is **not** in `Defs.lean`. Adding it is the user's decision (§4).

## 1. The curve

- **Route.** A polygonal glyph in a text box, under Text Effects ▸ Transform ▸ Warped Circle (or
  Arch: Warped / Arch: Warped Down), with the yellow handle left at its default.
- **The map.** A straight glyph edge becomes an arc of `r = A + Bθ` [Measured, F1]. Corners are exact
  to 0.06–0.74 pt; between corners the error is 2.8–5.4 % of R. This is category (b), which is
  closer to its ideal than the `sine` glyph is.
- **Normal form [Proof, W].** Every drawn arc is a mirrored similarity image of `r = ψ` on a window
  `[2πq₁, 2πq₂]` with P-constructible ends.
  - One arc turns at most once.
  - `q₂ ≤ 2q₁` for Warped Circle and Arch: Warped; `q₂ ≤ 4q₁` for Arch: Warped Down.
- **Reachable ψ** [F2]. About `[0.002, 47]` with font, spacing and stacked-row choices. It is not
  `(0, ∞)`.
- **Isolating a sub-arc [B].** `arc_of_length` from any P-constructible start isolates any
  sub-arc.

## 2. Catalogue

| Operation | Equation (normal form) | Class | Named / example | Reach |
|---|---|---|---|---|
| Box (any direction β) | `θ tan(θ−β) = 1` ⇔ `θ + arctan θ = β + π/2 + kπ` | **N** (T3; T2 with λ = 1) | `x tan x = 1` (Biot number Bi = 1, rod with a tip mass equal to its own), 0.86033…; `tan x = −x` (Robin rod, h = 1), 2.02876… | every audited root has a window [F2] |
| ∩ line through the pole; ∩ circle about the pole | elementary | E | — | — |
| ∩ general line, centred conic, off-centre circle, focal conic (`B² = 8fA`) | one harmonic × power of θ, or cosine ∩ hyperbola | R | Dottie, Kepler | — |
| ∩ generic conic; parabola `sin θ = kθcos²θ`; off-centre hyperbola | `Re(Aθ²e^{2iθ}+Bθe^{iθ}) + mθ² + f = 0` | ? | — | 343 roots audited, all reachable [F2] |
| ∩ poly graph deg ≥ 2, power law (b ∉ {0, ±1}), loop/cusp Bézier | never collapses to one harmonic [Proof, F3] | ? | solitary-node Bézier is R | — |
| ∩ `exp_two`, ∩ sine | nested transcendental | ? (F4: near-proof of novelty for `exp_two`, not reviewed) | `θ sin θ = 2^{θ cos θ}` | — |
| ∩ spiral, same pole | closed form | E | — | — |
| ∩ spiral, different pole / non-uniform partner | coupled | ? | mirror poles: on-axis roots are R | — |
| ∩ own offset | normal-chord quartic ∩ `t = tan(Δ/2)` | ? | none for \|d\| < π/2 | — |
| Offset spiral: box, cusps | box ± d; `c³ = d(c²+1)` | E/R | d = 1: supergolden ratio | — |
| Offset spiral ∩ line or conic | — | ? | — | — |
| Offset inversion along the spiral (offset → `arc_of_length` → 2 boxes) | `½(sinh u cosh u + u) − d(sinh u + gd u) = c` | ? | — | — |
| Arc length between roots; inverse arc length from any start (uniform spiral) | elementary in the roots; parabola inversion | R | — | — |
| Non-uniform image: offset cusp, arc-length inversion | trig × polynomial; non-elementary integral | ? | — | — |

**Negatives [Proof].** No single step reaches T1, T2 (λ ≠ 1) or T6 with fixed constants. This
covers I1, F3, B and C. No Lambert-W or Kepler class is new.

## 3. Structure

- **Composition is triangular [Proof, C].** Depth n splits into one-step equations whose
  parameters come from earlier roots. No new equation *shapes* appear.
- **The box tower is iteration of `φ⁻¹`** with `φ(θ) = θ + arctan θ`, the spiral's tangent-angle
  function. It gives 0.8603…, 1.4607…, 1.9372….
- **Parameter slots [C].** A spiral number can enter every parameter slot except:
  - the `power_law` exponent;
  - the shape invariants of degree-5 and degree-6 polynomials.

**Strength of novelty claims:**
- Only the box family is *named*. Its novelty relative to the spiral-free class is [Heuristic].
- For `exp_two`, F4 makes an Ax–Schanuel argument, not independently reviewed.
- Everything else marked ? is [Heuristic], from a search with no name found and no reduction found.

## 4. Constructor options (D)

**Recommended, D form A1:** one fixed open ray, like `sine` and `exp_two`.

```lean
noncomputable def spiralParam (t : ℝ) : ℝ × ℝ := (t * Real.cos t, t * Real.sin t)
| archimedes : PConstructibleCurve (spiralParam '' Set.Ioi 0)
```

- Similarity, mirroring and windows come from the existing closure operations.
- Lean cost is small: `speed = √(1+t²)` was checked in a scratch file, injectivity and C¹ are
  immediate.
- **Over-claim.**
  - Multi-turn extent adds nothing [Proof for `inter`, argued for `box`].
  - The ψ-range does add numbers. Roots above ψ ≈ 47 are new (for example the 16th and later
    roots of `x tan x = 1`), and scaling cannot remove them. This differs from `sine`, whose range
    `scale_x` removes.
- **Fallback, D form B2:** rational turn fractions plus the W/F2 window law as hypotheses. It is
  exact, but heavy, and loses theorems of the form "for every k".
- **Rejected:**
  - the glyph-edge warp-map form (better as a derived lemma);
  - a two-sided `t ∈ ℝ` (not injective).

**Decisions for the user** (full list in `D.md`):
1. Accept the ray's unlimited ψ, or keep the measured window?
2. Exclude or include the origin?
3. How does the `sine` glyph become a curve (D assumed Merge Shapes ▸ Combine)? The spiral should
   use the same route.
4. Is a visual check of the both-guides-full box sizes acceptable?
5. Include the Arch presets, or only Warped Circle?

## 5. Open

- Independent review of F4's novelty arguments.
- Root counts in I4 are uncertified, and so is C's mirror-pole scan.
- Offset injectivity on windows longer than one turn; non-uniform cusp scan beyond starts 0.3–3.8.
- Not surveyed: a spiral meeting the offset of another base curve (C).
- L's "no name" is heuristic, because OEIS could not be fetched.
- The routes for the named roots are untested in PowerPoint.
