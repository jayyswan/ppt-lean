# Inverting the first-kind integral with a continuous handle: ideas, identities, obstructions

Written 2026-11-08. Scripts used for every numerical check are described inline (mpmath, 30 digits;
residuals ≤ 1e-30). Labels: **[Proof]** paper argument, **[Num]** checked numerically at 30 digits,
**[Idea]** not established, **[Open]**.

Setting. The handle may sit at any P-constructible value in its range (idealized exact). Target:
`jacobiAm`, i.e. P-construct the `φ` with `F(φ | m) = u` for P-constructible `u`, `m`
(`Pptc/Jacobi.lean`, "Why the first kind resists"). Existing verdicts that this note does not
contradict: no algebraic text curve has first-kind arc length (§14.2), no slide-preset trochoid crossing
isolates `F` (§14.7), and offset towers keep a residue obstruction at `∞±`
(`notes/offset-inversion/SUMMARY.md` §3).

## 1. The right way to see the obstruction

Every drawable arc length is an abelian integral `∫ ν` on an elliptic curve `C: w² = Q`. Its class in
`H¹_dR(C)` (2-dimensional for second-kind differentials) and its **pole set** are what matter.

* `F` is `∫ ω`, `ω = dt/w`, no poles. A drawn curve has `ν` with poles at the points at infinity (the
  boundary term) or at the circular points.
* Two second-kind differentials on the *same* curve with *independent* classes combine to
  `a ν₁ + b ν₂ = c ω + d(algebraic)`. Pole sets do not obstruct this; only the class does. **[Proof]**
* So the algebra is not the problem. Two things are: (i) the leftover `d(algebraic)`, the boundary
  term; (ii) **linking**: forcing both arcs to be taken at the same point of `C`.

## 2. Exact identities found

**2.1 Cubic Bézier and ellipse on one curve [Proof + Num].** Let `Q(t) = B²(1−t²)² + 4A²t²`,
`w = √Q`, `F₀(t) = ∫₀ᵗ dt/w`.

* The cubic Bézier `γ_B(t) = (B(t − t³/3), A t²)` has speed `w`.
* The ellipse `(B cos ψ, A sin ψ)` at `t = tan(ψ/2)` has `ds = 2w dt/(1+t²)²`.
* Both are second kind on `w² = Q` with classes `(2B²/3)ω + ((4A²−2B²)/3)η` and `B²(ω − η)`
  (`η = t² dt/w`). Independent, so with `b₂ = (4A²−2B²)/3`:

      F₀(t) = 3/(4A²B²) · [ B² J_B(t) + b₂ s_E(2 arctan t) − B² t w/3 − b₂ t w/(1+t²) ].

  Residual 2e-31. `t w/(1+t²) = D(ψ) sin ψ / 2` with `D = √(A² sin²ψ + B² cos²ψ)`.
* A cubic *graph* guide `g′ = αx² + γ₀` matches such an ellipse when `4A²/B² = 2 + 2γ₀/√(1+γ₀²)`
  and `t = λx`, `λ² = α/√(1+γ₀²)` (checked: `Q_g(x) = ν Q_E(λx)`). **This is where the continuous
  handle enters: the Wave amplitude `K` (hence `γ₀`) and the Warp Up ratio `A/B` must be tuned
  together, and isolated handle values cannot do it.**

**2.2 Landen as a two-ellipse identity [Num].** With `k′ = b/a`, `k₁ = (1−k′)/(1+k′)`,
`tan(φ₁ − φ) = k′ tan φ` (so `φ₁ = φ + θ`, eccentric plus polar angle):

    E(φ | m) = ((1+k′)/2) E(φ₁ | m₁) − k′ F(φ | m) + ((1−k′)/2) sin φ₁.

The second ellipse is the AGM step `((a+b)/2, √(ab))`. So `F` is a combination of two ellipse arcs
at algebraically linked points.

**2.3 Offset plus scaling gives the same cancellation inside one legal curve [Proof + Num].**
`γ_std(t) = (t − t³/3, t²)` has speed `1+t²`, unit left normal `n = (−2t, 1−t²)/(1+t²)` (rational).
`Σ_d := scale_x B ∘ scale_y A ∘ offset_d(γ_std)` is a legal `PConstructibleCurve` and

    Σ_d(t) = γ_B(t) + d·(−2Bt, A(1−t²))/(1+t²),  speed = w·(1 − 2d/(1+t²)²),
    arc length  L_d(t) = J_B(t) − d·s_E(t)         (exact, Minkowski sum with parallel velocities).

At `d = −b₂/B²` the second-kind parts cancel:

    L(t) = (4A²/3) F₀(t) + t w/3 + (b₂/B²) t w/(1+t²).       [Num, residual 1e-30]

So *for every modulus* there is a drawable curve whose arc length is first kind plus an explicit
algebraic term and nothing else (cusp-free iff `1 − 2d > 0`). This is the one-stage tower of
`R2`/`R4`; the old notes had it as "elliptic plus independent elementary". What is new is the closed
form and that `d` and `A/B` are the two continuous knobs. The boundary term remains, as `R4` proves it
must for any algebraic curve.

**2.4 The lemniscatic pair [Num].** On `w² = 1 + x⁴`: `y = x³/3` has `J = x w/3 + (2/3)Φ`, and the
hyperbola `y = 1/x` has `J_h = 2Ê − w/x` (pure second kind). Same curve, same coordinate `x`, so they
*are* linked by the shared abscissa. But neither is a text guide, so neither arc becomes a plane
coordinate, and the boundary term `x w/3` is the tangent length (already in §14.6).

## 3. The pole-free curve

**3.1 [Proof + Num].** The curve `cosh x = c cos y` (`c > 1`) has arc length exactly

    ∫ ds = √(c²−1) ∫ dy / √(c² cos²y − 1) = F(y | c²/(c²−1))      (residual 0 at 30 digits)

with *no* boundary term. It is `Log` of the circle `|z − c| = √(c²−1)` (a circle orthogonal to the unit
circle): `|d log z| = |dz|/|z|`, so the first-kind integral is the length of a circle measured in the
cylinder metric. Equivalently it is the hodograph curve `∫ i p(φ) dφ` of the ellipse `p(φ)`, in
separated form `sin²X/k² + sinh²Y/k′² = 1`.

**3.2 It is the same family as the project's missing curves.** The log-cosine `y = ln sec x` is
`Log` of a *line* (`e^y cos x = 1`). So the missing curves of `offset-inversion/SUMMARY.md` §5 and the
missing base curve for `am` (Serret, `Jacobi.lean` Outlook) are all conformal-`Log` images of a line or
circle. One PowerPoint route to `z ↦ log z` on a circle or line would settle the log-cosine, the beam
spectra, and `sn`. This is the cleanest statement of "what is missing" I found.

**3.3 Why nothing legal builds it.** The constructors give algebraic curves, `sin`, `2^x`, affine maps,
offsets and text images. Polar presets give `z = (a + bv) e^{icu}`, which is `exp` of a *reparametrized*
chart, not `log`. A glyph circle maps to a polar graph, not to `Log(circle)`. Charts with log axes give
the coordinatewise `(ln x, ln y)`, not `(ln |z|, arg z)`. No route found.

## 4. Obstructions proved on the way

* **Affine link impossible [Proof].** For two image curves to share an abscissa on a common elliptic
  curve, their branch sets must agree under a *real affine* map. Cubic-graph guides have no real branch
  points (`Q = 1 + g′² > 0`); the ellipse in `X = cos ψ` has four real ones. Two ellipses match only if
  similar (`m₁ = m₂`, proportional classes); the reciprocal-modulus pair needs `m > 1`. So graph × ellipse
  and ellipse × ellipse trochoid crossings cannot realise 2.1 or 2.2.
* **The `t`-link is projective.** 2.1 needs `x ∝ tan(ψ/2)`, i.e. `cos ψ = (1−λ²x²)/(1+λ²x²)`; 2.2 needs
  `tan(φ₁−φ) = k′ tan φ`. Neither is affine, and `offset` introduces an extra radical.
* **Pell/torsion.** For every cubic guide the unit `u = g′ + w` has norm −1, so `∞₋ − ∞₊` is 2-torsion.
  A degree-≤6 graph with speed `r w` and `r ≠ const` needs a higher torsion order, so no second class on
  the same curve comes from `poly_graph`. A cubic Bézier realises *every* positive quartic `Q` (sum of two
  squares), but a single arc is pure first kind iff `Q = q(t−t₀)⁴ + q₀`: lemniscatic only.
* **Handle derivative [Idea, blocked].** `F = E − 2m ∂E/∂m`: a tunable modulus is exactly the missing
  dimension, but P has no derivative or envelope operation.
* **Doubling and addition [Proof].** `s([n]P) = n s(P) − alg` and Poncelet chords give algebraic
  translations. They fix torsion `u` only.

## 5. Enumerated ideas and verdicts

| # | Idea | Verdict |
|---|---|---|
| 1 | Cancel `Ê` between Wave cubic and Warp ellipse (2.1) | identity exact; link blocked (§4) |
| 2 | Landen/AGM pair of ellipses (2.2) | identity exact; link `tan(φ₁−φ) = k′tanφ` blocked |
| 3 | Offset+scale Minkowski curve (2.3) | legal; arc = first kind + boundary; boundary unremovable |
| 4 | Lemniscatic pair cubic/hyperbola (2.4) | same curve, shared abscissa; not text guides |
| 5 | Pole-free `Log`-circle curve (3.1) | exact; **missing base curve** |
| 6 | Modulus derivative in the handle | needs a derivative operation |
| 7 | Doubling, addition, Poncelet | only torsion `u` |
| 8 | Chaining outputs as handles | triangular (`R4`); no new shapes |
| 9 | Pell units for a second class on one curve | blocked by degree ≤ 6 / torsion order |
| 10 | Real-affine link by shared abscissa | impossible (real structure) |
| 11 | Mismatch presets (arc-fraction link) | gives a transcendental link, not an algebraic one |
| 12 | Log-axis charts for `Log` | coordinatewise log only |
| 13 | Limit / Newton / infinite AGM | no limit constructor |

## 6. What I would do next

1. **Hunt for `z ↦ log z`.** Candidates: the Pour presets with the inner-radius handle driven to 0
   (`z = v e^{icu}`, a pure `exp` chart), polar/radar charts with a logarithmic radial axis, and any
   preset whose guide has arc length `∼ log` (tractrix, catenary). Test whether the *inverse* chart
   can be read: a glyph curve `v = e^{w(u)}`.
2. **Realise the `tan(ψ/2)` link.** It is a chord slope from a fixed point: the projective map the
   toolbox lacks. Shadows are affine only (`ppt-curves/SUMMARY.md`); 3-D perspective is raster.
3. **Prove the boundary term unremovable for the whole tower including the continuous handle** (a
   strengthening of `R4`): the residues at `∞±` are independent of `d`, `A/B` and `γ₀`.
4. If 1 or 2 fails, record 2.1–2.3 and 3.1 as the reduction: *`am` is P-constructible if the curve
   `cosh x = c cos y` (or an equivalent Serret curve) is, by the abutting-arcs argument of
   `ellipticEAm_Pconstructible_of_mem_Icc`*. The converse is not claimed.
