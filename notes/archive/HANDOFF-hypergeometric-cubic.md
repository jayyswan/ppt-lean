# HANDOFF — cubic (and sextic) Ramanujan signatures

## Goal

Prove, as formal power series in the parameter `p`, Ramanujan's **cubic** transformation

`₂F₁(1/3, 2/3; 1; β(p)) = γ(p) · ₂F₁(1/2, 1/2; 1; α(p))`,  `p ∈ [0,1)`,  (`CUBIC`)

with `α(p) = p³(2+p)/(1+2p)`, `β(p) = 27p²(1+p)²/(4(1+p+p²)³)`, `γ(p) = (1+p+p²)/√(1+2p)`;
and the **sextic** analogue

`₂F₁(1/6, 5/6; 1; ξ(p)) = √(1+p+p²)/√(1+2p) · ₂F₁(1/2, 1/2; 1; x(p))`,  (`SEXTIC`)

with `x(p) = p(2+p)/(1+2p)`, `ξ(p) = (27/4)p²(1+p)²/(1+p+p²)³`.
Once these are unconditional, `Signatures.hyp_one_third_two_thirds_Pconstructible` and
`hyp_one_sixth_five_sixths_Pconstructible` lose their `hCubic` / `hSextic` hypotheses and can be
tagged `@[pconstructible_cond]`.

## Strategy (validated symbolically, zero residual — Wolfram)

Same shape as V7 (`Pptc.Hypergeometric.V7`): both sides satisfy **one shared second-order
linear ODE**, so their equality follows from equal constant terms. Concretely, let `D` be
`PowerSeries.derivative ℝ` and pull the `(1/3,2/3;1)` hypergeometric equation back along `β`
(multiplying through by `(β')³` to avoid dividing by `β'`, which vanishes at `p = 0`):

`cubicOp F := β(1−β)β'·F'' + [−β(1−β)β'' + (1−2β)(β')²]·F' − (2/9)(β')³·F`.

Then:
- the left side satisfies `cubicOp (subst β (hypSeries (1/3)(2/3)1)) = 0` — **proved**;
- the right side satisfies `cubicOp (γ · subst α (hypSeries (1/2)(1/2)1)) = 0` — **the blocker**;
- a power-series solution of `cubicOp F = 0` is determined by `F(0)` — **proved**.
The sextic is the same computation with `(ξ, x, √(1+p+p²)/√(1+2p))` and `ab = 5/36` in place of
`(β, α, γ)` and `ab = 2/9`.

## Files (all compiling except where noted)

| file | status |
|---|---|
| `SubstODE.lean` | DONE — general pullback `hypSeries_subst_ode (a b c) (hc) (hφ)` |
| `CubicSetup.lean` | DONE — `gSeries, gammaSeries, alphaSeries, betaSeries`; `gSeries_mul_self`, `(1+2X)g'=-g`, `gammaSeries_mul_self`, `alphaSeries_mul`, `betaSeries_mul`, `hasSubst_*` |
| `Cubic.lean` | DONE — `cubicOp`, `cubicOp_lhs` |
| `CubicUnique.lean` | DONE — `cubicOp_unique` |
| `CubicRHS.lean` | **INCOMPLETE** — infrastructure compiles (warnings only), but `cubicOp_rhs` is not proved |

## The precise remaining blocker

`CubicRHS.lean` already has explicit derivative formulas (`deriv_alphaSeries`, `deriv2_alphaSeries`,
`deriv_betaSeries`, `deriv2_betaSeries`, `deriv_gammaSeries`, `deriv2_gammaSeries`, plus
`deriv_vC/uC/nC/eC`), the `γ`-free forms `dT, eT, fT`, the `(1/2,1/2)`-operator coefficients
`aC, bC, cC`, and `aC_ne_zero`. Remaining:

1. The **proportionality identities** in `ℝ⟦X⟧`:
   `aC * eT = dT * bC`  and  `aC * fT = dT * cC`
   (equivalently, the operators `cubicOp` and the pullback of the `(1/2,1/2;1)` equation under
   `α` are proportional; Wolfram confirms both sides are *exactly* equal, and even
   `a/d = b/e = c/f`).
2. **Assembly**: from those, `linear_combination` with `hY` (the pullback ODE for
   `Y = subst α (hypSeries (1/2)(1/2)1)`) gives `aC * cubicOp (γY) = 0`, and `aC ≠ 0` plus the
   integral domain `PowerSeries ℝ` gives `cubicOp (γY) = 0`.
3. **Real transfer** (not started): `cubic_small` on a disc, analytic continuation on `(0,1)`,
   and the `p`-statement of (`CUBIC`); then the same for (`SEXTIC`), then wire into
   `Signatures.lean`.

### Notes from an attempt at (1)

- `field_simp` does **not** work on `PowerSeries ℝ` (not a field); it is used in
  `FractionRing ℝ⟦X⟧` (`IsFractionRing.injective` to transfer back). `CubicRHS.lean` has
  `algebraMap_inv_eq`, `algebraMap_uC_ne_zero`, `algebraMap_eC_ne_zero` for this.
- The route that nearly closed: `apply IsFractionRing.injective …`, `simp only [map_mul]`,
  rewrite all the derivative lemmas, then distribute `algebraMap` over the resulting *large*
  expressions with `simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one,
  map_zero]` (**`map_neg` is essential** — without it `algebraMap (negation)` blocks everything),
  then `rw [algebraMap_inv_eq …]` and `field_simp [algebraMap_uC_ne_zero, algebraMap_eC_ne_zero]`.
  After that, `field_simp` was still leaving divisions by `algebraMap (1+2X)` and
  `algebraMap (4(1+X+X²)³)`, so the final `ring`/`ring_nf` hit a "nested simp" error rather than
  closing. The likely fixes: (a) unfold `uC, vC, nC, eC, hC` is only needed *after* clearing;
  make sure `field_simp` is fed the nonzero facts in their **unfolded** form
  (`1 + 2*algebraMap X ≠ 0`, `4*(1+algebraMap X+algebraMap X^2)^3 ≠ 0`), or (b) avoid
  `FractionRing` and instead multiply the identity through by powers of the units
  `uC = 1+2X`, `eC = 4vC³`, `vC = 1+X+X²` to obtain a **polynomial** identity in `X`, then
  `ring` — this is probably the most robust route.
- The `a/d = b/e = c/f` proportionality suggests a possibly shorter certificate: find an
  explicit power series `r` with `aC = r*dT`, `bC = r*eT`, `cC = r*fT` (then both identities are
  immediate). `r = α(1−α)α'/(β(1−β)β'γ)` has order 2 and is nonzero.

## Suggested next run

Use route (b): state `uC * eC * vC * (aC*eT − dT*bC) = 0` (or a suitable power), expand the
derivatives via the lemmas already present, substitute `alphaSeries_eq`, `betaSeries_eq`, and
`eC, vC, nC, uC, hC`, and prove the resulting univariate polynomial identity in `X` by `ring`
(possibly with `set_option maxHeartbeats 2000000`). This avoids `FractionRing` and `field_simp`
entirely. Then assemble `cubicOp_rhs`.
