# HANDOFF: HeunMobius.lean

Target file: `Pptc/Hypergeometric/HeunMobius.lean`
Goal (Lean syntax):
```lean
noncomputable def mobius : PowerSeries ℝ := 2 * PowerSeries.X * (1 + PowerSeries.X)⁻¹
theorem hasSubst_mobius : PowerSeries.HasSubst mobius
noncomputable def mSeries : PowerSeries ℝ :=
  PowerSeries.subst mobius (hypSeries (1 / 2) (1 / 2) 1)
theorem mSeries_ode : ...
noncomputable def rSeries : PowerSeries ℝ := sqrtInvSeries * mSeries
theorem coeff_zero_rSeries : PowerSeries.coeff 0 rSeries = 1
theorem rSeries_heun : ...
```

## Plan
1. Read Goursat.lean / SqrtSeries.lean / Quadratic.lean signatures (hypSeries_ode,
   subst lemmas, linear_combination template).
2. Build helper lemmas for mobius derivative identities.
3. mSeries_ode via substitution + linear_combination.
4. coeff_zero_rSeries via constantCoeff lemmas.
5. rSeries_heun via prefactor relation and factorization.

## Log
- [start] Created log.
- [part1] compiles.
- `mSeries_ode` compiles. Note: the literal task statement `(1/2 : ℝ) * mSeries` does NOT
  elaborate (no `Coe ℝ (PowerSeries ℝ)` / `HMul ℝ (PowerSeries ℝ)`); used
  `PowerSeries.C (1/2) * mSeries` instead (definitionally the intended `algebraMap (1/2)`).
  Key facts: hY (specialized hypergeometric ODE via hypSeries_ode), hsubst, key (via
  coe_substAlgHom + AlgHom.commutes + map_ofNat), hM1/hM2 (derivative_subst), hrearr,
  hconst (2*C(1/4)=C(1/2)), linear_combination 2*key.
- `coeff_zero_rSeries` and `rSeries_heun` compile; `rSeries_heun` uses prefactor identities
  hp1 `(1+X)h' = -C(1/2)h`, hp2 `(1+X)h'' = -C(3/2)h'`, hp3 `(1+X)^2 h'' = C(3/4)h`,
  c1/c2 for R=sqrtInvSeries*mSeries, then hfactor with helper constants
  h2half `2*C(1/2)=1`, h34 `2*C(3/4)=3*C(1/2)`, and `resolve_left (pow_ne_zero 2 onePlusX_ne_zero)`.
  Same `C` substitution for `(3/4 : ℝ) * X`.
- FINAL: `lake_check Pptc/Hypergeometric/HeunMobius.lean` -> "OK - no errors or warnings."
  `lean_verify Pconstructible.rSeries_heun` -> axioms propext, Classical.choice, Quot.sound.
  No sorry/axiom. File is 477 lines. Deviation on constants is forced (no coercion).
