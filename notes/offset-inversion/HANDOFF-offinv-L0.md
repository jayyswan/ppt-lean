# HANDOFF — offset-inversion L0 (projectile corollary)

- read `PLAN-offset-inversion.md` §L0 and the source note §4; searched `Pptc/Basic.lean` for `laplace*`.
- reused `laplaceLimit_pos`, `laplaceLimit_spec`, `sqrt_one_add_laplaceLimit_sq`, `laplaceLimit_Pconstructible`, `arctan_Pconstructible`.
- wrote `Pptc/OffsetInversion/Projectile.lean`: `projectileAngle := Real.arctan (1 / laplaceLimit)`, P-constructibility, positivity, `< π/2`, and `projectileAngle_spec` (`sin θ · log (sec θ + tan θ) = 1`).
- `lean_diagnostic_messages`: clean (no errors/warnings). Three fixes: `field_simp` needed `laplaceLimit_pos.ne'`; `ring` → `field_simp` for the `(1/λ)²` identity.
- `lake build Pptc.OffsetInversion.Projectile`: success (2785 jobs, 30 s); added the import to `Pptc.lean`.
- **Gap recorded in the file docstring:** uniqueness of the root on `(0, π/2)` is not proved. Route if taken up later: `θ ↦ sin θ · gd⁻¹ θ` is strictly increasing on `(0, π/2)` because its derivative is `cos θ · gd⁻¹ θ + tan θ > 0`; combine with `f(0)=0`, `f(π/3)>1` and IVT. This was not needed for the plan's fallback (explicit angle + identity).
- no `sorry`; no push.
