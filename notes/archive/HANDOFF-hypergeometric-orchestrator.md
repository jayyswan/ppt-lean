# HANDOFF — hypergeometric ₂F₁ programme (for the next orchestrator)

## Where things stand

- Repo `C:\dev\Powerpoint\lean\pptc`; work lives in `Pptc/Hypergeometric/`.
- HEAD at this handoff is the previous commit (`ffb7ca7`, R4/R5 + orchestrator handoff);
  everything below is uncommitted at handoff time (see `git status`).
- **V7 (the quartic Goursat transformation) is now PROVED and `Signatures.lean`'s quartic
  signature is unconditional.** This was open thread 1 of the previous handoff.

## V7 — landed (inbound, unconditional)

The theorem (in `V7Real.lean`):

```lean
theorem hyp_quarter_three_quarter {z : ℝ} (hz0 : 0 ≤ z) (hz : z < 1) :
    hyp (1 / 4) (3 / 4) 1 z =
      (1 + Real.sqrt z) ^ (-(1 / 2 : ℝ))
        * hyp (1 / 2) (1 / 2) 1 (2 * Real.sqrt z / (1 + Real.sqrt z))
```

and `Signatures.hyp_quarter_three_quarter_Pconstructible` is now
`@[pconstructible_cond]` with no identity hypothesis.

### How it was done (the ODE / Heun route)

Files, in dependency order:

| file | content |
|---|---|
| `Goursat.lean` | general formal hypergeometric ODE `hypSeries_ode (a b c)` (needs `c ∉ −ℕ`) |
| `SqrtSeries.lean` | the formal series `sqrtInvSeries = (1+X)^(-1/2)`, `h*h*(1+X)=1`, `(1+X)h' = -(1/2)h` |
| `Heun.lean` | `phiSeries = ₂F₁(1/4,3/4;1;X²)`; it solves the Heun equation `X(1−X²)F''+(1−3X²)F'−(3/4)XF=0`; `heun_uniqueness` (constant term fixes the solution) |
| `HeunMobius.lean` | `mSeries = ₂F₁(1/2,1/2;1;2X/(1+X))` (Möbius pullback) and `rSeries = sqrtInvSeries * mSeries`; both solve the same Heun equation |
| `V7.lean` | `phiSeries_eq_rSeries` (the formal V7 identity, via `heun_uniqueness`) |
| `V7Eval.lean` | `hasSum_phiSeries`, `hasSum_sqrtInvSeries` (evaluations, `\|w\|<1`) |
| `V7MobiusEval.lean` | `hasSum_mSeries` (evaluation of the re-expanded Möbius substitution, `\|w\|<1/3`) |
| `V7Real.lean` | Cauchy product → `hasSum_rSeries` → `goursat_small` (`\|w\|<1/3`) → `goursat_unit` (`0≤w<1`, analytic continuation on `(0,1)`) → `hyp_quarter_three_quarter` |

Key mathematical point: the `w = √z` substitution turns the two hypergeometric equations of
`(1/4,3/4;1)` and `(1/2,1/2;1)` into the *same Heun equation* once the square-root prefactor
is included; the Heun equation's coefficient recurrence `(m+1)²a_{m+1} = (m²−1/4)a_{m-1}`
then makes the constant term `1` determine the series, giving the coefficient identity for
free. The general `hypSeries_ode` (the previously missing infrastructure) is what made the
two pullbacks mechanical.

## Open thread 1 (started) — the cubic and sextic signatures

`Signatures.lean` still carries the cubic (RBBG) and sextic (Shen/Robinson) transformations as
explicit hypotheses, and those two conditional theorems are deliberately **not**
`@[pconstructible_cond]`. To finish H5 they need the same treatment as V7. A cubic/sextic thread
is now under way; read `HANDOFF-hypergeometric-cubic.md` first. Status:

- `SubstODE.lean` (general pullback `hypSeries_subst_ode`), `CubicSetup.lean` (the parametric
  series `α, β, γ` and their identities), `Cubic.lean` (`cubicOp`, `cubicOp_lhs`) and
  `CubicUnique.lean` (`cubicOp_unique`) are **landed and sorry-free**.
- The one remaining formal gap is `cubicOp_rhs` (the right-hand side satisfies the shared ODE),
  blocked on the two proportionality identities `aC*eT = dT*bC`, `aC*fT = dT*cC`, whose
  infrastructure is in the compiling-but-incomplete `CubicRHS.lean`. The handoff records the
  exact state and two candidate routes (a `FractionRing`/`field_simp` route that nearly closes,
  and a polynomial-clearing route that avoids it).
- After that: real transfer for the cubic, then the sextic by the same template, then re-tag
  the two theorems in `Signatures.lean`.

## Open thread 2 — B6 breakthrough (unchanged)

Still wanted: a drawable construction realising the **first-kind** period
`A = (1/10)B(1/10,2/5) = 1.1905798216…`. See `NOTES-hypergeometric-R5.md`; a *bounded*
first-kind arc only gives the incomplete integral, so what is needed is a closed drawable
genus-≥2 curve, or a primitive whose complete period is first-kind. The bounding box does not
help. Correction: R1's second `m = 10` period is `(1/10)B(3/20,7/20) = 0.89354817…`.

## Tooling notes

- `lake_check` (i.e. `lake env lean`) needs the imported modules' `.olean`s. New modules must
  be built once with `lake build Pptc.Hypergeometric.<File>` (single narrow target) before
  another file can `import` them. `lake build Pptc.Hypergeometric.Signatures` builds the whole
  new chain in one go.
- Transient `failed to read file '…/Mathlib/….olean(.private)'` errors during a build are
  environmental (file-lock / leftover processes), not proof errors: kill only leftover
  lean/lake processes (`Get-Process lean,lake | Stop-Process -Force`) and rebuild. Doing this
  fixed the one failure in this session.
- The `lean-lsp` tools (`lean_diagnostic_messages` etc.) are far faster than `lake_check` for
  iteration; subagents used them successfully throughout.

## Subagent deliverables this session (all landed, sorry-free, targeted imports)

`HANDOFF-hypergeometric-{goursat-ode, sqrtseries, heun-lhs, heun-rhs, v7eval, v7mobius,
v7real}.md`, plus the code files listed in the table above. `Hypotheses`-style checks:
`lean_verify` on the headline theorems reports only `propext`, `Classical.choice`,
`Quot.sound`.
