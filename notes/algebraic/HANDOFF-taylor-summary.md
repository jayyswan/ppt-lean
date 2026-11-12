# HANDOFF: PLAN-taylor-lean (T0–T3)

Orchestration summary for `notes/algebraic/PLAN-taylor-lean.md`.
Task-level logs: `HANDOFF-taylor-T0.md`, `-T1.md`, `-T2.md`, `-T3.md`.

## Status: T0–T3 done, whole library green

`lake build` → `Build completed successfully (3957 jobs)`.
No `sorry`, no `axiom`, no `admit` anywhere under `Pptc/Taylor/`.
`lean_verify` on `realAlgebraic_Pconstructible_of_taylorTrinomial`,
`TrinomialLift.Pconstructible`, `PConstructible.of_unique_common_root`,
`PTowerReal.Pconstructible`, `trinomial_root_Pconstructible`,
`trinomial_root_pos_Pconstructible` → axioms `[propext, Classical.choice, Quot.sound]`.

## Files

| File | Task | Contents |
|---|---|---|
| `Pptc/Taylor/Field.lean` | T0 | `PReal : Subfield ℝ`; `SolvableReal`, `DegreeLE8Real`, `DegreeLE2Real`, `PTowerReal`; their `Pconstructible` wrappers; `Subfield.exists_map_eq_of_forall_coeff_mem`; `mobius_Pconstructible` |
| `Pptc/Taylor/Lift.lean` | T1 | `TrinomialLift`, `TrinomialLift.Pconstructible`, `PConstructible.of_unique_common_root` |
| `Pptc/Taylor/Statement.lean` | T2 | `TaylorTrinomial`, `SR`, `SR_8`, `SR_quad`, `SR_tower`, `SR_F`, `SR_tot`, `TrinomialReal`, `KTrSolvReal`; `TrinomialLift.mono`; implication diagram; conditional main theorem + 5 analogues |
| `Pptc/Taylor/Engine.lean` | T3 | `powGraph`, `affineLine`, `trinomial_root_Pconstructible`, `trinomial_root_pos_Pconstructible`, `trinomial_root_Pconstructible_of_lt` |
| `Pptc/Taylor/Main.lean` | — | imports all four; imported by `Pptc.lean` |

## Headline statements

```lean
theorem realAlgebraic_Pconstructible_of_taylorTrinomial (hTaylor : TaylorTrinomial) :
    ∀ β : ℝ, IsAlgebraic ℚ β → PConstructible β

theorem TrinomialLift.Pconstructible {Coord : ℝ → Prop}
    (hCoord : ∀ x, Coord x → PConstructible x) {β : ℝ}
    (h : TrinomialLift Coord β) : PConstructible β

-- no degree bound, no isolation, positive root only:
theorem trinomial_root_pos_Pconstructible {D : ℕ} (hD : 0 < D) {a b x : ℝ}
    (ha : PConstructible a) (hb : PConstructible b) (hx0 : 0 < x)
    (hne : (X ^ D + C a * X + C b : ℝ[X]) ≠ 0)
    (hx : x ^ D + a * x + b = 0) : PConstructible x
```

## Interface deviations from the plan (both forced/deliberate)

1. **`TrinomialLift` is `Type`-valued.** Lean refuses data-valued projections from a
   `Prop`-structure ("field must be a proof"), so §3.2's `structure … : Prop` is not
   expressible. The `Prop` layer is `Nonempty (TrinomialLift …)`, giving `SR`, `SR_8`,
   `SR_quad`, `SR_tower`, `SR_F`, `SR_tot`, `TaylorTrinomial`.
2. **`hinj` uses `Polynomial.eval`** on `q.map (algebraMap ℚ ℂ)` and
   `T.map (algebraMap ℝ ℂ)` instead of `aeval`; same statement, avoids `aeval`/`eval`
   transports in the recovery.

The recovery is proved through `minpoly PReal y₀`, **not** `Polynomial.gcd`: the minimal
polynomial divides both `q` and `T - x₀`, so all its conjugates are common roots; `hinj`
collapses them to `y₀`; separability plus a one-root/separable/`natDegree ≤ 1` argument
makes it linear. No `resultant`, no `gcd` computation.

`hroot`, `ha`, `hb` are *not used* by `TrinomialLift.Pconstructible`: they are geometric
input. `trinomial_root_pos_Pconstructible` even removes the need for `hx₀ : Coord x₀` when
the trinomial root is positive and the trinomial is nondegenerate — so a future revision of
`TrinomialLift` could weaken that field to `0 < x₀ ∧ trinomial ≠ 0`.

## Deliberately not proved (do not fake)

* `TaylorTrinomial → SR_tot`: nothing places an arbitrary solvable real in `Q^tr`.
* `SR_F → SR`: `FReal` records only "P and algebraic", not "solvable defining polynomial".
* T4 (`Geometry.lean`), T5 (concrete new unconditional β), T6 (point search) — open.

## Next steps, in order of expected value

1. **T5**: instantiate `TrinomialLift DegreeLE8Real β` (or `SolvableReal`) at a concrete
   `β`, following the shape `a, b, x₀, c, q, T, y₀` with `T = X` as a smoke test, then look
   for a `T ≠ X` case where `x₀ = T y₀` is genuinely *easier* to certify than `y₀` (that is
   where the lift beats `root_Pconstructible_deg8_coeffs`).
2. **Negative-root form** of the engine by reflecting `x ↦ -x` for odd `D`
   (`scale_x (-1)` / `scale_y (-1)` on `powGraph`).
3. **T4**: formalize `PSCForI` and derive `TaylorTrinomial`; this is the real frontier and
   should not block anything above.
