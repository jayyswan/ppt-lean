# HANDOFF: Taylor T2 — `Statement.lean` + `Main.lean`

**Status: DONE.** All declarations compile, the whole library builds, and the headline
declarations have no `sorryAx` in their axiom list.

| item | value |
|---|---|
| new file | `Pptc/Taylor/Statement.lean` (261 lines) |
| new file | `Pptc/Taylor/Main.lean` (imports + module summary) |
| edited file | `Pptc.lean` (+1 line: `import Pptc.Taylor.Main` after `import Pptc.Solvable.Main`) |
| untouched | `Pptc/Taylor/Field.lean`, `Pptc/Taylor/Lift.lean` |

## Build output

```
lake build Pptc.Taylor.Statement   ✔ [2971/2971] Built Pptc.Taylor.Statement (14s)
                                   Build completed successfully (2971 jobs).
lake build Pptc.Taylor.Main        ✔ [2972/2972] Built Pptc.Taylor.Main (11s)
                                   Build completed successfully (2972 jobs).
lake build            (whole lib)  Build completed successfully (3956 jobs).
```

`lean_diagnostic_messages` on both new files: **zero** items (no errors, no warnings).

Axiom check (`lean_verify`; the `axiom_check` tool does not exist in this environment, and
`lean_verify` works here because the file has a built `.olean`). For each of

* `Pconstructible.realAlgebraic_Pconstructible_of_taylorTrinomial`
* `Pconstructible.realAlgebraic_Pconstructible_of_SR`
* `Pconstructible.SR_8.Pconstructible`
* `Pconstructible.SR_F.Pconstructible`
* `Pconstructible.SR_tot.Pconstructible`

the axiom list is `[propext, Classical.choice, Quot.sound]`, `trust: standard`,
`non_standard_axioms: []`, and the source scan reports no warnings. **No `sorryAx`.**

## Declarations (all in `namespace Pconstructible`)

### §1 point-existence predicates

```lean
def TaylorTrinomial : Prop :=
  ∀ β : ℝ, IsAlgebraic ℚ β → Nonempty (TrinomialLift SolvableReal β)
def SR (β : ℝ) : Prop := Nonempty (TrinomialLift SolvableReal β)
def SR_8 (β : ℝ) : Prop := Nonempty (TrinomialLift DegreeLE8Real β)
def SR_quad (β : ℝ) : Prop := Nonempty (TrinomialLift DegreeLE2Real β)
def SR_tower (β : ℝ) : Prop := Nonempty (TrinomialLift PTowerReal β)
def FReal (x : ℝ) : Prop := PConstructible x ∧ IsAlgebraic ℚ x
def SR_F (β : ℝ) : Prop := Nonempty (TrinomialLift FReal β)
```

### §2 monotonicity

```lean
def TrinomialLift.mono {Coord Coord' : ℝ → Prop} (h : ∀ x, Coord x → Coord' x)
    {β : ℝ} (hl : TrinomialLift Coord β) : TrinomialLift Coord' β
```

### §3 coordinate-class inclusions

```lean
theorem SolvableReal.toPTowerReal {x : ℝ} (h : SolvableReal x) : PTowerReal x
theorem DegreeLE2Real.toDegreeLE8Real {x : ℝ} (h : DegreeLE2Real x) : DegreeLE8Real x
theorem DegreeLE8Real.toPTowerReal {x : ℝ} (h : DegreeLE8Real x) : PTowerReal x
theorem FReal.Pconstructible {x : ℝ} (h : FReal x) : PConstructible x
```

### §4 hierarchy implications

```lean
theorem SR_quad.toSR_8 {β : ℝ} (h : SR_quad β) : SR_8 β
theorem SR_8.toSR_tower {β : ℝ} (h : SR_8 β) : SR_tower β
theorem SR.toSR_tower {β : ℝ} (h : SR β) : SR_tower β
theorem SR_F.toP {β : ℝ} (h : SR_F β) : PConstructible β
theorem SR.Pconstructible {β : ℝ} (h : SR β) : PConstructible β
theorem SR_8.Pconstructible {β : ℝ} (h : SR_8 β) : PConstructible β
theorem SR_quad.Pconstructible {β : ℝ} (h : SR_quad β) : PConstructible β
theorem SR_tower.Pconstructible {β : ℝ} (h : SR_tower β) : PConstructible β
theorem SR_F.Pconstructible {β : ℝ} (h : SR_F β) : PConstructible β
```

### §5 conditional main theorems

```lean
theorem realAlgebraic_Pconstructible_of_taylorTrinomial (hTaylor : TaylorTrinomial) :
    ∀ β : ℝ, IsAlgebraic ℚ β → PConstructible β
theorem realAlgebraic_Pconstructible_of_SR
    (h : ∀ β : ℝ, IsAlgebraic ℚ β → SR β) : ∀ β : ℝ, IsAlgebraic ℚ β → PConstructible β
theorem realAlgebraic_Pconstructible_of_SR_8
    (h : ∀ β : ℝ, IsAlgebraic ℚ β → SR_8 β) : ∀ β : ℝ, IsAlgebraic ℚ β → PConstructible β
theorem realAlgebraic_Pconstructible_of_SR_quad
    (h : ∀ β : ℝ, IsAlgebraic ℚ β → SR_quad β) : ∀ β : ℝ, IsAlgebraic ℚ β → PConstructible β
theorem realAlgebraic_Pconstructible_of_SR_tower
    (h : ∀ β : ℝ, IsAlgebraic ℚ β → SR_tower β) : ∀ β : ℝ, IsAlgebraic ℚ β → PConstructible β
theorem realAlgebraic_Pconstructible_of_SR_F
    (h : ∀ β : ℝ, IsAlgebraic ℚ β → SR_F β) : ∀ β : ℝ, IsAlgebraic ℚ β → PConstructible β
```

### §6 the trinomial-field row

```lean
inductive TrinomialReal : ℝ → Prop
  | rat (q : ℚ) : TrinomialReal (q : ℝ)
  | root {n : ℕ} (hn : 0 < n) {a b : ℚ} {x : ℝ} (hx : x ^ n + a * x + b = 0) : TrinomialReal x
  | add {x y} : TrinomialReal x → TrinomialReal y → TrinomialReal (x + y)
  | neg {x} : TrinomialReal x → TrinomialReal (-x)
  | mul {x y} : TrinomialReal x → TrinomialReal y → TrinomialReal (x * y)
  | inv {x} : TrinomialReal x → TrinomialReal (x⁻¹)

def KTrSolvReal (x : ℝ) : Prop := TrinomialReal x ∧ SolvableReal x
def SR_tot (β : ℝ) : Prop := Nonempty (TrinomialLift KTrSolvReal β)
theorem SR_tot.toSR {β : ℝ} (h : SR_tot β) : SR β
theorem SR_tot.Pconstructible {β : ℝ} (h : SR_tot β) : PConstructible β
```

## Deviations from the brief

1. **`TrinomialLift.mono` is a `def`, not a `theorem`.** `TrinomialLift Coord β` is
   `Type`-valued, so `theorem` is rejected by the kernel
   (`type of theorem ... is not a proposition`). The name, signature and body are exactly
   as specified; only the keyword changed (`Main.lean` merely names it, without claiming
   it is a theorem).
2. **`TaylorTrinomial.toSR_tot` and `FReal.toSolvableReal` are omitted**, as instructed in
   the brief (§6 and §3 respectively: neither is formal).
3. **`SR_F.toP` and `SR_F.Pconstructible` are both provided** (the brief lists both); the
   latter delegates to the former.
4. `DegreeLE8Real.toPTowerReal` proves `p.eval x = 0` via
   `rw [← Polynomial.eval₂_eq_eval_map]; exact hx`, exactly mirroring
   `DegreeLE8Real.Pconstructible` in `Field.lean`, instead of using
   `Polynomial.eval_map_algebraMap` (both are equivalent; the chosen route is the one
   already known to work in this file).

## Gotchas / notes for later tasks

* `set_option linter.dupNamespace false` is required in `Statement.lean` because of
  `SR.Pconstructible`, `SR_8.Pconstructible`, `SR_F.Pconstructible`, `SR_tot.Pconstructible`
  (the ambient namespace `Pconstructible` appears again at the end of the name). This
  matches `Field.lean` / `Lift.lean`.
* `SolvableReal x` is an `∃`; use `obtain ⟨q, hq, hsol, hx⟩ := h` before applying
  `PTowerReal.solvable`. Do **not** try `h.1`/`h.2.1` directly — `h.1` is the polynomial.
* `TrinomialLift.Pconstructible` expects its coordinate predicate as an *explicit*
  argument: `hl.Pconstructible (fun _ hx => ...)`, not `hl.Pconstructible Coord.Pconstructible`
  (the latter relies on implicit-to-explicit promotion, which is fragile). All nine
  `.Pconstructible` wrappers use the explicit lambda form.
* `TrinomialReal.root` needs `0 < n`; with `n = 0` the equation degenerates and the
  closure properties (`add`, `mul`, …) would then be derivable for free, so the positive
  exponent is load-bearing for the intended meaning.
* Everything downstream that wants a concrete instance should supply
  `∀ β, IsAlgebraic ℚ β → SR_quad β` (easiest search target, plan §5.2) and apply
  `realAlgebraic_Pconstructible_of_SR_quad`.
