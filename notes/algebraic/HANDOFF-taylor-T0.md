# HANDOFF — Taylor T0 (`Pptc/Taylor/Field.lean`)

**Status: DONE** — file compiles, builds, zero `sorry`, zero non-standard axioms.

## Deliverable

New file `Pptc/Taylor/Field.lean` (7282 bytes, LF). No other file was modified.
(`git status`: `Pptc/Taylor/` is new/untracked; `notes/algebraic/HANDOFF-taylor-T0.md`
is new; nothing tracked was touched.)

Imports (targeted):

```lean
import Pptc.Basic
import Pptc.Octic.Main
import Pptc.Solvable.Main
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.FieldTheory.Minpoly.Field
```

Everything is in `namespace Pconstructible`, `open Polynomial`, `noncomputable section`,
with an Apache header matching `Pptc/Solvable/Main.lean` and a `/-! # ... -/` module
docstring.

## Declarations added (exact signatures as elaborated)

```lean
def PReal : Subfield ℝ                                    -- carrier = {x | PConstructible x}

@[simp] theorem mem_PReal {x : ℝ} : x ∈ PReal ↔ PConstructible x

theorem PReal.Pconstructible {x : ℝ} (h : x ∈ PReal) : PConstructible x
theorem PConstructible.mem_PReal {x : ℝ} (h : PConstructible x) : x ∈ PReal

@[simp] theorem PReal.coe_algebraMap (x : PReal) : (algebraMap PReal ℝ x : ℝ) = x

theorem Subfield.exists_map_eq_of_forall_coeff_mem (K : Subfield ℝ) {p : ℝ[X]}
    (h : ∀ i, p.coeff i ∈ K) : ∃ p' : K[X], p'.map (algebraMap K ℝ) = p
-- NOTE: declared with a `_root_.` prefix, so the full name is
-- `Subfield.exists_map_eq_of_forall_coeff_mem` (NOT `Pconstructible.Subfield.…`).

def SolvableReal (x : ℝ) : Prop :=
  ∃ q : ℚ[X], q ≠ 0 ∧ Group.IsSolvable q.Gal ∧ aeval x q = 0

def DegreeLE8Real (x : ℝ) : Prop :=
  ∃ q : ℚ[X], q ≠ 0 ∧ q.natDegree ≤ 8 ∧ aeval x q = 0

def DegreeLE2Real (x : ℝ) : Prop :=
  ∃ q : ℚ[X], q ≠ 0 ∧ q.natDegree ≤ 2 ∧ aeval x q = 0

inductive PTowerReal : ℝ → Prop
  | rat (q : ℚ) : PTowerReal (q : ℝ)
  | root8 {p : ℝ[X]} (hp : p ≠ 0) (hdeg : p.natDegree ≤ 8)
      (hcoeff : ∀ i, PTowerReal (p.coeff i)) {x : ℝ} (hx : p.eval x = 0) : PTowerReal x
  | solvable {q : ℚ[X]} (hq : q ≠ 0) (h : Group.IsSolvable q.Gal)
      {x : ℝ} (hx : aeval x q = 0) : PTowerReal x

theorem SolvableReal.Pconstructible {x : ℝ} (h : SolvableReal x) : PConstructible x
theorem DegreeLE8Real.Pconstructible {x : ℝ} (h : DegreeLE8Real x) : PConstructible x
theorem DegreeLE2Real.Pconstructible {x : ℝ} (h : DegreeLE2Real x) : PConstructible x
theorem PTowerReal.Pconstructible {x : ℝ} (h : PTowerReal x) : PConstructible x

theorem mobius_Pconstructible {a b c d x : ℝ} (hx : PConstructible x)
    (ha : PConstructible a) (hb : PConstructible b) (hc : PConstructible c)
    (hd : PConstructible d) : PConstructible ((a * x + b) / (c * x + d))
```

All names/signatures are exactly as required by the task brief. Proof bodies:

- `SolvableReal.Pconstructible` → `root_Pconstructible_of_solvable_gal`.
- `DegreeLE8Real.Pconstructible` → `root_Pconstructible_deg8_coeffs` applied to
  `q.map (algebraMap ℚ ℝ)`; degree bound from `Polynomial.natDegree_map_le.trans hdeg`,
  root transfer via `rw [← Polynomial.eval₂_eq_eval_map]`, coefficients via
  `Polynomial.coeff_map` + `rat_Pconstructible`.
- `DegreeLE2Real.Pconstructible` → `DegreeLE8Real.Pconstructible` + `omega` (plain term,
  no tactic block needed).
- `PTowerReal.Pconstructible` → `induction h with` (three cases).
- `mobius_Pconstructible` → explicit `PConstructible.div/add/mul` term (no
  nonzero-denominator hypothesis; the docstring says why).

## Lemma-name / elaborator gotchas found (v4.33)

1. **`∑ i in s, f` does not parse** in this toolchain ("unexpected token 'in'").
   Use `∑ i ∈ s, f` (which is what `Polynomial.as_sum_range_C_mul_X_pow` is stated
   with). No other file in the project uses a big-operator binder, so this was
   invisible until now.
2. **`Polynomial.as_sum_range_C_mul_X_pow` cannot be used with a bare `rw`**: rw rejects
   the rewrite because the LHS pattern is a metavariable (`Invalid rewrite argument:
   The pattern to be substituted is a metavariable`). Working proof tail (as in the file):
   ```lean
   refine ⟨∑ i ∈ Finset.range (p.natDegree + 1), C ⟨p.coeff i, h i⟩ * X ^ i, ?_⟩
   rw [Polynomial.map_sum]
   simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X]
   conv_rhs => rw [Polynomial.as_sum_range_C_mul_X_pow p]
   rfl
   ```
   (The `rfl` closes the goal because `algebraMap K ℝ ⟨p.coeff i, _⟩` is
   definitionally `p.coeff i`. Plain `rw [Polynomial.as_sum_range_C_mul_X_pow p]` at
   top level also fails — "motive is not type correct" — because it rewrites the `p`
   inside `p.coeff i` and `h i`; `conv_rhs` targets only the right-hand side.)
3. **`PTowerReal` recursor**: `Pconstructible.PTowerReal.rec` *is* generated and *does*
   carry the nested induction hypothesis `∀ i, motive (p.coeff i) …` for `hcoeff`, but
   that IH is the **last** explicit argument of the `root8` minor premise, i.e. *after*
   `hx`. The correct pattern is
   `| root8 hp hdeg hcoeff hx ih => …`. Naming only four binders silently binds
   `hcoeff` to the name you meant for the IH.
4. `Subfield` field order/labels are as the brief said:
   `carrier, zero_mem', one_mem', add_mem', mul_mem', neg_mem', inv_mem'`, with
   `inv_mem' : ∀ x ∈ carrier, x⁻¹ ∈ carrier` (two explicit arguments).
5. `Polynomial.natDegree_map_eq_of_injective` was *not* needed: `natDegree_map_le`
   suffices for a `≤ 8` bound and avoids the injectivity plumbing.
6. `Polynomial.eval₂_eq_eval_map` (used right-to-left) is the clean way to turn
   `aeval x q = 0` into `(q.map (algebraMap ℚ ℝ)).eval x = 0`.
7. `linter.dupNamespace` fires on every mandated name (`PReal.Pconstructible`,
   `SolvableReal.Pconstructible`, …) because the final component repeats the ambient
   namespace. Silenced at the top of the file with a one-line comment
   (`set_option linter.dupNamespace false`); all other linters are silent.

## Verification

- `lean_diagnostic_messages` on `Pptc/Taylor/Field.lean`: **success, zero items**
  (no errors, no warnings, no `sorry`).
- `grep -E "sorry|admit|axiom"` on the file: no matches.
- `lake build Pptc.Taylor.Field` (from `C:\dev\Powerpoint\lean\pptc`):
  ```
  ✔ [2969/2969] Built Pptc.Taylor.Field (13s)
  Build completed successfully (2969 jobs).
  ```
  The only warnings printed during the build come from pre-existing files
  (`Pptc/Solvable/AbelRuffini.lean`, `linter.style.haveILetI`); none from this file.
- `lean_verify` (axiom check) on all eight key declarations — `PReal`,
  `PReal.coe_algebraMap`, `Subfield.exists_map_eq_of_forall_coeff_mem`,
  `SolvableReal.Pconstructible`, `DegreeLE8Real.Pconstructible`,
  `DegreeLE2Real.Pconstructible`, `PTowerReal.Pconstructible`,
  `mobius_Pconstructible` — reports
  `axioms = [propext, Classical.choice, Quot.sound]`, `trust: standard`,
  `non_standard_axioms: []` for each. **No `sorryAx`.**

## Deviations from the brief

- The lifting lemma is declared as `_root_.Subfield.exists_map_eq_of_forall_coeff_mem`
  so that its full name is the required `Subfield.exists_map_eq_of_forall_coeff_mem`
  rather than `Pconstructible.Subfield.…`. (Inside `namespace Pconstructible` a bare
  `theorem Subfield.…` would have been prefixed.)
- One file-level `set_option linter.dupNamespace false` added (see gotcha 7); the
  declaration names themselves are unchanged.
- No `sorry` anywhere; nothing else was left out.
