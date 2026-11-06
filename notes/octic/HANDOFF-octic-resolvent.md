# HANDOFF: Pptc.Octic.Resolvent

## Goal
Create `Pptc/Octic/Resolvent.lean` (PLAN §2.3, Part B) for the octic resolvent /
Newton step and the Tschirnhaus tail.

## Status
- [x] file written
- [x] `lake build Pptc.Octic.Resolvent` succeeds
- [x] axiom check: standard 3 axioms only, no `sorryAx`, no `sorry`/`admit`/`axiom`

## Deliverable
`C:\dev\Powerpoint\lean\pptc\Pptc\Octic\Resolvent.lean`
Imports: `Pptc.TotallyReal.Main`, `Pptc.Octic.Engine`.
Namespace `Pconstructible`, `open Polynomial Matrix`, `noncomputable section`.

## Declarations (all in `Pconstructible`)

1. `companionN_trace_pow_aeval_eight` (helper; TraceForm is not imported, so the
   standard 16-line header + module docstring + this port of
   `companionN_trace_pow_aeval8` are local)
```lean
theorem companionN_trace_pow_aeval_eight (q φ : ℝ[X]) (hmon : q.Monic)
    (hnat : q.natDegree = 8) (hsep : q.Separable) (k : ℕ) :
    algebraMap ℝ ℂ (Matrix.trace ((aeval (companionN (n := 8) q) φ) ^ k))
      = ((q.map (algebraMap ℝ ℂ)).roots.map
          (fun z => ((φ.map (algebraMap ℝ ℂ)).eval z) ^ k)).sum
```

2. `companionN'_charpoly_aeval_eq_prod8` (helper; YSpace has no generic version,
   so this is a port of `companion7'_charpoly_aeval_eq_prod`)
```lean
theorem companionN'_charpoly_aeval_eq_prod8 {K : Type*} [Field K] [IsAlgClosed K]
    (q φ : K[X]) (hmon : q.Monic) (hnat : q.natDegree = 8) (hsep : q.Separable) :
    (aeval (companionN' (n := 8) q) φ).charpoly
      = (q.roots.map (fun z => Polynomial.X - Polynomial.C (φ.eval z))).prod
```

3. `charpoly_aeval_coeff_7_6_5_eq_zero`
```lean
theorem charpoly_aeval_coeff_7_6_5_eq_zero {q φ : ℝ[X]} (hmon : q.Monic)
    (hnat : q.natDegree = 8) (hsep : q.Separable)
    (hp1 : Matrix.trace (aeval (companionN (n := 8) q) φ) = 0)
    (hp2 : Matrix.trace ((aeval (companionN (n := 8) q) φ) ^ 2) = 0)
    (hp3 : Matrix.trace ((aeval (companionN (n := 8) q) φ) ^ 3) = 0) :
    (aeval (companionN (n := 8) q) φ).charpoly.coeff 7 = 0 ∧
    (aeval (companionN (n := 8) q) φ).charpoly.coeff 6 = 0 ∧
    (aeval (companionN (n := 8) q) φ).charpoly.coeff 5 = 0
```

4. `resolvent_quarticPowerLaw`
```lean
theorem resolvent_quarticPowerLaw {q φ : ℝ[X]} {β : ℝ}
    (hq : ∀ k, PConstructible (q.coeff k)) (hβ : q.eval β = 0) (h8 : q.coeff 8 = 1)
    (hdeg : q.natDegree ≤ 8) (hφ : ∀ k, PConstructible (φ.coeff k))
    (hkill : (aeval (companionN (n := 8) q) φ).charpoly.coeff 7 = 0 ∧
             (aeval (companionN (n := 8) q) φ).charpoly.coeff 6 = 0 ∧
             (aeval (companionN (n := 8) q) φ).charpoly.coeff 5 = 0) :
    ∃ c₀ c₁ c₂ c₃ c₄ : ℝ, PConstructible c₀ ∧ PConstructible c₁ ∧
      PConstructible c₂ ∧ PConstructible c₃ ∧ PConstructible c₄ ∧
      (φ.eval β) ^ 8 = quarticVal c₀ c₁ c₂ c₃ c₄ (φ.eval β)
```

5. `natDegree_ne_zero_of_trace_zero8`
```lean
theorem natDegree_ne_zero_of_trace_zero8 {q φ : ℝ[X]}
    (hp1 : Matrix.trace (aeval (companionN (n := 8) q) φ) = 0) (hφne : φ ≠ 0) :
    φ.natDegree ≠ 0
```

6. `eval_root_Pconstructible8` (helper, as permitted by the task)
```lean
theorem eval_root_Pconstructible8 {φ : Polynomial ℝ}
    (hcoeff : ∀ i, PConstructible (φ.coeff i)) (hdeg : φ.natDegree ≤ 7)
    (hne : φ.natDegree ≠ 0) {β y : ℝ} (hy : PConstructible y)
    (h : φ.eval β = y) : PConstructible β
```

7. `root_Pconstructible_of_tschirnhaus8`
```lean
theorem root_Pconstructible_of_tschirnhaus8 {q φ : ℝ[X]} (hmon : q.Monic)
    (hnat : q.natDegree = 8) (hsep : q.Separable) (hq : ∀ k, PConstructible (q.coeff k))
    (hφc : ∀ k, PConstructible (φ.coeff k)) (hφdeg : φ.natDegree ≤ 7) (hφne : φ ≠ 0)
    (hp1 : Matrix.trace (aeval (companionN (n := 8) q) φ) = 0)
    (hp2 : Matrix.trace ((aeval (companionN (n := 8) q) φ) ^ 2) = 0)
    (hp3 : Matrix.trace ((aeval (companionN (n := 8) q) φ) ^ 3) = 0)
    {β : ℝ} (hβ : q.eval β = 0) : PConstructible β
```

## Deviations
- The actual tool catalog has no `axiom_check`; used `lean_verify` per declaration.
  All four headline theorems report `["propext", "Classical.choice", "Quot.sound"]`.
- Two local helpers were added because `Octic/TraceForm.lean` is intentionally not
  imported (PLAN §2.3) and `YSpace` has no `companionN'` charpoly-product lemma.
- `eval_root_Pconstructible8` takes `hne : φ.natDegree ≠ 0` (matching the septic
  `eval_root_Pconstructible`), not `φ ≠ 0`; the tail supplies it through
  `natDegree_ne_zero_of_trace_zero8`.

## Verification
- `lake build Pptc.Octic.Resolvent` → "Build completed successfully (2946 jobs)".
- `lean_diagnostic_messages` on the file: empty.
- No lines > 100 chars; LF line endings (matching `Octic/Engine.lean`); no `sorry`.
