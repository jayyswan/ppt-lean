# HANDOFF: octic sextic along stereographic line

**Status: COMPLETE.** `lake build Pptc.Octic.Sextic` succeeds (2944 jobs, 15s, no
warnings). `lean_verify` on `Pconstructible.exists_sextic_along_line8` reports axioms
`[propext, Classical.choice, Quot.sound]`, `trust: standard`, no `sorryAx`.

File: `Pptc/Octic/Sextic.lean` (293 lines, all lines ≤ 100 chars). Import: `Pptc.Octic.Cone`.
No existing file touched.

## Declarations (all in `namespace Pconstructible`, `noncomputable section`)

Private helpers (dimension-free copies of DegreeSeven 3726-3768):

```lean
private theorem coeff_add_Pc {p r : ℝ[X]}
    (hp : ∀ k, PConstructible (p.coeff k)) (hr : ∀ k, PConstructible (r.coeff k)) :
    ∀ k, PConstructible ((p + r).coeff k)

private theorem coeff_sub_Pc {p r : ℝ[X]}
    (hp : ∀ k, PConstructible (p.coeff k)) (hr : ∀ k, PConstructible (r.coeff k)) :
    ∀ k, PConstructible ((p - r).coeff k)

private theorem coeff_X_Pc : ∀ k, PConstructible (((X : ℝ[X])).coeff k)

private theorem coeff_X_sq_Pc : ∀ k, PConstructible (((X : ℝ[X]) ^ 2).coeff k)

private theorem natDegree_C_le' (a : ℝ) : (C a : ℝ[X]).natDegree ≤ 0

private theorem natDegree_lin_le (a b : ℝ) :
    (C a + C b * X : ℝ[X]).natDegree ≤ 1

private theorem natDegree_quad_le (a b c : ℝ) :
    (C a + C b * X + C c * X ^ 2 : ℝ[X]).natDegree ≤ 2
```

Public:

```lean
theorem exists_sextic_along_line8 (q : ℝ[X]) (hq : ∀ k, PConstructible (q.coeff k))
    {P₀ d δ : Fin 7 → ℝ} (hP₀ : ∀ i, PConstructible (P₀ i))
    (hd : ∀ i, PConstructible (d i)) (hδ : ∀ i, PConstructible (δ i)) :
    ∃ Ψ : ℝ[X], (∀ k, PConstructible (Ψ.coeff k)) ∧ Ψ.natDegree ≤ 6 ∧
      ∀ m : ℝ, Ψ.eval m = p3vec8 q (Lcomb8 q (stereoN (Gram8 q) P₀ (d + m • δ)))

theorem continuous_Lcomb8 (q : ℝ[X]) :
    Continuous (fun v : Fin 7 → ℝ => Lcomb8 q v)

theorem continuous_Phi8 (q : ℝ[X]) (P₀ : Fin 7 → ℝ) :
    Continuous (fun d : Fin 7 → ℝ => p3vec8 q (Lcomb8 q (stereoN (Gram8 q) P₀ d)))

theorem stereoN_Pconstructible (q : ℝ[X]) (hq : ∀ k, PConstructible (q.coeff k))
    {P₀ d : Fin 7 → ℝ} (hP₀ : ∀ i, PConstructible (P₀ i))
    (hd : ∀ i, PConstructible (d i)) :
    ∀ i, PConstructible (stereoN (Gram8 q) P₀ d i)
```

## Port notes
- `stComp : Fin 7 → ℝ[X]`; `lineVec : Fin 8 → ℝ[X] := fun i => ∑ j : Fin 7, stComp j * C (bvec8 q j i)`.
- `Ψ := ∑ i : Fin 8, ∑ j : Fin 8, ∑ k : Fin 8, (lineVec i * lineVec j * lineVec k) *
    C (Matrix.trace ((companionN (n := 8) q) ^ (i.val + j.val + k.val)))`.
- Coefficient closure via `trace_pow_companion8_Pconstructible`, `bvec8_Pconstructible`,
  `Gram8_Pconstructible`; degree bound still `≤ 6`.
- Generic `bilin`/`qform` lemmas (`qform_smul_add`, `bilin_add_right`, `bilin_smul_right`,
  `coeff_*_Pconstructible`, `Finset.sum_Pconstructible`) come from `Pptc.DegreeSeven`, which
  `Pptc.Octic.Cone` transitively imports — no local copies needed.
- `stereoN`, `continuous_stereoN` from `Pptc.Octic.Cone` (generic in `n`, used at `n := 7`).

## Log
- created; read PLAN §2.6, DegreeSeven 3714-3940/3993-4022, Cone, TraceForm
- wrote full Sextic.lean port (5 public decls + 7 private helpers)
- `lean_diagnostic_messages`: clean (0 diagnostics); `lean_file_outline` confirms all signatures
- `lake build Pptc.Octic.Sextic`: success; `lean_verify`: standard axioms, no sorryAx
- no remaining issues
