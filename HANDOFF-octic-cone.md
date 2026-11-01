# HANDOFF: `Pptc/Octic/Cone.lean`

**Status: DONE.** File created, `lake build Pptc.Octic.Cone` succeeds (2943 jobs, 16 s),
no `sorry`/`admit`/`axiom`, no lines > 100 chars, LF endings as in the rest of
`Pptc/Octic/`. `lean_verify` on the headline declarations reports only
`propext`, `Classical.choice`, `Quot.sound` (`trust: standard`).

- Target file: `pptc/Pptc/Octic/Cone.lean`
- Import: `Pptc.Octic.Roots`
- `open Polynomial Matrix` / `namespace Pconstructible` / `noncomputable section`
- Module docstring `/-! # Pptc.Octic.Cone` describes signature `(7-s, s)`, the light
  cone `{Q = 0}`, its stereographic parametrisation, and the P-constructible cone point /
  isotropic orthogonal vector construction.
- Every theorem has a `-- Theorem: …` line.

## Declarations (exact signatures as elaborated)

### A. Dimension-free (`Fin n`)

```lean
def stereoN {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (P₀ x : Fin n → ℝ) : Fin n → ℝ :=
  qform A x • P₀ - (2 * bilin A P₀ x) • x

theorem qform_stereoN_eq_zero {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : Aᵀ = A)
    {P₀ : Fin n → ℝ} (hP₀ : qform A P₀ = 0) (x : Fin n → ℝ) :
    qform A (stereoN A P₀ x) = 0

theorem stereoN_smul_add_smul {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : Aᵀ = A)
    {P₀ : Fin n → ℝ} (hP₀ : qform A P₀ = 0) (c ε : ℝ) (δ : Fin n → ℝ) :
    stereoN A P₀ (c • P₀ + ε • δ) = ε ^ 2 • stereoN A P₀ δ

theorem exists_orth_projectionN {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, PConstructible (A i j)) {P₀ : Fin n → ℝ}
    (hP₀ : ∀ i, PConstructible (P₀ i)) :
    ∃ (c : ℝ) (u : Fin n → ℝ), c ≠ 0 ∧ PConstructible c ∧
      (∀ i, PConstructible (u i)) ∧
      ∀ y, bilin A P₀ (c • y - bilin A P₀ y • u) = 0

theorem exists_orth_neg_PconstructibleN {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, PConstructible (A i j)) {P₀ : Fin n → ℝ}
    (hP₀ : ∀ i, PConstructible (P₀ i)) {v₁ v₂ : Fin n → ℝ}
    (hdef : ∀ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) → qform A (a • v₁ + b • v₂) < 0) :
    ∃ e : Fin n → ℝ, (∀ i, PConstructible (e i)) ∧ bilin A P₀ e = 0 ∧
      qform A e < 0

theorem continuous_stereoN {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (P₀ : Fin n → ℝ) :
    Continuous (fun d : Fin n → ℝ => stereoN A P₀ d)
```

Reused generic lemmas (not redefined): `qform`, `bilin`, `qform_eq_sum`,
`qform_eq_bilin`, `qform_smul`, `qform_smul_add`, `qform_neg`, `bilin_comm`,
`bilin_add_left/right`, `bilin_smul_left/right`, `bilin_sum_left/right`,
`bilin_Pconstructible`, `bilin_smul_smul`, `continuous_qform`, `continuous_bilin`,
`exists_rat_vec_pos`, `exists_pos_quadratic_root`, `rat_Pconstructible`,
`zero_Pconstructible`.

### B. Octic-specific (`Fin 7`, `Gram8 q`)

```lean
theorem neg_dir_of_pair8 (q : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 8)
    (hsep : q.Separable) {z w : ℂ}
    (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0) (hzim : z.im ≠ 0)
    (hw : (q.map (algebraMap ℝ ℂ)).eval w = 0) (hwim : w.im ≠ 0)
    (hzw : z ≠ w) (hzw' : z ≠ starRingEnd ℂ w) :
    ∃ v1 v2 : Fin 7 → ℝ,
      ∀ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) → qform (Gram8 q) (a • v1 + b • v2) < 0

theorem pos_dir_of_pair8 (q : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 8)
    (hsep : q.Separable) {z w : ℂ}
    (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0) (hzim : z.im ≠ 0)
    (hw : (q.map (algebraMap ℝ ℂ)).eval w = 0) (hwim : w.im ≠ 0)
    (hzw : z ≠ w) (hzw' : z ≠ starRingEnd ℂ w) :
    ∃ v1 v2 : Fin 7 → ℝ,
      ∀ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) → 0 < qform (Gram8 q) (a • v1 + b • v2)

theorem exists_pos_isotropic_param8 (q : ℝ[X]) (hq : ∀ k, PConstructible (q.coeff k))
    {e f : Fin 7 → ℝ} (he : ∀ i, PConstructible (e i)) (hf : ∀ i, PConstructible (f i))
    (heQ : qform (Gram8 q) e < 0) (hfQ : 0 < qform (Gram8 q) f) :
    ∃ t : ℝ, PConstructible t ∧ 0 < t ∧ qform (Gram8 q) (e + t • f) = 0

theorem exists_isotropic_Pconstructible8 (q : ℝ[X]) (hq : ∀ k, PConstructible (q.coeff k))
    {e f : Fin 7 → ℝ} (he : ∀ i, PConstructible (e i)) (hf : ∀ i, PConstructible (f i))
    (heQ : qform (Gram8 q) e < 0) (hfQ : 0 < qform (Gram8 q) f) :
    ∃ P₀ : Fin 7 → ℝ,
      (∀ i, PConstructible (P₀ i)) ∧ qform (Gram8 q) P₀ = 0 ∧ P₀ ≠ 0

theorem exists_cone_point8 (q : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 8)
    (hsep : q.Separable) (hq : ∀ k, PConstructible (q.coeff k)) {z : ℂ}
    (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0) (hzim : z.im ≠ 0) :
    ∃ P₀ : Fin 7 → ℝ,
      (∀ i, PConstructible (P₀ i)) ∧ qform (Gram8 q) P₀ = 0 ∧ P₀ ≠ 0

theorem exists_isotropic_orth_Pconstructible8 (q : ℝ[X])
    (hq : ∀ k, PConstructible (q.coeff k))
    {P₀ e f : Fin 7 → ℝ} (hQ₀ : qform (Gram8 q) P₀ = 0)
    (he : ∀ i, PConstructible (e i)) (hf : ∀ i, PConstructible (f i))
    (hBe : bilin (Gram8 q) P₀ e = 0) (hBf : bilin (Gram8 q) P₀ f = 0)
    (heQ : qform (Gram8 q) e < 0) (hfQ : 0 < qform (Gram8 q) f) :
    ∃ x : Fin 7 → ℝ, (∀ i, PConstructible (x i)) ∧ qform (Gram8 q) x = 0 ∧
      bilin (Gram8 q) P₀ x = 0 ∧ ¬ ∃ k : ℝ, x = k • P₀
```

## Notes / constants that changed from the septic version

| Septic (`DegreeSeven`) | Octic (`Cone.lean`) | Where |
|---|---|---|
| `stereo` (`Fin 6`) | `stereoN` (`Fin n`) | A.1 |
| `C (2 / 7)` mean shift | `C (2 / 8)` | `pos_dir_of_pair8` |
| `trace_sq_sub_scalar` `… + c^2 * 7` | `trace_sq_sub_scalar8` `… + c^2 * 8` | reused from `TraceForm` |
| `aeval_sub_C` (`companion7`) | `aeval_sub_C8` (`companionN (n := 8)`) | reused |
| `aeval_sub_C_smul_add` | `aeval_sub_C_smul_add8` | reused |
| `coeff6` / `vecOf` / `Lcomb` / `p1vec` | `coeff7` / `vecOf8` / `Lcomb8` / `p1vec8` | everywhere |
| `qform_Hmat_eq_hermiteForm` + `hermiteForm_eq_trace_sq` | `qform_Gram8_eq_trace_sq` | `exists_cone_point8` |
| `c^2 * 7` positivity value `10/7` | `3 / 2` | `exists_cone_point8` |
| `exists_rat_vec_pos 6` | `exists_rat_vec_pos 7` | `exists_cone_point8` |

Arithmetic check for `exists_cone_point8`: with `gpos = fpos - C (2/8)` and
`Tr(fpos) = Tr(fpos²) = 2`,
`Tr(gpos²) = 2 - 2*(2/8)*2 + (2/8)²*8 = 2 - 1 + 1/2 = 3/2`. ✓
Negative branch unchanged: `Tr(fneg²) = -2`. ✓

`pos_dir_of_pair8` final inequality: with mean shift `c = 2/8 = 1/4`,
`Q(a•v1 + b•v2) = 2a² + 2b² - 2·((a+b)/4)·(2a+2b) + ((a+b)/4)²·8`
`= (3a² - 2ab + 3b²)/2 > 0` for `(a,b) ≠ 0` (discriminant `4 - 36 < 0`).

## Remaining issues

None. Nothing outside `Pptc/Octic/Cone.lean` was modified.
