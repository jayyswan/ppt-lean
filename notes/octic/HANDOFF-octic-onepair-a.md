# Octic OnePair — part A (complete)

File: `Pptc/Octic/OnePair.lean` (500 lines). Imports: `Pptc.Octic.Sextic`,
`Pptc.Octic.Resolvent`. Header copied from `Pptc/TotallyReal/Engines.lean`.
`open Polynomial Matrix`, `namespace Pconstructible`, `noncomputable section`.

**Status: compiles clean.** `lake env lean Pptc/Octic/OnePair.lean` → exit 0, zero diagnostics.
`lean_verify` on both headline theorems: axioms `propext, Classical.choice, Quot.sound`.
No `sorry`/`admit`/`axiom`. All lines ≤ 100 chars.
The file ends with exactly:

```
end

end Pconstructible

/-! ### Part B: sign change and assembly (to be appended) -/
```

Nothing after the banner. Part B must re-open `namespace Pconstructible` /
`noncomputable section` itself.

## Declarations in part A (all in `namespace Pconstructible`)

```lean
theorem exists_lagrange_value8 {q : ℝ[X]} (hmon : q.Monic) (hnat : q.natDegree = 8)
    (hsep : q.Separable) {z : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0)
    (hzim : z.im ≠ 0)
    (hone : ∀ w : ℂ, (q.map (algebraMap ℝ ℂ)).eval w = 0 → w.im ≠ 0 →
      w = z ∨ w = starRingEnd ℂ z)
    {x : ℝ} (hx : q.eval x = 0) (hxz : (x : ℂ) ≠ z) (hxz' : (x : ℂ) ≠ starRingEnd ℂ z)
    {c : ℂ} (hc1 : c + starRingEnd ℂ c = -1) (hc2 : c * starRingEnd ℂ c = 1) :
    ∃ X : ℝ[X], X.natDegree ≤ 7 ∧
      (X.map (algebraMap ℝ ℂ)).eval z = c ∧
      (X.map (algebraMap ℝ ℂ)).eval (starRingEnd ℂ z) = starRingEnd ℂ c ∧
      X.eval x = 1 ∧
      (∀ r : ℝ, q.eval r = 0 → r ≠ x → X.eval r = 0) ∧
      Matrix.trace (aeval (companionN (n := 8) q) X) = 0 ∧
      Matrix.trace ((aeval (companionN (n := 8) q) X) ^ 2) = 0 ∧
      Matrix.trace ((aeval (companionN (n := 8) q) X) ^ 3) = 3
```

```lean
private lemma vecOf8_polyOfVec8 (v : Fin 8 → ℝ) : vecOf8 (polyOfVec8 v) = v
private lemma eval_map_ofReal (f : ℝ[X]) (r : ℝ) :
    (f.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ r) = ((f.eval r : ℝ) : ℂ)
private lemma eval_C_mul_add (F G : ℝ[X]) (z : ℂ) (a b : ℝ) :
    (((C a * F + C b * G).map (algebraMap ℝ ℂ)).eval z)
      = (a : ℂ) * ((F.map (algebraMap ℝ ℂ)).eval z)
        + (b : ℂ) * ((G.map (algebraMap ℝ ℂ)).eval z)
private theorem sum_sq_add_pair_re8 {q H : ℝ[X]} (hmon : q.Monic) (hnat : q.natDegree = 8)
    (hsep : q.Separable) {z : ℂ} {R : Multiset ℝ}
    (hroots : (q.map (algebraMap ℝ ℂ)).roots
      = z ::ₘ starRingEnd ℂ z ::ₘ (R.map (algebraMap ℝ ℂ)))
    (htrace : Matrix.trace ((aeval (companionN (n := 8) q) H) ^ 2) = 0) :
    (R.map (fun r => (H.eval r) ^ 2)).sum
      + 2 * ((((H.map (algebraMap ℝ ℂ)).eval z) ^ 2).re) = 0
lemma eq_zero_of_vanishes_on_roots8 {q H : ℝ[X]} (hnat : q.natDegree = 8) (hsep : q.Separable)
    (hHdeg : H.natDegree ≤ 7)
    (h : ∀ w : ℂ, w ∈ (q.map (algebraMap ℝ ℂ)).roots →
      (H.map (algebraMap ℝ ℂ)).eval w = 0) : H = 0
theorem isotropic_plane_trivial8 {q : ℝ[X]} (hmon : q.Monic) (hnat : q.natDegree = 8)
    (hsep : q.Separable) {z : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0)
    (hzim : z.im ≠ 0)
    (hone : ∀ w : ℂ, (q.map (algebraMap ℝ ℂ)).eval w = 0 → w.im ≠ 0 →
      w = z ∨ w = starRingEnd ℂ z) :
    ∀ x y : Fin 7 → ℝ, qform (Gram8 q) x = 0 → qform (Gram8 q) y = 0 →
      bilin (Gram8 q) x y = 0 → y ≠ 0 → ∃ c : ℝ, x = c • y
```

## Notes for part B

- **`ofReal_multiset_sum` is NOT redefined.** The degree-free version already exists, public,
  in `Pptc.DegreeSeven` (`namespace Pconstructible`), with exactly the wanted signature
  `(R : Multiset ℝ) (F : ℝ → ℝ) : (R.map (fun r => (F r : ℂ))).sum = ((R.map F).sum : ℝ)`. A
  duplicate copy triggers "has already been declared". Just use the name.
- `roots_eq_pair_add_real8` takes `q` **explicitly** as its first argument
  (`roots_eq_pair_add_real8 q hmon hnat hsep hz hzim hone`).
- The `private` helpers above are still usable **inside this same file**, so part B can call
  `sum_sq_add_pair_re8`, `eval_C_mul_add`, `eval_map_ofReal`, `vecOf8_polyOfVec8` directly.
- The trace chain in `isotropic_plane_trivial8` is shorter than the septic one: I used
  `qform_Gram8_eq_trace_sq` directly instead of the 3-step
  `hermiteForm8_eq_trace_sq` / `qform_Hmat8_eq_hermiteForm8` / `qform_Gram8_Lcomb8` chain
  (both are available). Reuse the same shortcut wherever the septic code built that chain.
- `polyOfVec8_smul_add` has statement
  `polyOfVec8 (a • vecOf8 f + b • vecOf8 g) = C a * f + C b * g` (rewrite with `←`).
- Available and confirmed-compiling from imports: `Gram8`, `Hmat8`, `coeff7`, `Lcomb8`
  (`Lcomb8_smul_add`, `Lcomb8_smul`, `Lcomb8_sub`, `Lcomb8_injective`, `Lcomb8_coeff7`),
  `polyOfVec8`, `vecOf8`, `polyOfVec8_natDegree_le`, `polyOfVec8_ne_zero`,
  `polyOfVec8_vecOf8`, `polyOfVec8_smul_add`, `p1vec8`, `p3vec8`, `svec8`,
  `qform_Gram8_Lcomb8`, `qform_Gram8_eq_trace_sq`, `qform_Hmat8_eq_hermiteForm8`,
  `hermiteForm8_eq_trace_sq`, `bilin_Gram8_Lcomb8`, `Gram8_symm`, generic `qform_smul_add`
  / `qform_add` / `bilin_comm` (polymorphic in `n`, from `DegreeSeven`),
  `companionN_trace_pow_aeval8`, `companionN_trace_aeval8`, `trace_aeval_eq_zero_of_vanishes8`,
  `trace_eq_of_value8`, `exists_value_trace8`, `exists_neg_trace8`, `exists_pos_trace8`,
  `roots_eq_pair_add_real8`, `eval_map_conj` (DegreeSeven, `Pconstructible` namespace).
