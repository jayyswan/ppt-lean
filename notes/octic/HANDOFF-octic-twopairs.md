# HANDOFF: Octic TwoPairs (`s ≥ 2` case)

File: `Pptc/Octic/TwoPairs.lean` (193 lines, created new; no existing file edited).
Imports: `Pptc.Octic.Cone`, `Pptc.Octic.Resolvent`.
Status: **compiles** (`lake build Pptc.Octic.TwoPairs` → "Build completed successfully"),
no `sorry`/`admit`/`axiom`, all lines ≤ 100 chars.

`lean_verify` on both headline declarations:
axioms = `propext, Classical.choice, Quot.sound` (trust: standard), no warnings.

## Declarations

```lean
-- Theorem: if a monic separable octic `q` with P-constructible coefficients has two
-- non-real roots `z, w` in distinct conjugate classes, then there is a nonzero
-- polynomial `φ` of degree `≤ 7` with P-constructible coefficients whose first three
-- trace power sums at `companionN (n := 8) q` vanish.
theorem exists_tschirnhaus_traces_two_pairs8 (q : ℝ[X]) (hmon : q.Monic)
    (hnat : q.natDegree = 8) (hsep : q.Separable) (hq : ∀ k, PConstructible (q.coeff k))
    {z w : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0) (hzim : z.im ≠ 0)
    (hw : (q.map (algebraMap ℝ ℂ)).eval w = 0) (hwim : w.im ≠ 0)
    (hzw : z ≠ w) (hzw' : z ≠ starRingEnd ℂ w) :
    ∃ φ : ℝ[X], (∀ k, PConstructible (φ.coeff k)) ∧ φ.natDegree ≤ 7 ∧ φ ≠ 0 ∧
      Matrix.trace (aeval (companionN (n := 8) q) φ) = 0 ∧
      Matrix.trace ((aeval (companionN (n := 8) q) φ) ^ 2) = 0 ∧
      Matrix.trace ((aeval (companionN (n := 8) q) φ) ^ 3) = 0

-- Theorem: a real root `β` of a monic separable octic `q` with P-constructible
-- coefficients and two non-real roots `z, w` in distinct conjugate classes is
-- P-constructible. This is the `s ≥ 2` case of the octic; the non-separable case is
-- handled in `Pptc/Octic/Main.lean`.
theorem root_Pconstructible_of_two_conjugate_pairs8 {q : ℝ[X]} (hmon : q.Monic)
    (hnat : q.natDegree = 8) (hsep : q.Separable) (hq : ∀ k, PConstructible (q.coeff k))
    {z w : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0) (hzim : z.im ≠ 0)
    (hw : (q.map (algebraMap ℝ ℂ)).eval w = 0) (hwim : w.im ≠ 0)
    (hzw : z ≠ w) (hzw' : z ≠ starRingEnd ℂ w) {β : ℝ} (hβ : q.eval β = 0) :
    PConstructible β
```

Namespace `Pconstructible`, `open Polynomial Matrix`, `noncomputable section`.

## Proof shape (port map from `DegreeSeven:4211`)

- `exists_cone_point8` (§ `Cone`), `neg_dir_of_pair8`, `pos_dir_of_pair8` (directions
  in `Fin 7 → ℝ`).
- `exists_orth_neg_PconstructibleN (n := 7) (A := Gram8 q) (Gram8_Pconstructible q hq) …`
  then the same with `(A := -Gram8 q)` and `fun i j => neg_Pconstructible …`;
  `bilin_neg` / `qform_neg` flip the sign back.
- `exists_isotropic_orth_Pconstructible8 q hq hQ₀ …` gives `x : Fin 7 → ℝ`.
- `cv : Fin 8 → ℝ := Lcomb8 q P₀`, `cw := Lcomb8 q x`; isotropy via
  `qform_Gram8_Lcomb8` (**note**: there is no `qform_Hmat8_Lcomb8`; the existing lemma
  `qform_Gram8_Lcomb8 : qform (Hmat8 q) (Lcomb8 q x) = qform (Gram8 q) x` is the one to
  use), orthogonality via `bilin_Hmat8_Lcomb8`, first moment via `p1vec8_Lcomb8`.
- `Ncv/Ncw := aeval (companionN (n := 8) q) (polyOfVec8 _)`; `aeval_entries_Pconstructible`
  with `companionN_entries_Pconstructible 8 q hq`.
- `binary_cubic_zero` on `a = p3vec8 q cv`, `b = 3 * Tr (Ncv² * Ncw)`,
  `c = 3 * Tr (Ncv * Ncw²)`, `d = p3vec8 q cw`.
- Non-degeneracy of `ψ = s • cv + t • cw` from
  `smul_add_smul_eq_zero_of_not_parallel` + `Lcomb8_injective`.
- Conclusion: `φ = polyOfVec8 ψ`; `polyOfVec8_natDegree_le` gives `≤ 7`;
  traces by `p1vec8_eq_trace` / `hermiteForm8_eq_trace_sq` /
  `qform_Hmat8_eq_hermiteForm8` and `trace_cube_smul_add8`.

## Notes / differences from the septic original

- `root_Pconstructible_of_two_conjugate_pairs8` assumes `hsep` (the septic version
  discharged non-separability itself); `Octic/Main.lean` handles the non-separable case.
- The tail lemma `root_Pconstructible_of_tschirnhaus8` lives in `Octic/Resolvent.lean`
  and is used directly (no resolvent re-derivation).
- Line-wrap needed at `hdefpos` (the `-Gram8` version is 106 chars on one line).
