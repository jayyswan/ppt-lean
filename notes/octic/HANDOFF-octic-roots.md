# HANDOFF: `Pptc/Octic/Roots.lean`

**Status: DONE.** `lake build Pptc.Octic.Roots` → "Build completed successfully (2942 jobs)".
`#print axioms` on every declaration: `[propext, Classical.choice, Quot.sound]` — no `sorryAx`.
No `sorry` / `admit` / `axiom`. All lines ≤ 100 codepoints. No files edited except the new one.

Imports: `Pptc.Octic.TraceForm` only. Namespace `Pconstructible`, `open Polynomial Matrix`,
`noncomputable section`. 16-line project header copied from `Pptc/TotallyReal/Engines.lean`.

## Declarations (exact signatures)

### helper (added, see deviations)

```lean
theorem companionN_trace_aeval8 (q F : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 8)
    (hsep : q.Separable) :
    algebraMap ℝ ℂ (Matrix.trace (aeval (companionN (n := 8) q) F))
      = ((q.map (algebraMap ℝ ℂ)).roots.map
          (fun z => (F.map (algebraMap ℝ ℂ)).eval z)).sum
```

### 1. Lagrange interpolation

```lean
theorem exists_poly_value_at_root8 (q : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 8)
    (hsep : q.Separable) {z : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0)
    (hzim : z.im ≠ 0) (c : ℂ) :
    ∃ f : ℝ[X], f.natDegree ≤ 7 ∧
      (f.map (algebraMap ℝ ℂ)).eval z = c ∧
      (f.map (algebraMap ℝ ℂ)).eval (starRingEnd ℂ z) = starRingEnd ℂ c ∧
      ∀ x : ℂ, (q.map (algebraMap ℝ ℂ)).eval x = 0 → x ≠ z → x ≠ starRingEnd ℂ z →
        (f.map (algebraMap ℝ ℂ)).eval x = 0
```

### 2. Trace consequences

```lean
theorem algebraMap_trace_eq_of_value8 (q : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 8)
    (hsep : q.Separable) {z : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0)
    (hzim : z.im ≠ 0) (F : ℝ[X]) (c : ℂ)
    (hFz : (F.map (algebraMap ℝ ℂ)).eval z = c)
    (hFother : ∀ x : ℂ, (q.map (algebraMap ℝ ℂ)).eval x = 0 → x ≠ z →
      x ≠ starRingEnd ℂ z → (F.map (algebraMap ℝ ℂ)).eval x = 0) :
    algebraMap ℝ ℂ (Matrix.trace (aeval (companionN (n := 8) q) F)) = c + starRingEnd ℂ c

theorem trace_aeval_eq_zero_of_vanishes8 (q : ℝ[X]) (hmon : q.Monic)
    (hnat : q.natDegree = 8) (hsep : q.Separable) (F : ℝ[X])
    (hF : ∀ x : ℂ, (q.map (algebraMap ℝ ℂ)).eval x = 0 →
      (F.map (algebraMap ℝ ℂ)).eval x = 0) :
    algebraMap ℝ ℂ (Matrix.trace (aeval (companionN (n := 8) q) F)) = 0

theorem trace_eq_of_value8 (q : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 8)
    (hsep : q.Separable) {z : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0)
    (hzim : z.im ≠ 0) {f : ℝ[X]} {c : ℂ}
    (hfz : (f.map (algebraMap ℝ ℂ)).eval z = c)
    (hfother : ∀ x : ℂ, (q.map (algebraMap ℝ ℂ)).eval x = 0 → x ≠ z →
      x ≠ starRingEnd ℂ z → (f.map (algebraMap ℝ ℂ)).eval x = 0) :
    Matrix.trace (aeval (companionN (n := 8) q) f) = 2 * c.re ∧
      Matrix.trace ((aeval (companionN (n := 8) q) f) ^ 2) = 2 * (c ^ 2).re

theorem exists_value_trace8 (q : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 8)
    (hsep : q.Separable) {z : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0)
    (hzim : z.im ≠ 0) (c : ℂ) :
    ∃ f : ℝ[X], f.natDegree ≤ 7 ∧
      Matrix.trace (aeval (companionN (n := 8) q) f) = 2 * c.re ∧
      Matrix.trace ((aeval (companionN (n := 8) q) f) ^ 2) = 2 * (c ^ 2).re

theorem exists_neg_trace8 (q : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 8)
    (hsep : q.Separable) {z : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0)
    (hzim : z.im ≠ 0) :
    ∃ f : ℝ[X], f.natDegree ≤ 7 ∧ Matrix.trace (aeval (companionN (n := 8) q) f) = 0 ∧
      Matrix.trace ((aeval (companionN (n := 8) q) f) ^ 2) = -2

theorem exists_pos_trace8 (q : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 8)
    (hsep : q.Separable) {z : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0)
    (hzim : z.im ≠ 0) :
    ∃ f : ℝ[X], f.natDegree ≤ 7 ∧ Matrix.trace (aeval (companionN (n := 8) q) f) = 2 ∧
      Matrix.trace ((aeval (companionN (n := 8) q) f) ^ 2) = 2
```

### 3. Two conjugate pairs

```lean
theorem exists_value_pair8 (q : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 8)
    (hsep : q.Separable) {z w : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0)
    (hzim : z.im ≠ 0) (hw : (q.map (algebraMap ℝ ℂ)).eval w = 0) (hwim : w.im ≠ 0)
    (hzw : z ≠ w) (hzw' : z ≠ starRingEnd ℂ w) (c : ℂ) :
    ∃ f g : ℝ[X], f.natDegree ≤ 7 ∧ g.natDegree ≤ 7 ∧
      Matrix.trace (aeval (companionN (n := 8) q) f) = 2 * c.re ∧
      Matrix.trace (aeval (companionN (n := 8) q) g) = 2 * c.re ∧
      Matrix.trace ((aeval (companionN (n := 8) q) f) ^ 2) = 2 * (c ^ 2).re ∧
      Matrix.trace ((aeval (companionN (n := 8) q) g) ^ 2) = 2 * (c ^ 2).re ∧
      Matrix.trace ((aeval (companionN (n := 8) q) f)
        * (aeval (companionN (n := 8) q) g)) = 0

theorem exists_neg_pair8 (q : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 8)
    (hsep : q.Separable) {z w : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0)
    (hzim : z.im ≠ 0) (hw : (q.map (algebraMap ℝ ℂ)).eval w = 0) (hwim : w.im ≠ 0)
    (hzw : z ≠ w) (hzw' : z ≠ starRingEnd ℂ w) :
    ∃ f g : ℝ[X], f.natDegree ≤ 7 ∧ g.natDegree ≤ 7 ∧
      Matrix.trace (aeval (companionN (n := 8) q) f) = 0 ∧
      Matrix.trace (aeval (companionN (n := 8) q) g) = 0 ∧
      Matrix.trace ((aeval (companionN (n := 8) q) f) ^ 2) = -2 ∧
      Matrix.trace ((aeval (companionN (n := 8) q) g) ^ 2) = -2 ∧
      Matrix.trace ((aeval (companionN (n := 8) q) f)
        * (aeval (companionN (n := 8) q) g)) = 0

theorem exists_pos_pair8 (q : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 8)
    (hsep : q.Separable) {z w : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0)
    (hzim : z.im ≠ 0) (hw : (q.map (algebraMap ℝ ℂ)).eval w = 0) (hwim : w.im ≠ 0)
    (hzw : z ≠ w) (hzw' : z ≠ starRingEnd ℂ w) :
    ∃ f g : ℝ[X], f.natDegree ≤ 7 ∧ g.natDegree ≤ 7 ∧
      Matrix.trace (aeval (companionN (n := 8) q) f) = 2 ∧
      Matrix.trace (aeval (companionN (n := 8) q) g) = 2 ∧
      Matrix.trace ((aeval (companionN (n := 8) q) f) ^ 2) = 2 ∧
      Matrix.trace ((aeval (companionN (n := 8) q) g) ^ 2) = 2 ∧
      Matrix.trace ((aeval (companionN (n := 8) q) f)
        * (aeval (companionN (n := 8) q) g)) = 0
```

### 4. Root decomposition

```lean
theorem roots_eq_pair_add_real8 (q : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 8)
    (hsep : q.Separable) {z : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0)
    (hzim : z.im ≠ 0)
    (hone : ∀ w : ℂ, (q.map (algebraMap ℝ ℂ)).eval w = 0 → w.im ≠ 0 →
      w = z ∨ w = starRingEnd ℂ z) :
    ∃ R : Multiset ℝ, R.Nodup ∧ R.card = 6 ∧
      (q.map (algebraMap ℝ ℂ)).roots
        = z ::ₘ starRingEnd ℂ z ::ₘ (R.map (algebraMap ℝ ℂ))
```

## Deviations

1. **One extra helper declaration**, `companionN_trace_aeval8`: the degree-free form of the
   spectral identity (trace of `aeval`, not of a power). It is `companionN_trace_pow_aeval8`
   at `k = 1` closed with `simpa`, and plays exactly the role `companion7_trace_aeval` played
   in `Pptc.DegreeSeven`. Required names are otherwise exactly as requested.
2. `roots_eq_pair_add_real8` takes `q` as an **explicit** `(q : ℝ[X])` binder, as specified
   (note `DegreeSeven.roots_eq_pair_add_real` makes it implicit, so call sites of the
   septic version do not transfer verbatim — add `q` as the first argument there).
3. Wrapping only: some statements are line-broken differently from `DegreeSeven` (the
   `companionN (n := 8) q` applications are longer than `companion7 q`), and docstrings/
   comments were rewritten for degree 8. No statement content differs otherwise.
4. Reused (not redefined) from `Pptc.DegreeSeven`: `conjQuad`, `conjQuad_monic`,
   `conjQuad_natDegree`, `conjQuad_eval_map`, `conjQuad_dvd_of_root`,
   `conjQuad_map_eq_prod`, `eval_map_conj`, `exists_linear_eval`,
   `multiset_sum_eq_two_of_vanish`.

## Constant check

`natDegree = 7 → 8` everywhere; `G.natDegree = 5 → 6`; all `natDegree ≤ 6 → ≤ 7`;
`R.card = 5 → 6`; `nonR.card = 2` unchanged; `qC.roots.card = 7 → 8`;
`2 * c.re`, `-2`, `2` trace targets unchanged; `companion7 q → companionN (n := 8) q`.

## Log

- [start] read `DegreeSeven.lean` 460-960 and 2650-2750, `Octic/TraceForm.lean`, `PLAN.md` §2.4
- [1] wrote `Pptc/Octic/Roots.lean` (all 11 required declarations + 1 helper)
- [2] `lean_diagnostic_messages`: no diagnostics
- [3] `lake build Pptc.Octic.Roots`: success (2942 jobs)
- [4] `#print axioms` on all 12 declarations via a temp file: standard 3 only; temp file deleted
- [5] line-length check (UTF-8 codepoints): max ≤ 100
