# T3 — the trinomial engine (`Pptc/Taylor/Engine.lean`)

**Status: done, zero sorries.** One new file, `Pptc/Taylor/Engine.lean`, importing
`Pptc.Basic` only. No existing file was touched. `lake build Pptc.Taylor.Engine` succeeds
(2787 jobs, 16 s, everything up to date) and `lean_verify` on each declaration below reports
`axioms = [propext, Classical.choice, Quot.sound]`, `trust = standard` — no `sorryAx`.

## Declarations added

All in namespace `Pconstructible`.

### 1. The requested engine (window form)

```lean
theorem trinomial_root_Pconstructible {D : ℕ} (hD : 0 < D) {a b l r x : ℝ}
    (ha : PConstructible a) (hb : PConstructible b)
    (hl : PConstructible l) (hr : PConstructible r)
    (hl0 : 0 < l) (hlr : l ≤ r)
    (hx : x ^ D + a * x + b = 0) (hxI : l ≤ x ∧ x ≤ r)
    (huniq : ∀ y : ℝ, l ≤ y → y ≤ r → y ^ D + a * y + b = 0 → y = x) :
    PConstructible x
```

Statement is verbatim the one requested.

### 2. The requested open-window variant

```lean
theorem trinomial_root_Pconstructible_of_lt {D : ℕ} (hD : 0 < D) {a b l r x : ℝ}
    (ha : PConstructible a) (hb : PConstructible b)
    (hl : PConstructible l) (hr : PConstructible r)
    (hl0 : 0 < l) (hlr : l ≤ r)
    (hx : x ^ D + a * x + b = 0) (hxI : l ≤ x ∧ x ≤ r)
    (huniq : ∀ y : ℝ, l < y → y < r → y ^ D + a * y + b = 0 → y = x) :
    PConstructible x
```

### 3. Bonus: the engine with no isolation hypothesis at all

```lean
theorem trinomial_root_pos_Pconstructible {D : ℕ} (hD : 0 < D) {a b x : ℝ}
    (ha : PConstructible a) (hb : PConstructible b) (hx0 : 0 < x)
    (hne : (Polynomial.X ^ D + Polynomial.C a * Polynomial.X + Polynomial.C b :
      Polynomial ℝ) ≠ 0)
    (hx : x ^ D + a * x + b = 0) :
    PConstructible x
```

Private helpers (all with docstrings): `powGraph`, `affineLine`, `power_law_one_set`,
`powGraph_PConstructibleCurve`, `affineLine_PConstructibleCurve`.

## Proof of the window engine (as outlined)

1. `powGraph D := {p | 0 ≤ p.1 ∧ p.2 = p.1 ^ D}`. `power_law_one_set` shows the raw
   `power_law 1 D` set — with its `0 < pt.1 ∨ (pt.1 = 0 ∧ 0 < (D:ℚ))` domain and rational
   real-power — is exactly `powGraph D`; the two ingredients are `Real.rpow_natCast` and
   `exact_mod_cast hD` for `0 < (D:ℚ)`.
2. `affineLine a b := {p | p.2 = -(a * p.1) - b}` is built as the image of `poly_graph X`
   under `scale_y (-a)` then `translate_y (-b)`; both image sets are identified by `ext`
   with `Prod.mk.inj` on the existential.
3. Crop **only the line** to `[l, r] × [-(r ^ D + 1), r ^ D + 1]` (`PConstructibleCurve.restrict`;
   the four bounds are `hl`, `hr` and `±(r ^ D + 1)` from `pow_Pconstructible`). The power
   curve needs no cropping: it already carries `x ≥ 0`, and the window alone is what isolates
   the root. This is one `restrict` fewer than the sketch.
4. The intersection with `powGraph D` is `{(x, x ^ D)}`: forward, a common point gives
   `v = u ^ D`, `v = -(a*u) - b`, `l ≤ u ≤ r`, hence `u ^ D + a*u + b = 0`, hence `u = x`;
   backward, `0 ≤ x` and `-(r^D+1) ≤ x^D ≤ r^D+1` follow from `0 ≤ x ≤ r` by
   `pow_nonneg` / `pow_le_pow_left₀`.
5. `PConstructible.inter_x` reads off `x`.

## Deviations / notes

* **Declaration 3 is an addition**, not requested. It is what makes declaration 2 cheap, and
  it is mathematically the interesting point: *the isolation window is removable*. The
  trinomial has finitely many roots, so all other crossings `(t, t ^ D)` are finitely many
  points and a rational box around `(x, x ^ D)` excludes them — `crossing_Pconstructible`
  (already in `Pptc.Basic`) then returns both coordinates. The nondegeneracy hypothesis is
  necessary: at `D = 1, a = -1, b = 0` the trinomial is the zero polynomial and no root is
  determined by the others. For `D ≥ 2` the coefficient of `X ^ D` is `1`, so `hne` is
  automatic for any caller who wants a window-free version at degree ≥ 2.
* **Declaration 2 is proved from declaration 3, not from the closed-window engine**, because
  the closed form genuinely cannot yield it: `t ^ 3 - t` on `[-1, 1]` has `x = 0` as its only
  root in the open interval while `±1` are also roots, so closed-window uniqueness fails. The
  degenerate window `l = r` is handled separately (then `x` is the endpoint `l`, hence P).
  For that reason `hr : PConstructible r` is unused in declaration 2 and the declaration
  carries `set_option linter.unusedVariables false in` with a comment saying so. (The
  open-window form does not need the right endpoint to be P-constructible.)
* No `l = 0` variant was added (per instructions).
* Imports: `Pptc.Basic` only — the Taylor classes of `Pptc.Taylor.Field` are not needed.

## Files

* new: `Pptc/Taylor/Engine.lean`
* progress log: `HANDOFF-taylor-T3.md` (repo root)
* this report

## Verification log

* `lean_diagnostic_messages` on `Pptc/Taylor/Engine.lean`: empty (no errors, no warnings).
* `lake build Pptc.Taylor.Engine`: "Build completed successfully (2787 jobs)".
* `lean_verify`:
  * `Pconstructible.trinomial_root_Pconstructible` → standard 3 axioms, `trust: standard`
  * `Pconstructible.trinomial_root_pos_Pconstructible` → standard 3 axioms, `trust: standard`
  * `Pconstructible.trinomial_root_Pconstructible_of_lt` → standard 3 axioms, `trust: standard`
* `rg 'sorry|admit|axiom'` on the file: no matches.
