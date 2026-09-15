/-
Scratch file for task B4 (legality of offset extractions + Lean infrastructure).
Imported by nothing. Never run `lake build`; checked through lean-lsp only.

Sections:
 1. Rationalization / norm lemmas (PROVED).
 2. Isolation-only crossing lemma (PROVED).
 3. Rational-curve recovery (generalisations of offsetParam_normal_eq_zero).
 4. Parabola offset is a rational curve (identity PROVED, set equality stated).
 5. Analytic finiteness for two arcs (stated).
 6. Headline statement shapes (stated).
-/
import Pptc.Offset
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Topology.Compactness.Compact

namespace Pconstructible

/-! ### 1. Rationalization / norm lemmas -/

/-- If `w ^ 2 = S` and `E + w * O = 0`, then the "norm" `E ^ 2 - S * O ^ 2` vanishes.
This is the algebraic content of clearing `w = √S` from a crossing equation. -/
theorem rationalize {E O w S : ℝ} (hS : w ^ 2 = S) (h : E + w * O = 0) :
    E ^ 2 - S * O ^ 2 = 0 := by
  have key : E ^ 2 - S * O ^ 2
      = (E + w * O) * (E - w * O) - O ^ 2 * (S - w ^ 2) := by ring
  rw [key, h, hS]
  ring

/-- The sign pattern of `offsetCrossVal`: `g * w = -(d * h)` with `w ^ 2 = S`
rationalizes to `g ^ 2 * S - d ^ 2 * h ^ 2 = 0`. This is exactly
`offsetCrossPoly` with `S = x' ^ 2 + y' ^ 2`. -/
theorem rationalize_mul {g h d w S : ℝ} (hS : w ^ 2 = S) (hcross : g * w + d * h = 0) :
    g ^ 2 * S - d ^ 2 * h ^ 2 = 0 := by
  have h' : (d * h) + w * g = 0 := by linarith
  have hnorm := rationalize (E := d * h) (O := g) (w := w) (S := S) hS h'
  nlinarith [hnorm]

/-- Generic form for an arbitrary polynomial in `w`: if every occurrence of `w ^ 2` is
folded into `S`, a vanishing `Σ cᵢ wⁱ` becomes `E + w * O = 0`, and then the norm
`E ^ 2 - S * O ^ 2` vanishes. Stated as a rewriting principle. -/
theorem rationalize_add_mul {E O w S : ℝ} (hS : w ^ 2 = S) (h : E + w * O = 0) :
    E ^ 2 = S * O ^ 2 := by
  have := rationalize hS h
  linarith

/-! ### 2. Isolation-only crossing lemma -/

-- Theorem: if two constructible curves have an isolated common point `(x₀, y₀)`, then
-- both its coordinates are P-constructible. Unlike `crossing_Pconstructible` this needs
-- neither a parametrization of the first curve nor finiteness of a zero set: only that
-- some ball around `(x₀, y₀)` meets `S ∩ T` in `(x₀, y₀)` alone. A rational box inside
-- that ball crops both curves to a unique crossing.
theorem crossing_PConstructible_of_isolated {S T : Set (ℝ × ℝ)}
    (hS : PConstructibleCurve S) (hT : PConstructibleCurve T) {x₀ y₀ : ℝ}
    (hS₀ : (x₀, y₀) ∈ S) (hT₀ : (x₀, y₀) ∈ T)
    (hiso : ∃ ε : ℝ, 0 < ε ∧ ∀ q ∈ S, q ∈ T → dist q (x₀, y₀) < ε →
      q = (x₀, y₀)) :
    PConstructible x₀ ∧ PConstructible y₀ := by
  obtain ⟨ε, hε, hiso⟩ := hiso
  obtain ⟨q₁, hq₁a, hq₁b⟩ := exists_rat_btwn (show x₀ - ε < x₀ by linarith)
  obtain ⟨q₂, hq₂a, hq₂b⟩ := exists_rat_btwn (show x₀ < x₀ + ε by linarith)
  obtain ⟨r₁, hr₁a, hr₁b⟩ := exists_rat_btwn (show y₀ - ε < y₀ by linarith)
  obtain ⟨r₂, hr₂a, hr₂b⟩ := exists_rat_btwn (show y₀ < y₀ + ε by linarith)
  have hS' := PConstructibleCurve.restrict hS (q₁ : ℝ) (q₂ : ℝ) (r₁ : ℝ) (r₂ : ℝ)
    (rat_Pconstructible q₁) (rat_Pconstructible q₂)
    (rat_Pconstructible r₁) (rat_Pconstructible r₂)
  have hT' := PConstructibleCurve.restrict hT (q₁ : ℝ) (q₂ : ℝ) (r₁ : ℝ) (r₂ : ℝ)
    (rat_Pconstructible q₁) (rat_Pconstructible q₂)
    (rat_Pconstructible r₁) (rat_Pconstructible r₂)
  have hsing : (S ∩ {q : ℝ × ℝ | (q₁ : ℝ) ≤ q.1 ∧ q.1 ≤ (q₂ : ℝ) ∧
        (r₁ : ℝ) ≤ q.2 ∧ q.2 ≤ (r₂ : ℝ)}) ∩
      (T ∩ {q : ℝ × ℝ | (q₁ : ℝ) ≤ q.1 ∧ q.1 ≤ (q₂ : ℝ) ∧
        (r₁ : ℝ) ≤ q.2 ∧ q.2 ≤ (r₂ : ℝ)}) = {((x₀, y₀) : ℝ × ℝ)} := by
    ext q
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨hqS, hb1, hb2, hb3, hb4⟩, hqT, -⟩
      have hdist : dist q (x₀, y₀) < ε := by
        rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq, abs_lt, abs_lt]
        exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
      exact hiso q hqS hqT hdist
    · rintro rfl
      exact ⟨⟨hS₀, hq₁b.le, hq₂a.le, hr₁b.le, hr₂a.le⟩, hT₀, hq₁b.le, hq₂a.le,
        hr₁b.le, hr₂a.le⟩
  exact ⟨PConstructible.inter_x hS' hT' hsing, PConstructible.inter_y hS' hT' hsing⟩

/-! ### 3. Rational-curve recovery

`offsetParam_normal_eq_zero` already holds for an *arbitrary* `γ`, hence for every
rational curve; the generalisation that matters is the *polynomial* normal equation
obtained by clearing the denominators of a proper rational parametrisation. -/

/-- The normal equation of `offsetParam` for a rational parametrization
`γ t = (P t / D t, Q t / D t)`, cleared of denominators. The un-cleared version is
`offsetParam_normal_eq_zero` with this `γ`; clearing uses
`deriv (P / D) = (P' D - P D') / D ^ 2`. -/
theorem normalEq_rat_eq_zero {P Q D : Polynomial ℝ} {X Y t : ℝ} (hD : D.eval t ≠ 0)
    (hγ : (X - P.eval t / D.eval t) * deriv (fun s => P.eval s / D.eval s) t
      + (Y - Q.eval t / D.eval t) * deriv (fun s => Q.eval s / D.eval s) t = 0) :
    (X * D.eval t - P.eval t) * (P.derivative.eval t * D.eval t - P.eval t * D.derivative.eval t)
      + (Y * D.eval t - Q.eval t)
        * (Q.derivative.eval t * D.eval t - Q.eval t * D.derivative.eval t) = 0 := by
  sorry

-- Theorem: the exact (degree-one-in-the-point) recovery equations for a rational
-- parametrization `γ t = (P t / D t, Q t / D t)`. Each is a polynomial in `t` of degree at
-- most the degree of the parametrization, with coefficients affine in `(X, Y)`.
-- `offsetParam_normal_eq_zero` says the vanishing combinations of these two equations
-- vanish at the crossing parameter, so this is the shape every recovery step has.
theorem rational_param_recovery {P Q D : Polynomial ℝ} {X Y t : ℝ} (hD : D.eval t ≠ 0)
    (hX : X = P.eval t / D.eval t) (hY : Y = Q.eval t / D.eval t) :
    (Polynomial.C X * D - P).eval t = 0 ∧ (Polynomial.C Y * D - Q).eval t = 0 := by
  constructor
  · simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, hX]
    field_simp
    ring
  · simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, hY]
    field_simp
    ring

/-- The degree bookkeeping behind `rational_param_recovery`: a proper rational
parametrization of degree at most `n` gives two recovery polynomials of degree at most `n`
whose coefficients are affine in the point. -/
theorem proper_rational_recovery_degree {P Q D : Polynomial ℝ} {n : ℕ} {X Y t : ℝ}
    (hP : P.natDegree ≤ n) (hQ : Q.natDegree ≤ n) (hDdeg : D.natDegree ≤ n)
    (hD : D.eval t ≠ 0) (hX : X = P.eval t / D.eval t) (hY : Y = Q.eval t / D.eval t) :
    (Polynomial.C X * D - P).natDegree ≤ n ∧
      (Polynomial.C Y * D - Q).natDegree ≤ n ∧
      (Polynomial.C X * D - P).eval t = 0 ∧ (Polynomial.C Y * D - Q).eval t = 0 := by
  sorry

-- Theorem: recovery through a chain. The hard part of a chain is producing the preimage `W`
-- of a crossing `Z` under an invertible affine map `L`; once `W = offsetParam γ d t` is
-- known, the normal equation of the *base* curve `γ` at `t` holds with `W` in place of the
-- offset point. That is exactly `offsetParam_normal_eq_zero`, and it needs no regularity.
theorem chain_recovery {γ : ℝ → ℝ × ℝ} {d t : ℝ} {W : ℝ × ℝ}
    (hW : W = offsetParam γ d t) :
    (W.1 - (γ t).1) * deriv (fun s => (γ s).1) t
      + (W.2 - (γ t).2) * deriv (fun s => (γ s).2) t = 0 := by
  rw [hW]
  exact offsetParam_normal_eq_zero γ d t

/-! ### 4. Parabola offset is a rational curve -/

/-- The parabola `y = x ^ 2`. -/
noncomputable def parabola (t : ℝ) : ℝ × ℝ := (t, t ^ 2)

/-- The offset of the parabola by `d`, reparametrized rationally in
`s = 2t + √(1 + 4t²)`. -/
noncomputable def parabolaOffsetRat (d s : ℝ) : ℝ × ℝ :=
  ((s ^ 2 - 1) / (4 * s) * (1 - 4 * d * s / (s ^ 2 + 1)),
   ((s ^ 2 - 1) / (4 * s)) ^ 2 + 2 * d * s / (s ^ 2 + 1))

@[simp] theorem parabola_fst (t : ℝ) : (parabola t).1 = t := rfl

@[simp] theorem parabola_snd (t : ℝ) : (parabola t).2 = t ^ 2 := rfl

theorem deriv_parabola_fst (t : ℝ) : deriv (fun s => (parabola s).1) t = 1 := by
  simp [parabola]

theorem deriv_parabola_snd (t : ℝ) : deriv (fun s => (parabola s).2) t = 2 * t := by
  have h : (fun s => (parabola s).2) = fun s : ℝ => s ^ 2 := rfl
  rw [h]
  simpa using (hasDerivAt_pow 2 t).deriv

theorem deriv_id_proj (t : ℝ) : deriv (fun s : ℝ => s) t = 1 := by simp

theorem deriv_sq_proj (t : ℝ) : deriv (fun s : ℝ => s ^ 2) t = 2 * t := by
  simpa using (hasDerivAt_pow 2 t).deriv

theorem speed_parabola (t : ℝ) : speed parabola t = Real.sqrt (1 + 4 * t ^ 2) := by
  rw [speed, deriv_parabola_fst, deriv_parabola_snd,
    show (1 : ℝ) ^ 2 + (2 * t) ^ 2 = 1 + 4 * t ^ 2 by ring]

theorem parabola_offset_sq_sub (t : ℝ) :
    (2 * t + Real.sqrt (1 + 4 * t ^ 2)) ^ 2 - 1
      = 4 * t * (2 * t + Real.sqrt (1 + 4 * t ^ 2)) := by
  have hsq : Real.sqrt (1 + 4 * t ^ 2) ^ 2 = 1 + 4 * t ^ 2 :=
    Real.sq_sqrt (by positivity)
  nlinarith [hsq]

theorem parabola_offset_sq_add (t : ℝ) :
    (2 * t + Real.sqrt (1 + 4 * t ^ 2)) ^ 2 + 1
      = 2 * (2 * t + Real.sqrt (1 + 4 * t ^ 2)) * Real.sqrt (1 + 4 * t ^ 2) := by
  have hsq : Real.sqrt (1 + 4 * t ^ 2) ^ 2 = 1 + 4 * t ^ 2 :=
    Real.sq_sqrt (by positivity)
  nlinarith [hsq]

theorem parabola_sqrt_pos (t : ℝ) : 0 < 2 * t + Real.sqrt (1 + 4 * t ^ 2) := by
  have hle : |2 * t| < Real.sqrt (1 + 4 * t ^ 2) := by
    rw [Real.lt_sqrt (by positivity), sq_abs]
    nlinarith
  have := (abs_lt.mp hle).1
  linarith

/-- The offset of the parabola is a rational curve: the substitution
`s = 2t + √(1 + 4t²)` (a bijection from `ℝ` onto `(0, ∞)`) makes `offsetParam` rational.
This is the identity content of A4's "the parabola has a rational offset". -/
theorem offsetParam_parabola (d t : ℝ) :
    offsetParam parabola d t
      = parabolaOffsetRat d (2 * t + Real.sqrt (1 + 4 * t ^ 2)) := by
  set s : ℝ := 2 * t + Real.sqrt (1 + 4 * t ^ 2) with hs
  set w : ℝ := Real.sqrt (1 + 4 * t ^ 2) with hw
  have hwpos : 0 < w := by rw [hw]; positivity
  have hsne : s ≠ 0 := by rw [hs]; exact ne_of_gt (parabola_sqrt_pos t)
  have hwne : w ≠ 0 := ne_of_gt hwpos
  have hsub : s ^ 2 - 1 = 4 * t * s := by
    rw [hs, hw]; exact parabola_offset_sq_sub t
  have hadd : s ^ 2 + 1 = 2 * s * w := by
    rw [hs, hw]; exact parabola_offset_sq_add t
  have hsp1 : s ^ 2 + 1 ≠ 0 := by positivity
  have ht : (s ^ 2 - 1) / (4 * s) = t := by
    field_simp
    linarith [hsub]
  have hsw4 : 4 * d * s / (s ^ 2 + 1) = 2 * d / w := by
    rw [hadd]
    field_simp
    ring
  have hsw2 : 2 * d * s / (s ^ 2 + 1) = d / w := by
    rw [hadd]
    field_simp
  have hsp : speed parabola t = w := by rw [hw]; exact speed_parabola t
  apply Prod.ext
  · simp only [offsetParam, unitNormal, hsp, deriv_id_proj, deriv_sq_proj,
      parabola_fst, parabola_snd, parabolaOffsetRat, ht, hsw4]
    ring
  · simp only [offsetParam, unitNormal, hsp, deriv_id_proj, deriv_sq_proj,
      parabola_fst, parabola_snd, parabolaOffsetRat, ht, hsw2]
    ring

/-! ### 5. Analytic finiteness for two arcs

The offset x offset crossing has no convenient implicit polynomial on the second side, so
the finiteness hypothesis of `crossing_Pconstructible` cannot be discharged by writing down
a polynomial. The replacement is analytic: two real-analytic arcs that are not identical
near a point meet only finitely often on a compact window.

Mathlib lemmas:
  * `AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero` (analytic continuation);
  * `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero` (zeros are isolated);
  * `Set.Infinite.exists_accPt_of_subset_isCompact` (accumulation point inside `Icc`);
  * `Real.contDiffAt_sqrt` / `ContDiffAt.sqrt` (the unit normal is analytic where regular).
-/

-- Theorem: a real-analytic function on a closed interval that is not identically zero there
-- has finitely many zeros. PROOF PLAN: an infinite zero set in the compact `Icc a b` has an
-- accumulation point there; analytic continuation forces `f = 0` on the preconnected
-- `Icc a b`, contradicting the hypothesis. STATED (sorry).
theorem finite_zeros_of_analyticOnNhd {f : ℝ → ℝ} {a b : ℝ}
    (hf : AnalyticOnNhd ℝ f (Set.Icc a b)) (hne : ∃ x ∈ Set.Icc a b, f x ≠ 0) :
    {t : ℝ | t ∈ Set.Icc a b ∧ f t = 0}.Finite := by
  sorry

-- Theorem: two analytic arcs that are not equal on all of `Icc a b` meet finitely often
-- in `Icc a b`. STATED (sorry).
theorem analytic_arcs_finite_meet {Γ₁ Γ₂ : ℝ → ℝ × ℝ} {a b : ℝ}
    (h₁ : AnalyticOnNhd ℝ (fun t => (Γ₁ t).1) (Set.Icc a b))
    (h₂ : AnalyticOnNhd ℝ (fun t => (Γ₁ t).2) (Set.Icc a b))
    (h₃ : AnalyticOnNhd ℝ (fun t => (Γ₂ t).1) (Set.Icc a b))
    (h₄ : AnalyticOnNhd ℝ (fun t => (Γ₂ t).2) (Set.Icc a b))
    (hne : ∃ x ∈ Set.Icc a b, Γ₁ x ≠ Γ₂ x) :
    {t : ℝ | t ∈ Set.Icc a b ∧ Γ₁ t = Γ₂ t}.Finite := by
  sorry

/-! ### 6. Headline statement shapes (all STATED, `sorry`) -/

-- H1 (offset x conic engine): the offset of a cubic pair crossed with a conic. `hnotid`
-- rules out the degenerate case in which the conic is crossed on a whole offset arc, which
-- is what makes `F ∘ Γ` have finitely many zeros; the conic keeps `F` of degree two.
theorem offsetConic_cross_root_PConstructible {T : Set (ℝ × ℝ)}
    (hT : PConstructibleCurve T) {F : ℝ → ℝ → ℝ}
    {c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃ d β : ℝ}
    (hc₀ : PConstructible c₀) (hc₁ : PConstructible c₁) (hc₂ : PConstructible c₂)
    (hc₃ : PConstructible c₃) (he₀ : PConstructible e₀) (he₁ : PConstructible e₁)
    (he₂ : PConstructible e₂) (he₃ : PConstructible e₃) (hd : PConstructible d)
    {a b c e f g : ℝ}
    (hF : ∀ X Y, F X Y = a * X ^ 2 + b * X * Y + c * Y ^ 2 + e * X + f * Y + g)
    (hTzero : ∀ q ∈ T, F q.1 q.2 = 0)
    (hnotid : ∃ s : ℝ, F (offsetParam (cubicPairParam c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃) d s).1
        (offsetParam (cubicPairParam c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃) d s).2 ≠ 0)
    (hreg : cubicDer c₁ c₂ c₃ β ≠ 0 ∨ cubicDer e₁ e₂ e₃ β ≠ 0)
    (hβT : offsetParam (cubicPairParam c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃) d β ∈ T) :
    PConstructible β := by
  sorry

-- H2 (offset x offset engine): two constructible curves meeting in an isolated point. This
-- is the isolation-only route; no implicit polynomial and no global finiteness are needed.
theorem offsetOffset_cross_isolated {S T : Set (ℝ × ℝ)}
    (hS : PConstructibleCurve S) (hT : PConstructibleCurve T) {x₀ y₀ : ℝ}
    (hS₀ : (x₀, y₀) ∈ S) (hT₀ : (x₀, y₀) ∈ T)
    (hiso : ∃ ε : ℝ, 0 < ε ∧ ∀ q ∈ S, q ∈ T → dist q (x₀, y₀) < ε →
      q = (x₀, y₀)) :
    PConstructible x₀ ∧ PConstructible y₀ :=
  crossing_PConstructible_of_isolated hS hT hS₀ hT₀ hiso

-- H3 (degree-`N` family covered): the degree-10 engine of `Pptc.Offset`, restated as the
-- template for a "whole degree covered" theorem: every real solution of
-- `x(β)·√(x'(β)² + y'(β)²) = d·y'(β)` for a cubic pair `(x, y)` and P-constructible `d`.
theorem degreeTenFamily_covered {c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃ d : ℝ}
    (hc₀ : PConstructible c₀) (hc₁ : PConstructible c₁) (hc₂ : PConstructible c₂)
    (hc₃ : PConstructible c₃) (he₀ : PConstructible e₀) (he₁ : PConstructible e₁)
    (he₂ : PConstructible e₂) (he₃ : PConstructible e₃) (hd : PConstructible d)
    (hlead : c₃ ≠ 0) {β : ℝ}
    (hreg : cubicDer c₁ c₂ c₃ β ≠ 0 ∨ cubicDer e₁ e₂ e₃ β ≠ 0)
    (hcross : cubicVal c₀ c₁ c₂ c₃ β
        * Real.sqrt (cubicDer c₁ c₂ c₃ β ^ 2 + cubicDer e₁ e₂ e₃ β ^ 2)
      = d * cubicDer e₁ e₂ e₃ β) :
    PConstructible β := by
  sorry

end Pconstructible


