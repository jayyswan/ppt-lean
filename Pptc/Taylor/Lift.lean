/-
Copyright (c) 2024 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pptc contributors
-/

import Pptc.Taylor.Field
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Separable

/-! # The trinomial lift and the gcd/minpoly recovery

The geometric half of the Taylor programme (`notes/algebraic/PLAN-taylor-lean.md` §5)
produces, for a target real algebraic number `β`, a point on a trinomial surface
`x ^ D + a * x + b = 0` whose coordinates lie in some class `Coord` of real numbers
already known to be P-constructible (`SolvableReal`, `PTowerReal`, …).  Recovering `β`
from such a point is pure algebra and is what this file formalizes.

* `TrinomialLift Coord β` is the **lift data**: the trinomial parameters `D`, `a`, `b`
  and a root `x₀`, a rational polynomial `q` with a real root `y₀`, a real polynomial `T`
  with `x₀ = T y₀`, and the normalization `β = y₀ ^ 2 + c` coming from the square lift
  `y₀ = sqrt (β - c)` after a rational Möbius normalization.  All coordinates (`a`, `b`,
  `x₀` and the coefficients of `T`) are required to lie in `Coord`.
* `PConstructible.of_unique_common_root` is the **recovery step**.  Both `q` and
  `T - x₀` vanish at `y₀`, so in `PReal[X]` the minimal polynomial `p` of `y₀` divides
  both of them.  If the only complex root of `q` at which `T` takes the value `x₀` is
  `y₀`, then the only complex root of `p` is `y₀` as well; since `p` is separable this
  forces `natDegree p ≤ 1`, and a linear minimal polynomial means `y₀ ∈ PReal`.
* `TrinomialLift.Pconstructible` collects everything through one hypothesis
  `∀ x, Coord x → PConstructible x` and concludes `PConstructible β` using
  `β = y₀ ^ 2 + c` and the closure of `PConstructible` under field operations.

The distinctness hypothesis is deliberately stated on **all** complex roots of `q`
rather than only on the real ones.  The recovery works with the minimal polynomial of
`y₀` over `PReal`, which divides both `q` and `T - x₀`; if the two polynomials shared a
non-real common root, that minimal polynomial could acquire the corresponding complex
factor and its degree would no longer be forced to be `1`, so `y₀` would not have to be
rational over `PReal`.
-/

namespace Pconstructible

open Polynomial

-- The plan mandates the names `PConstructible.of_unique_common_root` and
-- `TrinomialLift.Pconstructible`, whose first component repeats the ambient namespace;
-- that is not a mistake here.
set_option linter.dupNamespace false

noncomputable section

/-! ### The lift data -/

/-- The data of a point on the trinomial surface from which `β` is recovered as
`y₀ ^ 2 + c`.  `Coord` is the class the coordinates are known to lie in
(`SolvableReal`, `PTowerReal`, …).  The distinctness hypothesis `hinj` is checked on
*all* complex roots of `q`, not only the real ones: otherwise the recovery can pick up
extra complex factors. -/
structure TrinomialLift (Coord : ℝ → Prop) (β : ℝ) where
  /-- The exponent of the trinomial `x ^ D + a * x + b`. -/
  D : ℕ
  /-- The exponent is positive. -/
  hD : 0 < D
  /-- The linear coefficient of the trinomial. -/
  a : ℝ
  /-- The constant coefficient of the trinomial. -/
  b : ℝ
  /-- A root of the trinomial. -/
  x₀ : ℝ
  /-- The rational shift in the square lift `β = y₀ ^ 2 + c`. -/
  c : ℚ
  /-- A rational polynomial with root `y₀`. -/
  q : ℚ[X]
  /-- The polynomial expressing `x₀` as a function of `y₀`. -/
  T : ℝ[X]
  /-- The real number whose square recovers `β`. -/
  y₀ : ℝ
  /-- The coefficient `a` lies in the coordinate class. -/
  ha : Coord a
  /-- The coefficient `b` lies in the coordinate class. -/
  hb : Coord b
  /-- The root `x₀` lies in the coordinate class. -/
  hx₀ : Coord x₀
  /-- Every coefficient of `T` lies in the coordinate class. -/
  hT : ∀ i, Coord (T.coeff i)
  /-- `x₀` is a root of the trinomial. -/
  hroot : x₀ ^ D + a * x₀ + b = 0
  /-- `q` is nonzero. -/
  hq : q ≠ 0
  /-- `y₀` is a root of `q`. -/
  hqy : aeval y₀ q = 0
  /-- `q` is separable. -/
  hq_sep : q.Separable
  /-- `x₀` is the value of `T` at `y₀`. -/
  hxT : x₀ = T.eval y₀
  /-- `T` is injective on the complex roots of `q`: this is the distinctness of the
  conjugates, checked on all complex roots so that the recovery cannot pick up extra
  complex factors. -/
  hinj : ∀ z₁ z₂ : ℂ,
    (q.map (algebraMap ℚ ℂ)).eval z₁ = 0 →
    (q.map (algebraMap ℚ ℂ)).eval z₂ = 0 →
    (T.map (algebraMap ℝ ℂ)).eval z₁ = (T.map (algebraMap ℝ ℂ)).eval z₂ → z₁ = z₂
  /-- The square lift: `β` is `y₀ ^ 2` shifted by the rational constant `c`. -/
  hβ : β = y₀ ^ 2 + c

/-! ### A separable polynomial with a single complex root is linear -/

/-- A nonzero separable polynomial over a field of characteristic zero whose complex
roots are all equal to a fixed point has degree at most one.

This is the degree count behind the gcd recovery: separability bounds the number of
roots by the degree with multiplicity, and the single-root hypothesis bounds it by one,
so the minimal polynomial of `y₀` is at most linear. -/
private theorem natDegree_le_one_of_separable_of_unique_root
    {K : Type*} [Field K] {φ : K →+* ℂ} (hφ : Function.Injective φ)
    {p : K[X]} (hp : p ≠ 0) (hsep : p.Separable) {a : ℂ}
    (hroot : ∀ z : ℂ, (p.map φ).eval z = 0 → z = a) :
    p.natDegree ≤ 1 := by
  have hne : p.map φ ≠ 0 := Polynomial.map_ne_zero hp
  have hsep' : (p.map φ).Separable := Polynomial.Separable.map hsep (f := φ)
  have hnodup : (p.map φ).roots.Nodup := Polynomial.nodup_roots hsep'
  have hmem : ∀ z ∈ (p.map φ).roots, z = a := by
    intro z hz
    exact hroot z ((Polynomial.mem_roots hne).mp hz)
  have hrep : (p.map φ).roots = Multiset.replicate (p.map φ).roots.card a :=
    Multiset.eq_replicate_card.mpr hmem
  have hcard : (p.map φ).roots.card ≤ 1 := by
    have h := (Multiset.nodup_iff_count_le_one.mp hnodup) a
    rwa [hrep, Multiset.count_replicate_self] at h
  have hsplit : (p.map φ).Splits := IsAlgClosed.splits (p.map φ)
  have hdeg : (p.map φ).natDegree = (p.map φ).roots.card := hsplit.natDegree_eq_card_roots
  calc p.natDegree = (p.map φ).natDegree := (Polynomial.natDegree_map_eq_of_injective hφ p).symm
    _ = (p.map φ).roots.card := hdeg
    _ ≤ 1 := hcard

/-! ### The recovery theorem -/

/-- **Unique-common-root recovery.** Let `q` be a nonzero separable rational polynomial
with a root `y₀`, and let `T` be a real polynomial with P-constructible coefficients. If
the only complex root of `q` at which `T` takes the value `x₀ = T y₀` is `y₀` itself,
then `y₀` is P-constructible. -/
theorem PConstructible.of_unique_common_root
    {q : ℚ[X]} {T : ℝ[X]} (hq : q ≠ 0) (hsep : q.Separable)
    (hT : ∀ i, PConstructible (T.coeff i))
    {x₀ y₀ : ℝ} (hx₀ : PConstructible x₀) (hxT : T.eval y₀ = x₀)
    (hqy : aeval y₀ q = 0)
    (huniq : ∀ z : ℂ, (q.map (algebraMap ℚ ℂ)).eval z = 0 →
      (T.map (algebraMap ℝ ℂ)).eval z = (x₀ : ℂ) → z = (y₀ : ℂ)) :
    PConstructible y₀ := by
  -- `q` viewed over the field `PReal` of P-constructible reals.
  let qK : PReal[X] := q.map (algebraMap ℚ PReal)
  have hqK : qK ≠ 0 := by
    dsimp only [qK]
    exact Polynomial.map_ne_zero hq
  have hsepK : qK.Separable := by
    dsimp only [qK]
    exact (Polynomial.separable_map (algebraMap ℚ PReal)).mpr hsep
  have hqyK : aeval y₀ qK = 0 := by
    dsimp only [qK]
    rw [Polynomial.aeval_map_algebraMap PReal y₀ q]
    exact hqy
  -- `T - x₀` viewed over `PReal`.
  obtain ⟨TK, hTK⟩ := Subfield.exists_map_eq_of_forall_coeff_mem PReal (fun i => hT i)
  let xK : PReal := ⟨x₀, hx₀⟩
  let RK : PReal[X] := TK - C xK
  have hRK : RK.map (algebraMap PReal ℝ) = T - C x₀ := by
    simp [RK, hTK, xK]
  have hyRK : aeval y₀ RK = 0 := by
    rw [← Polynomial.eval_map_algebraMap RK y₀, hRK]
    simp [hxT]
  -- The minimal polynomial of `y₀` over `PReal`.
  have h_int : IsIntegral PReal y₀ := IsAlgebraic.isIntegral ⟨qK, hqK, hqyK⟩
  let p : PReal[X] := minpoly PReal y₀
  have hp_ne : p ≠ 0 := by
    dsimp only [p]
    exact minpoly.ne_zero h_int
  have hmon : p.Monic := by
    dsimp only [p]
    exact minpoly.monic h_int
  have hpdq : p ∣ qK := by
    dsimp only [p]
    exact minpoly.dvd PReal y₀ hqyK
  have hpdR : p ∣ RK := by
    dsimp only [p]
    exact minpoly.dvd PReal y₀ hyRK
  have hp_sep : p.Separable := hsepK.of_dvd hpdq
  -- Both factors remain divisible after mapping to `ℂ`.
  have hqKmap : qK.map (algebraMap PReal ℂ) = q.map (algebraMap ℚ ℂ) := by
    dsimp only [qK]
    rw [Polynomial.map_map, IsScalarTower.algebraMap_eq ℚ PReal ℂ]
  have hRKmap : RK.map (algebraMap PReal ℂ) = (T - C x₀).map (algebraMap ℝ ℂ) := by
    rw [← hRK, Polynomial.map_map, IsScalarTower.algebraMap_eq PReal ℝ ℂ]
  have hpq : p.map (algebraMap PReal ℂ) ∣ q.map (algebraMap ℚ ℂ) := by
    rw [← hqKmap]
    exact Polynomial.map_dvd (algebraMap PReal ℂ) hpdq
  have hpR : p.map (algebraMap PReal ℂ) ∣ (T - C x₀).map (algebraMap ℝ ℂ) := by
    rw [← hRKmap]
    exact Polynomial.map_dvd (algebraMap PReal ℂ) hpdR
  -- The only complex root of the minimal polynomial is `y₀`.
  have huniq_root : ∀ z : ℂ, (p.map (algebraMap PReal ℂ)).eval z = 0 → z = (y₀ : ℂ) := by
    intro z hz
    have hzq : (q.map (algebraMap ℚ ℂ)).eval z = 0 := by
      obtain ⟨c, hc⟩ := hpq
      rw [hc, Polynomial.eval_mul, hz, zero_mul]
    have hzR : ((T - C x₀).map (algebraMap ℝ ℂ)).eval z = 0 := by
      obtain ⟨c, hc⟩ := hpR
      rw [hc, Polynomial.eval_mul, hz, zero_mul]
    have hzT : (T.map (algebraMap ℝ ℂ)).eval z = (x₀ : ℂ) := by
      rw [Polynomial.map_sub, Polynomial.map_C, Polynomial.eval_sub, Polynomial.eval_C] at hzR
      simpa using sub_eq_zero.mp hzR
    exact huniq z hzq hzT
  -- A separable polynomial with a single complex root is at most linear.
  have hdeg : p.natDegree ≤ 1 :=
    natDegree_le_one_of_separable_of_unique_root (algebraMap PReal ℂ).injective hp_ne hp_sep
      huniq_root
  -- Hence `p` is linear with leading coefficient `1`, and its root `y₀` lies in `PReal`.
  have hpdeg_pos : 0 < p.natDegree := by
    dsimp only [p]
    exact minpoly.natDegree_pos h_int
  have hpdeg : p.natDegree = 1 := by omega
  have hc1 : p.coeff 1 = 1 := by
    have h := hmon.coeff_natDegree
    rwa [hpdeg] at h
  have hp_form : p = C (p.coeff 1) * X + C (p.coeff 0) :=
    Polynomial.eq_X_add_C_of_natDegree_le_one hdeg
  have heval : aeval y₀ p = 0 := by
    dsimp only [p]
    exact minpoly.aeval PReal y₀
  rw [hp_form] at heval
  have hlin : algebraMap PReal ℝ (p.coeff 1) * y₀ + algebraMap PReal ℝ (p.coeff 0) = 0 := by
    simpa only [Polynomial.aeval_add, Polynomial.aeval_mul, Polynomial.aeval_C,
      Polynomial.aeval_X] using heval
  have hy_eq : y₀ = -algebraMap PReal ℝ (p.coeff 0) := by
    rw [hc1, map_one, one_mul] at hlin
    linarith
  have hmem : y₀ ∈ PReal := by
    rw [hy_eq]
    exact PReal.neg_mem (p.coeff 0).2
  exact hmem

/-! ### The lift theorem -/

/-- **The generic lift theorem.** If every `Coord`-number is P-constructible, then a
`TrinomialLift Coord β` makes `β` P-constructible. This is the single collection point for
all the weaker point-existence hypotheses of the plan (§5). -/
theorem TrinomialLift.Pconstructible {Coord : ℝ → Prop}
    (hCoord : ∀ x, Coord x → PConstructible x) {β : ℝ}
    (h : TrinomialLift Coord β) : PConstructible β := by
  obtain ⟨D, hD, a, b, x₀, c, q, T, y₀, ha, hb, hx₀, hT, hroot, hq, hqy, hsep, hxT,
    hinj, hβ⟩ := h
  have huniq : ∀ z : ℂ, (q.map (algebraMap ℚ ℂ)).eval z = 0 →
      (T.map (algebraMap ℝ ℂ)).eval z = (x₀ : ℂ) → z = (y₀ : ℂ) := by
    intro z hzq hzT
    refine hinj z (y₀ : ℂ) hzq ?_ ?_
    · have hm : q.map (algebraMap ℚ ℂ) = (q.map (algebraMap ℚ ℝ)).map (algebraMap ℝ ℂ) := by
        rw [Polynomial.map_map, IsScalarTower.algebraMap_eq ℚ ℝ ℂ]
      have h : (q.map (algebraMap ℚ ℂ)).eval (algebraMap ℝ ℂ y₀) = 0 := by
        rw [hm, Polynomial.eval_map_apply, Polynomial.eval_map_algebraMap, hqy, map_zero]
      exact h
    · rw [hzT]
      have h : (T.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ y₀) = (x₀ : ℂ) := by
        rw [Polynomial.eval_map_apply, hxT]
        rfl
      exact h.symm
  have hy₀ : PConstructible y₀ :=
    PConstructible.of_unique_common_root hq hsep (fun i => hCoord _ (hT i)) (hCoord _ hx₀)
      hxT.symm hqy huniq
  rw [hβ]
  simpa only [pow_two] using PConstructible.add (PConstructible.mul hy₀ hy₀) (rat_Pconstructible c)

end

end Pconstructible
