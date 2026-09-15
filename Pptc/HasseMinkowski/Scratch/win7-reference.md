# HassePrinciple → Pptc porting reference (`win7`)

Source repo: `mariainesdff/HassePrinciple`, branch `main`, fetched 2026-09-14.
Raw form: `https://raw.githubusercontent.com/mariainesdff/HassePrinciple/main/HassePrinciple/<path>`.
`[proved]` = no `sorry` anywhere in the declaration; `[sorry]` = at least one `sorry`.
Line counts are raw (`Get-Content`); `sorry` counts are occurrences.

| file | lines | decls | sorry occ. / sorry decls |
|---|---|---|---|
| Padics/Legendre.lean | 103 | 12 | 0 / 0 |
| Padics/Lemmas.lean | 339 | 16 | 11 / 6 |
| HilbertSymbol/Basic.lean | 418 | 35 | 11 / 11 |
| HilbertSymbol/ExistenceTheorem.lean | 395 | 31 | 1 / 1 |
| QuadraticForm/Basic.lean | 901 | 75 | 5 / 5 |
| QuadraticForm/HasseMinkowskiInvariant.lean | 306 | 18 | 5 / 5 |
| QuadraticForm/RankThree.lean | 22 | 1 | 1 / 1 |
| QuadraticForm/HighRank.lean | 22 | 1 | 1 / 1 |
| QuadraticForm/Chain.lean | 62 | 4 | 2 / 2 |

Signatures are transcribed upstream; routine instance binders are kept where they carry information
and elided as `[…]` where purely boilerplate. Every listing is in source order.

---

## 1. Padics/Legendre.lean — 103 lines, 0 sorry

Imports: `Mathlib.NumberTheory.LegendreSymbol.Basic`, `Mathlib.NumberTheory.Padics.RingHoms`.
Whole file follows (copyright header omitted); declarations in order:
`MulChar.compMonoidHom`, `PadicInt.legendreSym`, `legendreSym.intCast`, `legendreSym.eq_pow`,
`legendreSym.eq_one_or_neg_one`, `legendreSym.eq_neg_one_iff_not_one`, `legendreSym.eq_zero_iff`,
`legendreSym.hom`, `legendreSym.sq_one`, `legendreSym.sq_one'`, `legendreSym.eq_one_iff`,
`legendreSym.eq_neg_one_iff`. All `[proved]`.

```lean
module

public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.NumberTheory.Padics.RingHoms

/-! # The Legendre Symbol for Padic Integers. -/

@[expose] public section

namespace MulChar

variable {M M' R F : Type*} [CommMonoid M] [CommMonoid M'] [CommMonoidWithZero R]
  [FunLike F M' M] [MonoidHomClass F M' M]

/-- We define the composition of monoid morphisms as the map composition. It is still a monoid
morphism. -/
@[simps]
def compMonoidHom (χ : MulChar M R) (f : F) [IsLocalHom f] : MulChar M' R where
  toFun m' := χ (f m')
  map_one' := by simp
  map_mul' := by simp
  map_nonunit' m' hm' := map_nonunit χ (isUnit_map_iff f m' |>.not.mpr hm')

end MulChar

namespace PadicInt

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- The Legendre symbol of a p-adic integer is the quadratic character on ℤ_[p] precomposed with
the reduction modulo p. -/
noncomputable
def legendreSym : MulChar ℤ_[p] ℤ := (quadraticChar (ZMod p)).compMonoidHom toZMod

variable {a b : ℤ_[p]}
namespace legendreSym

/-- The Padic Legendre symbol agrees with the classical Legendre symbol on ℤ. -/
lemma intCast (z : ℤ) : legendreSym (z : ℤ_[p]) = _root_.legendreSym p z := by
  simp [legendreSym, _root_.legendreSym, quadraticCharFun]

/-- We have the congruence `legendreSym a ≡ a ^ (p / 2) mod p`. -/
theorem eq_pow : (legendreSym a : ZMod p) = (a.toZMod) ^ (p / 2) := by
  calc (legendreSym a : ZMod p)
    _ = (legendreSym (a.zmodRepr : ℤ_[p]) : ZMod p) := by
      simp [legendreSym, (ZMod.intCast_eq_intCast_iff' (quadraticCharFun (ZMod p) (toZMod a))
        (quadraticCharFun (ZMod p) a.zmodRepr) p).mpr rfl]
    _ = _root_.legendreSym p (a.zmodRepr) := by simp [legendreSym, _root_.legendreSym]
    _ = (a.zmodRepr) ^ (p / 2) := by simp [_root_.legendreSym.eq_pow]
    _ = (a.toZMod) ^ (p / 2) := ZMod.valMinAbs_inj.mp rfl

/-- If `a` is a p-adic unit, then `legendreSym a` is `1` or `-1`. -/
theorem eq_one_or_neg_one (ha : IsUnit a) : legendreSym a = 1 ∨ legendreSym a = -1 :=
  Int.isUnit_eq_one_or (IsUnit.map ((quadraticChar (ZMod p)).compMonoidHom toZMod) ha)

/-- If a is a p-adic unit, then `legendreSym a = -1` iff `legendreSym a ≠ 1`. -/
theorem eq_neg_one_iff_not_one (ha : IsUnit a) :
    legendreSym a = -1 ↔ ¬legendreSym a = 1 := by
  have := eq_one_or_neg_one ha
  lia

/-- The Legendre symbol of `p` and `a` is zero iff `p ∣ a`. -/
theorem eq_zero_iff : legendreSym a = 0 ↔ ¬ IsUnit a :=
  ⟨fun _ h ↦ by have := eq_one_or_neg_one h; lia, fun h ↦ by rw [MulChar.map_nonunit
  legendreSym h]⟩

/-- The Legendre symbol is a homomorphism of monoids with zero. -/
@[simps]
noncomputable def hom : ℤ_[p] →*₀ ℤ where
  toFun        := legendreSym
  map_zero'    := by simp [legendreSym]
  map_one'     := by simp [legendreSym]
  map_mul' _ _ := by simp [legendreSym, map_mul]

/-- The square of the symbol is 1 if `a` is a unit. -/
theorem sq_one (ha : IsUnit a) : legendreSym a ^ 2 = 1 := by
   cases eq_one_or_neg_one ha <;> aesop

/-- The Legendre symbol of `a^2` at `p` is 1 if `a` is a unit. -/
theorem sq_one' (ha : IsUnit a) : legendreSym (a ^ 2) = 1 := by
  rw [pow_two]
  cases eq_one_or_neg_one ha <;> aesop

/-- If `a` is a unit, then `legendreSym a = 1` iff `a` is a square mod `p`. -/
theorem eq_one_iff (ha : IsUnit a) : legendreSym a = 1 ↔ IsSquare (a.toZMod) := by
  rw [legendreSym, MulChar.compMonoidHom_apply, quadraticChar_one_iff_isSquare]
  rw [← ZMod.val_ne_zero (toZMod a), val_toZMod_eq_zmodRepr, ← norm_natCast_zmodRepr_eq_one_iff_ne,
    norm_natCast_zmodRepr_eq_one_iff.mpr (isUnit_iff.mp ha)]

/-- `legendreSym p a = -1` iff `a` is a nonsquare mod `p`. -/
theorem eq_neg_one_iff (ha : IsUnit a) :
    legendreSym a = -1 ↔ ¬ IsSquare (a.toZMod) := by
  rw [eq_neg_one_iff_not_one ha, eq_one_iff ha]

end legendreSym

end PadicInt
```

Porting notes: `MulChar.compMonoidHom` is **not** in Mathlib 4.33 (this file defines it) — carry it
over. `_root_.legendreSym.eq_pow` was not found by local search; verify/rename.
`quadraticChar`, `quadraticCharFun`, `quadraticChar_one_iff_isSquare`, `ZMod.valMinAbs_inj`,
`ZMod.val_ne_zero`, `PadicInt.norm_natCast_zmodRepr_eq_one_iff{,_ne}` all exist locally. 103 lines.

---

## 2. Padics/Lemmas.lean — 339 lines, 11 sorry occurrences (6 sorry decls)

Imports: `Mathlib.Algebra.MvPolynomial.PDeriv`, `Mathlib.NumberTheory.LegendreSymbol.Basic`,
`Mathlib.NumberTheory.Padics.PadicIntegers`, `Mathlib.NumberTheory.Padics.RingHoms`,
`Mathlib.RingTheory.MvPolynomial.Homogeneous`, `Mathlib.NumberTheory.Padics.Hensel`,
`Mathlib.Algebra.Polynomial.Basic`.

```lean
def Function.IsPrimitive {M σ : Type*} [Monoid M] (f : σ → M) : Prop := ∃ s, IsUnit (f s)   -- [proved]
lemma Padic.norm_mul_pow_neg_valuation_eq_one (x : ℚ_[p]ˣ) : ‖(x : ℚ_[p]) * p ^ (- valuation x.val)‖ = 1   -- [proved]
noncomputable def Padic.unitPart (x : ℚ_[p]ˣ) : ℤ_[p]ˣ := PadicInt.mkUnits (norm_mul_pow_neg_valuation_eq_one x)   -- [proved]
lemma Padic.valuation_units (a : ℤ_[p]ˣ) : (a : ℤ_[p]).valuation = 0   -- [proved]
lemma Padic.map_unitPart (a : ℤ_[p]ˣ) : unitPart (Units.map (algebraMap ℤ_[p] ℚ_[p]) a) = a   -- [proved]
noncomputable abbrev Padic.p2 (hp : p ≠ 2) : ℤ_[2]ˣ   -- [proved]
lemma Padic.exists_padicInt_solution {v : ℚ_[p]ˣ} {x y z : ℚ_[p]} (hnontriv : (x, y, z) ≠ (0, 0, 0)) (hsol : z ^ 2 - p * x ^ 2 - v * y ^ 2 = 0) : ∃ z' y' x' : ℤ_[p], (z' : ℚ_[p]) ^ 2 - p * (x' : ℚ_[p]) ^ 2 - v * (y' : ℚ_[p]) ^ 2 = 0 ∧ (IsUnit z' ∨ IsUnit y' ∨ IsUnit x')   -- [sorry] (2)
lemma Padic.lift_solutions_to_int_first {v : ℚ_[p]ˣ} {x y z : ℚ_[p]} (hnontriv : (x, y, z) ≠ (0, 0, 0)) (hsol : z ^ 2 - p * x ^ 2 - v * y ^ 2 = 0) : ∃ z' y' x' : ℤ_[p], (z' : ℚ_[p]) ^ 2 - p * (x' : ℚ_[p]) ^ 2 - v * (y' : ℚ_[p]) ^ 2 = 0 ∧ (IsUnit z' ∨ IsUnit y' ∨ IsUnit x')   -- [sorry] (1)
lemma Padic.exists_nontrivial_zero {v : (ℚ_[p])ˣ} {x y z : ℚ_[p]} (hnontriv : (x, y, z) ≠ (0, 0, 0)) (hsol : z ^ 2 - p * x ^ 2 - v * y ^ 2 = 0) : ∃ z' y' : ℤ_[p]ˣ, ∃ x' : ℤ_[p], (z' : ℚ_[p]) ^ 2 - p * (x' : ℚ_[p]) ^ 2 - v * (y' : ℚ_[p]) ^ 2 = 0   -- [sorry] (5)
lemma Padic.common_root_tfae {σ ι : Type*} {f : ι → MvPolynomial σ ℤ_[p]} (hf : ∀ i, (f i).IsHomogeneous (f i).totalDegree) : List.TFAE [∃ (z : σ → ℚ_[p]), (∃ s, z s ≠ 0) ∧ (∀ i, (f i).aeval z = 0), ∃ (z : σ → ℤ_[p]), z.IsPrimitive ∧ ∀ i, (f i).aeval z = 0, ∀ {n : ℕ} (hn : 1 ≤ n), ∃ (z : σ → ZMod (p ^ n)), z.IsPrimitive ∧ ∀ i, ((f i).map (PadicInt.toZModPow n)).aeval z = 0]   -- [sorry] (1)
lemma PadicInt.p_dvd_iff_toZMod_eq_zero {m : ℤ_[p]} : (p : ℤ_[p]) ∣ m ↔ m.toZMod = 0   -- [proved]
lemma PadicInt.pow_p_dvd_iff_toZModPow_eq_zero {m : ℤ_[p]} {n : ℕ} : (p : ℤ_[p]) ^ n ∣ m ↔ m.toZModPow n = 0   -- [proved]
lemma PadicInt.isSquare_of_zmod (hp : p ≠ 2) {m : ℤ_[p]} (hm : ¬ (p : ℤ_[p]) ∣ m) (hmod : IsSquare m.toZMod) : IsSquare m   -- [proved]
lemma PadicInt.isSquare_of_zmodPow {m : ℤ_[2]} (hm : ¬ (2 : ℤ_[2]) ∣ m) (hmod : IsSquare (m.toZModPow 3)) : IsSquare m   -- [proved]
theorem PadicInt.multivariable_hensel {m : ℕ} {f : MvPolynomial (Fin m) ℤ_[p]} {a : Fin m → ℤ_[p]} {n k : ℤ} (hk : 0 < 2 * k ∧ 2 * k < n) {j : Fin m} (hF : n ≤ valuation (MvPolynomial.aeval a f)) (hJ : valuation (MvPolynomial.aeval a (MvPolynomial.pderiv j f)) = k) : ∃ (z : Fin m → ℤ_[p]), (MvPolynomial.aeval z f = 0) ∧ ∀ i, n - k ≤ valuation (z i - a i)   -- [sorry] (1)
theorem PadicInt.multivariable_hensel' {m : ℕ} {f : MvPolynomial (Fin m) ℤ_[p]} {a : Fin m → ℤ_[p]} {n k : ℤ} (hk : 0 < 2 * k ∧ 2 * k < n) {j : Fin m} (hF : ‖(MvPolynomial.aeval a) f‖ ≤ p ^ (-n)) (hJ : ‖(MvPolynomial.aeval a) (MvPolynomial.pderiv j f)‖ = p ^ (-k)) : ∃ (z : Fin m → ℤ_[p]), (MvPolynomial.aeval z f = 0) ∧ ∀ i, ‖z i - a i‖ < p ^ (-n + k)   -- [sorry] (1)
```

### Full bodies to port first (all `[proved]`, sorry-free)

```lean
/-- An element in `ℤ_[p]` for odd `p` is a square if its reduction modulo `p` is a square. -/
lemma isSquare_of_zmod {p : ℕ} [Fact (Nat.Prime p)] (hp : p ≠ 2)
    {m : ℤ_[p]} (hm : ¬ (p : ℤ_[p]) ∣ m) (hmod : IsSquare m.toZMod) : IsSquare m := by
  obtain ⟨r, hr⟩ := hmod
  let a := (r.cast : ℤ_[p])
  let F : ℤ_[p][X] := X ^ 2 - C m
  have hF : ‖(aeval a) F‖ < ‖(aeval a) (derivative F)‖ ^ 2 := by
    have h2 : ‖(2 : ℤ_[p])‖ = 1 := by
      rw [← Nat.cast_two, norm_natCast_eq_one_iff]
      simp [Nat.coprime_two_right, Nat.Prime.odd_of_ne_two Fact.out hp]
    have h1 : ‖(r.cast : ℤ_[p])‖ = 1 := by
      rw [← isUnit_iff, ← IsLocalRing.notMem_maximalIdeal, ← ker_toZMod, RingHom.mem_ker]
      simp only [ZMod.ringHom_map_cast]
      by_contra h0
      simp only [h0, mul_zero, ← p_dvd_iff_toZMod_eq_zero] at hr
      exact hm hr
    simp only [aeval_sub, coe_aeval_eq_eval, eval_pow, eval_X, aeval_C, Algebra.algebraMap_self,
      RingHom.id_apply, derivative_sub, derivative_X_pow_succ, Nat.cast_one, one_add_one_eq_two,
      pow_one, derivative_C, sub_zero, eval_mul, eval_C, norm_mul, a, F, h2, one_mul, h1, one_pow]
    simp [norm_lt_one_iff_dvd, p_dvd_iff_toZMod_eq_zero, hr, pow_two]
  obtain ⟨z, hz0, hz⟩ := hensels_lemma hF
  simp only [aeval_sub, coe_aeval_eq_eval, eval_pow, eval_X, aeval_C, Algebra.algebraMap_self,
    RingHom.id_apply, F, sub_eq_zero] at hz0
  exact ⟨z, by simp [← hz0, pow_two]⟩

/-- An element in `ℤ_[2]` is a square if its reduction modulo `8` is a square. -/
lemma isSquare_of_zmodPow {m : ℤ_[2]} (hm : ¬ (2 : ℤ_[2]) ∣ m) (hmod : IsSquare (m.toZModPow 3)) :
    IsSquare m := by
  obtain ⟨r, hr⟩ := hmod
  let a := (r.cast : ℤ_[2])
  let F : ℤ_[2][X] := X ^ 2 - C m
  have hF : ‖(aeval a) F‖ < ‖(aeval a) (derivative F)‖ ^ 2 := by
    have h1 : ‖(r.cast : ℤ_[2])‖ = 1 := by
      rw [← isUnit_iff, ← IsLocalRing.notMem_maximalIdeal, ← ker_toZMod, RingHom.mem_ker]
      simp only [Nat.reducePow, ← p_dvd_iff_toZMod_eq_zero, Nat.cast_ofNat]
      by_contra h0
      have : toZModPow 3 r.cast = r := by simp
      rw [← sub_eq_zero, ← this, ← map_mul, ← map_sub, ← pow_p_dvd_iff_toZModPow_eq_zero,
        Nat.cast_ofNat] at hr
      exact hm ((dvd_iff_dvd_of_dvd_sub (dvd_trans (dvd_pow_self 2 three_ne_zero) hr)).mpr
        (dvd_mul_of_dvd_left h0 r.cast))
    simp only [aeval_sub, coe_aeval_eq_eval, eval_pow, eval_X, aeval_C, Algebra.algebraMap_self,
      RingHom.id_apply, derivative_sub, derivative_X_pow_succ, Nat.cast_one, one_add_one_eq_two,
      pow_one, derivative_C, sub_zero, eval_mul, eval_C, norm_mul, a, F, mul_one, h1,
      ← Nat.cast_two (R := ℤ_[2]), PadicInt.norm_p, ← zpow_neg_one, ← zpow_natCast,
      ← zpow_mul, Nat.reducePow, Int.reduceNeg, neg_mul, one_mul,
      norm_lt_pow_iff_norm_le_pow_sub_one, Nat.cast_ofNat (R := ℤ), Int.reduceSub]
    rw [← Nat.cast_three, norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton,
      pow_p_dvd_iff_toZModPow_eq_zero]
    simp [hr, pow_two]
  obtain ⟨z, hz0, hz⟩ := hensels_lemma hF
  simp only [aeval_sub, coe_aeval_eq_eval, eval_pow, eval_X, aeval_C, Algebra.algebraMap_self,
    RingHom.id_apply, F, sub_eq_zero] at hz0
  exact ⟨z, by simp [← hz0, pow_two]⟩

variable {p : ℕ} [Fact (Nat.Prime p)] (x : ℚ_[p]ˣ)
/-- Given a nonzero padic number `x`, the norm of `x` times `p` raised to the negative of its
valuation equals one. -/
lemma norm_mul_pow_neg_valuation_eq_one : ‖(x : ℚ_[p]) * p ^ (- valuation x.val)‖ = 1 := by
  simp [norm_eq_zpow_neg_valuation, inv_mul_cancel₀ (zpow_ne_zero _ NeZero.out)]

/-- Given a nonzero padic number `x`, the unit part of `x` is defined as the element `u` in `ℤ_[p]ˣ`
such that `u = x(p^{-v(x)})` -/
noncomputable def unitPart : ℤ_[p]ˣ :=
  PadicInt.mkUnits (norm_mul_pow_neg_valuation_eq_one x)
```

Porting notes: all pieces these three need exist locally (`hensels_lemma`,
`PadicInt.norm_natCast_eq_one_iff`, `PadicInt.norm_p`, `PadicInt.prime_p`,
`PadicInt.norm_lt_pow_iff_norm_le_pow_sub_one`, `PadicInt.norm_le_pow_iff_mem_span_pow`,
`PadicInt.norm_eq_zpow_neg_valuation`, `PadicInt.mkUnits`, `padicValInt`, `PadicInt.toZModPow`,
`PadicInt.ker_toZModPow`). No Mathlib gap expected beyond possible API renames. 339 lines.

---

## 3. HilbertSymbol/ExistenceTheorem.lean — 395 lines, 1 sorry

Imports: `HassePrinciple.HilbertSymbol.Basic`, `HassePrinciple.ForMathlib.Algebra.Ring.Int.Parity`.

Shared `Integer`-section context:

```lean
variable {I : Type*} {a : I → ℤ} (ha : ∀ i, a i ≠ 0) {ep : I → Primes → ℤ}
  (hep : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1)
  {ereal : I → ℤ} (hereal : ∀ i : I, ereal i = 1 ∨ ereal i = -1)
  (h1 : ∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1)
  (h2 : ∀ i : I, (∏ᶠ (p : Primes), ep i p) * ereal i = 1)
  (h3 : ((∀ (p : Primes), ∃ xp : ℚ_[p], ∀ i : I, hilbertSym xp (a i) = ep i p)) ∧
    ∃ xr : ℝ, ∀ i : I, hilbertSym xr (a i) = ereal i)
```

Statements only (bodies omitted). All `[proved]` except the one marked:

```lean
private lemma necessary_cond (x : ℚˣ) (h : ∀ i : I, (∀ p : Primes, hilbertSym (x : ℚ_[p]) (a i) = ep i p) ∧ hilbertSym (x : ℝ) (a i) = ereal i) : (∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1) ∧ (∀ i : I, (∏ᶠ p : Primes, ep i p) * ereal i = 1) ∧ (∀ p : Primes, ∃ xp : ℚ_[p], ∀ i : I, hilbertSym xp (a i) = ep i p) ∧ ∃ xr : ℝ, ∀ i : I, hilbertSym xr (a i) = ereal i   -- [proved]
private lemma ep_eq_neg_one_iff_not_one {i : I} {p : Primes} : ep i p = -1 ↔ ¬ep i p = 1   -- [proved]
lemma all_but_one_places_suffice (q : Primes) (x : ℚˣ) (h4 : ∀ i : I, (∀ p : Primes, p ≠ q → hilbertSym (x : ℚ_[p]) (a i) = ep i p) ∧ hilbertSym (x : ℝ) (a i) = ereal i) : ∀ i : I, (∀ p : Primes, hilbertSym (x : ℚ_[p]) (a i) = ep i p) ∧ hilbertSym (x : ℝ) (a i) = ereal i   -- [proved]
noncomputable def S : Finset Primes := (univ.biUnion (fun i ↦ (a i).natAbs.primeFactors) ∪ {2}).preimage Subtype.val Subtype.val_injective.injOn   -- [proved]
private lemma two_in_S : ⟨2, prime_two⟩ ∈ S a   -- [proved]
lemma Tfin : (⋃ i : I, {p : Primes | ep i p = -1}).Finite   -- [proved]
noncomputable def T : Finset Primes := (Tfin hep h1).toFinset   -- [proved]
private lemma ep_eq_one_of_not_mem_T {p : Primes} (hpT : p ∉ T hep h1) (i : I) : ep i p = 1   -- [proved]
private lemma ep_eq_one_iff_not_mem_T (p : Primes) : p ∉ T hep h1 ↔ ∀ i : I, ep i p = 1   -- [proved]
private lemma ep_eq_one_of_mem_S_disjoint {p : Primes} (hpS : p ∈ S a) (i : I) : ep i p = 1   -- [proved]
private lemma is_unit_ai_of_p_notMem_S {p : Primes} (hpS : p ∉ S a) (i : I) : padicValInt p (a i) = 0   -- [proved]
private noncomputable abbrev A : ℕ := ∏ t ∈ T hep h1, (t : ℕ)   -- [proved]
private lemma A_ne_zero : A hep h1 ≠ 0   -- [proved]
private lemma A_pos : 0 < A hep h1   -- [proved]
private noncomputable abbrev M := 4 * ∏ s ∈ S a, (s : ℕ)   -- [proved]
private lemma M_ne_zero : M a ≠ 0   -- [proved]
private lemma q_existence : ∃ q : ℕ, Nat.Prime q ∧ q ≡ ∏ t ∈ T hep h1, (t : ℕ) [MOD 4 * ∏ s ∈ S a, (s : ℕ)]   -- [proved]
private noncomputable abbrev q : ℕ := (q_existence hep h1 disjoint_ST).choose   -- [proved]
private lemma q_prime : Nat.Prime (q hep h1 disjoint_ST)   -- [proved]
private lemma q_cong : q hep h1 disjoint_ST ≡ ∏ t ∈ T hep h1, (t : ℕ) [MOD 4 * ∏ s ∈ S a, (s : ℕ)]   -- [proved]
private noncomputable def x := mk0 ((A hep h1) * (q hep h1 disjoint_ST) : ℚ) (by simp only [ne_eq, _root_.mul_eq_zero, cast_eq_zero, not_or]; exact ⟨A_ne_zero hep h1, (q_prime hep h1 disjoint_ST).ne_zero⟩)   -- [proved]
private lemma x_pos : 0 < (x hep h1 disjoint_ST).val   -- [proved]
private lemma p_mem_S_not_dvd_x {p : Primes} (hpS : p ∈ S a) (hpq : p ≠ q hep h1 disjoint_ST) : ¬ (p : ℤ_[p]) ∣ (A hep h1) * (q hep h1 disjoint_ST)   -- [proved]
private lemma isSquare_x {p : Primes} (hpS : p ∈ S a) (hpq : p ≠ q hep h1 disjoint_ST) : IsSquare ((A hep h1) * (q hep h1 disjoint_ST) : ℤ_[p])   -- [proved]
private lemma isSquare_x_of_p_mem_S {p : Primes} (hpS : p ∈ S a) (hpq : p ≠ q hep h1 disjoint_ST) : IsSquare (x hep h1 disjoint_ST : ℚ_[p])   -- [proved]
private lemma padicValRat_x_eq_one_of_p_mem_T (p : Primes) (pneq : p ≠ q hep h1 disjoint_ST) (hpT : p ∈ T hep h1) : padicValRat p (x hep h1 disjoint_ST).val = 1   -- [proved]
private lemma padicValRat_x_eq_zero_of_p_notMem_T {p : Primes} (pneq : p ≠ q hep h1 disjoint_ST) (hpT : p ∉ T hep h1) : padicValRat p (x hep h1 disjoint_ST).val = 0   -- [proved]
private lemma existence_disjoint (infty_not_mem_T : ∀ i : I, ereal i = 1) : ∃ x : ℚˣ, ∀ i : I, (∀ p : Primes, hilbertSym (x : ℚ_[p]) (a i) = ep i p) ∧ hilbertSym (x : ℝ) (a i) = ereal i   -- [proved]
theorem exists_rat_with_finite_prescribed_hilbertSym_of_int [Nonempty I] : (∃ x : ℚˣ, ∀ i : I, (∀ p : Primes, hilbertSym (x : ℚ_[p]) (a i) = ep i p) ∧ hilbertSym (x : ℝ) (a i) = ereal i) ↔ (∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1) ∧ (∀ i : I, (∏ᶠ (p : Primes), ep i p) * ereal i = 1) ∧ ((∀ (p : Primes), ∃ xp : ℚ_[p], ∀ i : I, hilbertSym xp (a i) = ep i p)) ∧ ∃ xr : ℝ, ∀ i : I, hilbertSym xr (a i) = ereal i   -- [sorry]
theorem exists_rat_with_finite_prescribed_hilbertSym {I : Type*} [Finite I] [Nonempty I] (a : I → ℚˣ) {ep : I → Primes → ℤ} {ereal : I → ℤ} (hep : ∀ i : I, ∀ p : Primes, ep i p = 1 ∨ ep i p = -1) (hereal : ∀ i : I, ereal i = 1 ∨ ereal i = -1) : (∃ x : ℚˣ, ∀ i : I, (∀ p : Primes, hilbertSym (x : ℚ_[p]) (a i) = ep i p) ∧ hilbertSym (x : ℝ) (a i) = ereal i) ↔ (∀ i : I, ∀ᶠ p : Primes in cofinite, ep i p = 1) ∧ (∀ i : I, (∏ᶠ (p : Primes), ep i p) * ereal i = 1) ∧ ((∀ (p : Primes), ∃ xp : ℚ_[p], ∀ i : I, hilbertSym xp (a i) = ep i p)) ∧ ∃ xr : ℝ, ∀ i : I, hilbertSym xr (a i) = ereal i   -- [proved]
theorem exists_rat_with_two_prescribed_hilbertSym (a b : ℚˣ) {ep ep' : Primes → ℤ} {er er' : ℤ} (hep : ∀ p : Primes, ep p = 1 ∨ ep p = -1) (hep' : ∀ p : Primes, ep' p = 1 ∨ ep' p = -1) (her : er = 1 ∨ er = -1) (her' : er' = 1 ∨ er' = -1) : (∃ x : ℚˣ, (∀ p : Primes, hilbertSym (x : ℚ_[p]) a = ep p ∧ hilbertSym (x : ℚ_[p]) b = ep' p) ∧ hilbertSym (x : ℝ) a = er ∧ hilbertSym (x : ℝ) b = er') ↔ ((∀ᶠ (p : Primes) in cofinite, ep p = 1) ∧ (∀ᶠ (p : Primes) in cofinite, ep' p = 1)) ∧ (((∏ᶠ (p : Primes), ep p) * er = 1) ∧ ((∏ᶠ (p : Primes), ep' p) * er' = 1)) ∧ (∀ (p : Primes), ∃ xp : ℚ_[p], hilbertSym xp a = ep p ∧ hilbertSym xp b = ep' p) ∧ ∃ xr : ℝ, hilbertSym xr a = er ∧ hilbertSym xr b = er'   -- [proved]
```

Porting notes: only dependency outside Mathlib is the local
`HassePrinciple.ForMathlib.Algebra.Ring.Int.Parity`; `Nat.infinite_setOfPred_prime_and_modEq`
(Dirichlet in AP, used by `q_existence`) is present in `Mathlib.NumberTheory.LSeries.PrimesInAP`.
1 sorry: the `_of_int` master theorem. 395 lines.

---

## 4. HilbertSymbol/Basic.lean — 418 lines, 11 sorry

Imports: `HassePrinciple.Padics.Lemmas`, `HassePrinciple.Padics.Legendre`,
`Mathlib.Algebra.QuadraticAlgebra.Basic`, `Mathlib.NumberTheory.PrimeCounting`,
`Mathlib.NumberTheory.LSeries.PrimesInAP`.

```lean
noncomputable abbrev PadicInt.epsilon (u : (PadicInt 2)ˣ) : ℤ := if (u.val).appr 2 % 4 = 1 then 0 else 1   -- [proved]
noncomputable abbrev PadicInt.omega (u : (PadicInt 2)ˣ) : ℤ := if (u.val).appr 3 % 8 = 1 ∨ (u.val).appr 3 % 8 = 7 then 0 else 1   -- [proved]
noncomputable def hilbertSym {k : Type*} [Field k] (a b : k) : ℤ := by classical exact if a = 0 ∨ b = 0 then 0 else if ∃ z x y : k, (z, x, y) ≠ (0, 0, 0) ∧ z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0 then 1 else -1   -- [proved]
lemma hilbertSym.eq_one_or_neg_one_of_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) : hilbertSym a b = 1 ∨ hilbertSym a b = -1   -- [proved]
lemma hilbertSym.ne_zero_of_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) : hilbertSym a b ≠ 0   -- [proved]
lemma hilbertSym.mul_square_eq (ha' : a' ≠ 0) (hb' : b' ≠ 0) : hilbertSym (a * a' ^ 2) (b * b' ^ 2) = hilbertSym a b   -- [proved]
lemma hilbertSym.mul_left_square_eq (ha' : a' ≠ 0) : hilbertSym (a * a' ^ 2) b = hilbertSym a b   -- [proved]
lemma hilbertSym.mul_right_square_eq (hb' : b' ≠ 0) : hilbertSym a (b * b' ^ 2) = hilbertSym a b   -- [proved]
lemma hilbertSym.comm : hilbertSym a b = hilbertSym b a   -- [proved]
theorem hilbertSym.eq_one_iff (ha : a ≠ 0) (hb : b ≠ 0) (hc : ¬IsSquare b) : hilbertSym a b = 1 ↔ ∃ t : QuadraticAlgebra k b 0, a = QuadraticAlgebra.norm t   -- [proved]
theorem hilbertSym.right_square_eq_one (ha : a ≠ 0) (hb : b ≠ 0) : hilbertSym a (b ^ 2) = 1   -- [proved]
theorem hilbertSym.right_neg_self_eq_one (ha : a ≠ 0) : hilbertSym a (-a) = 1   -- [proved]
theorem hilbertSym.right_one_minus_self_eq_one (ha0 : a ≠ 0) (ha1 : a ≠ 1) : hilbertSym a (1 - a) = 1   -- [proved]
theorem hilbertSym.eq_one_or_neg_one (ha : a ≠ 0) (hb : b ≠ 0) : hilbertSym a b = 1 ∨ hilbertSym a b = -1   -- [proved]
theorem hilbertSym.eq_neg_one_iff_not_one (ha : a ≠ 0) (hb : b ≠ 0) : hilbertSym a b = -1 ↔ ¬hilbertSym a b = 1   -- [proved]
theorem hilbertSym.right_mul_eq_of_eq_one (hab : hilbertSym a b = 1) : hilbertSym a (b * b') = hilbertSym a b'   -- [proved]
theorem hilbertSym.right_neg_mul : hilbertSym a (- (a * b)) = hilbertSym a b   -- [proved]
theorem hilbertSym.left_neg_mul : hilbertSym (- (a * b)) b = hilbertSym a b   -- [proved]
theorem hilbertSym.right_minus_self_mul (ha : a ≠ 1) : hilbertSym a ((1 - a) * b) = hilbertSym a b   -- [proved]
class hilbertSym.HasBilinHilbertSym (k : Type*) [Field k] : Prop where mul_left_eq {a a' b : k} : hilbertSym (a * a') b = hilbertSym a b * hilbertSym a' b   -- [proved]
lemma hilbertSym.HasBilinHilbertSym.mul_right_eq [HasBilinHilbertSym k] : hilbertSym a (b * b') = hilbertSym a b * hilbertSym a b'   -- [proved]
theorem hilbertSym.real_eq (ha : a ≠ 0) (hb : b ≠ 0) : hilbertSym a b = if 0 < a ∨ 0 < b then 1 else -1   -- [proved]
instance _root_.Real.instHasBilinHilbertSym : HasBilinHilbertSym ℝ   -- [proved]
lemma hilbertSym.padic_odd_case00 (ha0 : a.valuation = 0) (hb0 : b.valuation = 0) : (hilbertSym a b : ℚ) = Int.negOnePow (valuation a * valuation b * epsilon (p2 hp2)) * (legendreSym (unitPart (Units.mk0 a ha) : ℤ_[p])) ^ valuation b * (legendreSym (unitPart (Units.mk0 b hb) : ℤ_[p])) ^ valuation a   -- [sorry]
lemma hilbertSym.padic_odd_case10 (ha1 : valuation a = 1) (hb0 : valuation b = 0) : (hilbertSym a b : ℚ) = Int.negOnePow (valuation a * valuation b * epsilon (p2 hp2)) * (legendreSym (unitPart (Units.mk0 a ha) : ℤ_[p])) ^ valuation b * (legendreSym (unitPart (Units.mk0 b hb) : ℤ_[p])) ^ valuation a   -- [sorry]
lemma hilbertSym.padic_odd_case11 (ha1 : valuation a = 1) (hb1 : valuation b = 1) : (hilbertSym a b : ℚ) = Int.negOnePow (valuation a * valuation b * epsilon (p2 hp2)) * (legendreSym (unitPart (Units.mk0 a ha) : ℤ_[p])) ^ valuation b * (legendreSym (unitPart (Units.mk0 b hb) : ℤ_[p])) ^ valuation a   -- [sorry]
theorem hilbertSym.padic_odd_eq : (hilbertSym a b : ℚ) = Int.negOnePow (valuation a * valuation b * epsilon (p2 hp2)) * (legendreSym (unitPart (Units.mk0 a ha) : ℤ_[p])) ^ valuation b * (legendreSym (unitPart (Units.mk0 b hb) : ℤ_[p])) ^ valuation a   -- [sorry]
lemma hilbertSym.two_adic_case00 (ha0 : valuation a = 0) (hb0 : valuation b = 0) : hilbertSym a b = Int.negOnePow (epsilon (unitPart (Units.mk0 a ha)) * epsilon (unitPart (Units.mk0 b hb)) + valuation a * omega (unitPart (Units.mk0 b hb)) + valuation b * omega (unitPart (Units.mk0 a ha)))   -- [sorry]
lemma hilbertSym.two_adic_case10 (ha1 : valuation a = 1) (hb0 : valuation b = 0) : hilbertSym a b = Int.negOnePow (epsilon (unitPart (Units.mk0 a ha)) * epsilon (unitPart (Units.mk0 b hb)) + valuation a * omega (unitPart (Units.mk0 b hb)) + valuation b * omega (unitPart (Units.mk0 a ha)))   -- [sorry]
lemma hilbertSym.two_adic_case11 (ha1 : valuation a = 1) (hb1 : valuation b = 1) : hilbertSym a b = Int.negOnePow (epsilon (unitPart (Units.mk0 a ha)) * epsilon (unitPart (Units.mk0 b hb)) + valuation a * omega (unitPart (Units.mk0 b hb)) + valuation b * omega (unitPart (Units.mk0 a ha)))   -- [sorry]
theorem hilbertSym.two_adic_eq : hilbertSym a b = Int.negOnePow (PadicInt.epsilon (unitPart (Units.mk0 a ha)) * epsilon (unitPart (Units.mk0 b hb)) + valuation a * omega (unitPart (Units.mk0 b hb)) + valuation b * omega (unitPart (Units.mk0 a ha)))   -- [sorry]
instance _root_.Padic.instHasBilinHilbertSym : HasBilinHilbertSym ℚ_[p]   -- [sorry]
scoped instance hilbertSym.fact_prime (p : Nat.Primes) : Fact (Nat.Prime p) := fact_iff.mpr p.2   -- [proved]
theorem hilbertSym.almost_all_one (a b : ℚˣ) : ∀ᶠ (p : Nat.Primes) in Filter.cofinite, hilbertSym (a : ℚ_[p]) b = 1   -- [sorry]
theorem hilbertSym.prod_eq_one (a b : ℚˣ) : (∏ᶠ (p : Nat.Primes), hilbertSym (a : ℚ_[p]) b) * hilbertSym (a : ℝ) b = 1   -- [sorry]
```

Porting notes: shaky dependencies are `zpow_odd_one_or_neg_one_eq_self` (not found locally),
`QuadraticAlgebra.norm` / `QuadraticAlgebra.mk` (only the `QuadraticAlgebra` structure was found by
local search — verify the norm API), and `_root_.legendreSym.eq_pow` from Legendre.lean.
`LinearMap.SeparatingLeft`, `Nat.Primes`, `PadicInt.norm_p` exist. 11 sorry declarations.

---

## 5. QuadraticForm/Basic.lean — 901 lines, 5 sorry

Imports: `HassePrinciple.ForMathlib.LinearAlgebra.BilinearForm.TensorProduct`,
`HassePrinciple.ForMathlib.LinearAlgebra.LinearIndependent.Basis`,
`HassePrinciple.ForMathlib.LinearAlgebra.TensorProduct.Prod`, `Mathlib.Algebra.Squarefree.Basic`,
`Mathlib.LinearAlgebra.QuadraticForm.Prod`, `Mathlib.LinearAlgebra.QuadraticForm.Radical`,
`Mathlib.LinearAlgebra.QuadraticForm.TensorProduct`, `Mathlib.LinearAlgebra.TensorProduct.Finiteness`,
`Mathlib.LinearAlgebra.TensorProduct.Pi`, `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`.

```lean
theorem QuadraticForm.equivalent_weightedSumSquares_units_of_nondegenerate {K V} [Field K] [Invertible (2:K)] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (n : ℕ) (hn : Module.finrank K V = n) {Q : QuadraticForm K V} (hQ : LinearMap.SeparatingLeft (associated Q)) : ∃ w : Fin n → Kˣ, Equivalent Q (QuadraticMap.weightedSumSquares K w)   -- [proved]
abbrev QuadraticForm.prod (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) : QuadraticForm R (M₁ × M₂)   -- [proved]
abbrev QuadraticForm.restrict (Q : QuadraticForm R M) (U : Submodule R M) : QuadraticForm R U   -- [proved]
abbrev QuadraticForm.weightedSumSquares (R) (w : ι → S) : QuadraticForm R (ι → R)   -- [proved]
lemma QuadraticForm.weightedSumSquares_toMatrix (R) (w) : toMatrix (Pi.basisFun R ι) (weightedSumSquares R w) = Matrix.diagonal fun i ↦ w i • 1   -- [proved]
lemma QuadraticForm.weightedSumSquares_discr (R) (w) : discr (Pi.basisFun R ι) (weightedSumSquares R w) = ∏ i, w i • 1   -- [proved]
lemma QuadraticForm.baseChange_toMatrix (A) (b) : (Q.baseChange A).toMatrix (b.baseChange A) = (Q.toMatrix b).map (algebraMap R A)   -- [proved]
lemma QuadraticForm.baseChange_discr (A) (b) : (Q.baseChange A).discr (b.baseChange A) = algebraMap R A (Q.discr b)   -- [proved]
def QuadraticForm.weightedSumSquaresCongr' (f : ι ≃ κ) (h : w = w'.comp f) : (weightedSumSquares R w).IsometryEquiv (weightedSumSquares R w')   -- [proved]
lemma QuadraticForm.weightedSumSquaresCongr'_equivalent (f) (h) : (weightedSumSquares R w).Equivalent (weightedSumSquares R w')   -- [proved]
lemma QuadraticForm.discr_reindex (e : ι ≃ κ) (b) (Q) : Q.discr (b.reindex e) = Q.discr b   -- [proved]
lemma QuadraticForm.IsometryEquiv.discr (e : ι ≃ κ) (b₁) (b₂) (f : Q₁.IsometryEquiv Q₂) : Q₁.discr b₁ = Q₂.discr b₂ * (f.toLinearEquiv.toMatrix (b₁.reindex e) b₂).det ^ 2   -- [proved]
lemma QuadraticMap.Equivalent.baseChange (A) (h : Q₁.Equivalent Q₂) : (Q₁.baseChange A).Equivalent (Q₂.baseChange A)   -- [proved]
theorem QuadraticMap.polarBilin_injective' : Function.Injective (polarBilin : QuadraticMap R M N → _)   -- [proved]
theorem QuadraticMap.polarBilin_ext_iff : Q₁ = Q₂ ↔ Q₁.polarBilin = Q₂.polarBilin   -- [proved]
abbrev QuadraticMap.Isotropic (Q : QuadraticMap R M₁ N) := ¬ Q.Anisotropic   -- [proved]
def QuadraticMap.represents (Q : QuadraticMap R M₁ N) (n : N) : Prop := ∃ x, Q x = n ∧ x ≠ 0   -- [proved]
lemma QuadraticMap.represents_zero_iff_isotropic : Q.represents 0 ↔ Q.Isotropic   -- [proved]
lemma QuadraticMap.Equivalent.represents (h : Q.Equivalent Q') (hQ : Q.represents n) : Q'.represents n   -- [proved]
lemma QuadraticMap.Equivalent.represents_iff (h) (n) : Q.represents n ↔ Q'.represents n   -- [proved]
lemma QuadraticMap.Equivalent.isotropic (h) (hQ : Q.Isotropic) : Q'.Isotropic   -- [proved]
lemma QuadraticMap.Equivalent.isotropic_iff (h) : Q.Isotropic ↔ Q'.Isotropic   -- [proved]
lemma QuadraticMap.nondegenerate_of_anisotropic [Invertible (2:R)] (hQ : Q.Anisotropic) : Q.Nondegenerate   -- [proved]
lemma QuadraticMap.anisotropic_of_rank_zero (hr : finrank R M = 0) : Q.Anisotropic   -- [proved]
lemma QuadraticMap.anisotropic_of_rank_one (hr : finrank R M = 1) (hQ : Q ≠ 0) : Q.Anisotropic   -- [proved]
lemma QuadraticMap.isotropic_iff_zero_of_rank_one (hr : finrank R M = 1) : Q.Isotropic ↔ Q = 0   -- [proved]
lemma QuadraticMap.degenerate_zero (hM : 0 < finrank R M) : ¬ (0 : QuadraticMap R M N).Nondegenerate   -- [proved]
lemma QuadraticMap.two_le_finrank_of_isotropic_of_nondegenerate (hQ : Q.Isotropic) (hQ' : Q.Nondegenerate) : 2 ≤ finrank R M   -- [proved]
theorem QuadraticMap.Equivalent.nondegenerate (h : Q.Equivalent Q') (hQ : Q.Nondegenerate) : Q'.Nondegenerate   -- [proved]
theorem QuadraticMap.Equivalent.nondegenerate_iff (h) : Q.Nondegenerate ↔ Q'.Nondegenerate   -- [proved]
lemma QuadraticMap.nondegenerate_weightedSumSquares (w : Fin n → kˣ) : (weightedSumSquares k w).Nondegenerate   -- [proved]
lemma QuadraticMap.mul_unit_isotropic {a : Sˣ} (h : ∀ i, w' i = a * w i) : (weightedSumSquares R w').Isotropic → (weightedSumSquares R w).Isotropic   -- [proved]
lemma QuadraticMap.mul_unit_isotropic_iff {a : Sˣ} (h : ∀ i, w' i = a * w i) : (weightedSumSquares R w).Isotropic ↔ (weightedSumSquares R w').Isotropic   -- [proved]
lemma QuadraticMap.weightedSumSquares_mul_squares_equivalent (u : ι → Sˣ) (h : ∀ i, w' i * u i ^ 2 = w i) : Equivalent (weightedSumSquares R w) (weightedSumSquares R w')   -- [proved]
lemma QuadraticForm.degenerate_baseChange (hQ : ¬ Q.Nondegenerate) : ¬ (Q.baseChange A).Nondegenerate   -- [proved]
theorem QuadraticForm.isotropic_iff_weightedSumSquares_units_of_nondegenerate (hQ : Q.Nondegenerate) : ∃ w : Fin (finrank K V) → Kˣ, w 0 = 1 ∧ (Q.Isotropic ↔ (weightedSumSquares K w).Isotropic)   -- [proved]
theorem QuadraticForm.isotropic_iff_weightedSumSquares_squarefree_units_of_nondegenerate (hQ) : ∃ w : Fin (finrank ℚ V) → ℤ, w 0 = 1 ∧ ∀ n, w n ≠ 0 ∧ Squarefree (w n) ∧ (Q.Isotropic ↔ (weightedSumSquares ℚ w).Isotropic)   -- [sorry]
lemma QuadraticForm.represents_iff_sub_isotropic (hQ) (r : Kˣ) : Q.represents r ↔ (Q.prod (weightedSumSquares K ![-r])).Isotropic   -- [sorry]
lemma QuadraticForm.prod_isotropic_iff (hQ) (hQ') : (Q.prod (-Q')).Isotropic ↔ ∃ r : Kˣ, Q.represents r ∧ Q'.represents r   -- [sorry]
lemma QuadraticForm.prod_isotropic_iff' (hQ) (hQ') : (Q.prod (-Q')).Isotropic ↔ ∃ r : Kˣ, (Q.prod (weightedSumSquares K ![-r])).Isotropic ∧ (Q'.prod (weightedSumSquares K ![-r])).Isotropic   -- [sorry]
noncomputable abbrev QuadraticForm.XY (b : Basis (Fin 2) R V) : QuadraticForm R V   -- [proved]
def QuadraticForm.IsHyperbolic (Q : QuadraticForm R V) : Prop := Q.Equivalent (XY (Pi.basisFun R (Fin 2)))   -- [proved]
lemma QuadraticForm.XY_isHyperbolic (b : Basis (Fin 2) R V) : IsHyperbolic (XY b)   -- [proved]
lemma QuadraticMap.Equivalent.isHyperbolic (hQ : Q.IsHyperbolic) (heq : Q'.Equivalent Q) : Q'.IsHyperbolic   -- [proved]
theorem QuadraticForm.represents_of_isHyperbolic (hQ : Q.IsHyperbolic) (r : R) : represents Q r   -- [proved]
theorem QuadraticForm.restrict_isHyperbolic_of_polar (hx0) (hQx) (hQy) (hQxy) : (Q.restrict (span R {x, y})).IsHyperbolic   -- [proved]
def QuadraticForm.orthoCompl (Q) (S : Set V) : Submodule R V   -- [proved]
lemma QuadraticForm.mem_orthoCompl (Q) (S) (v) : v ∈ Q.orthoCompl S ↔ ∀ w : S, Q.IsOrtho v w   -- [proved]
def QuadraticForm.toDual (Q) (S : Submodule R V) : V →ₗ[R] Module.Dual R S   -- [proved]
lemma QuadraticForm.orthoCompl_eq_ker_toDual (Q) (S) : Q.orthoCompl S = (Q.toDual S).ker   -- [proved]
noncomputable def QuadraticForm.xyIsometryEquivSumSquares : IsometryEquiv (XY b) (weightedSumSquares R ![(1 : Rˣ), -1])   -- [proved]
lemma QuadraticForm.Xsq_sub_Ysq_isHyperbolic : IsHyperbolic (weightedSumSquares R ![(1 : Rˣ), -1])   -- [proved]
lemma QuadraticForm.equivalent_Xsq_sub_Ysq_of_isHyperbolic (hQ : Q.IsHyperbolic) : Q.Equivalent (weightedSumSquares R ![(1 : Rˣ), -1])   -- [proved]
lemma QuadraticForm.IsHyperbolic.nondegenerate (hQ : Q.IsHyperbolic) : Q.Nondegenerate   -- [proved]
lemma QuadraticForm.radical_eq_orthoCompl_top (Q) : Q.radical = Q.orthoCompl ⊤   -- [proved]
lemma QuadraticForm.radical_restrict_eq_inf (Q) (S) : map S.subtype (Q.restrict S).radical = (S ⊓ (Q.orthoCompl S))   -- [proved]
lemma QuadraticForm.nondegenerate_iff_toDual_bijective : Q.Nondegenerate ↔ Function.Bijective (Q.toDual ⊤)   -- [proved]
lemma QuadraticForm.toDual_surjective (hQ) (S) : Function.Surjective (Q.toDual S)   -- [proved]
lemma QuadraticForm.finrank_eq_add (hQ) (S) : finrank K V = finrank K S + finrank K (Q.orthoCompl S)   -- [proved]
lemma QuadraticForm.orthoCompl_orthoCompl (hQ) (S) : (Q.orthoCompl (Q.orthoCompl S)) = S   -- [proved]
lemma QuadraticForm.nondegenerate_orthoCompl (hQ) {S} (hS) : (Q.restrict (Q.orthoCompl S)).Nondegenerate   -- [proved]
lemma QuadraticForm.nondegenerate_orthoCompl_iff (hQ) (S) : (Q.restrict S).Nondegenerate ↔ (Q.restrict (Q.orthoCompl S)).Nondegenerate   -- [proved]
lemma QuadraticForm.orthoCompl_isCompl (hQ) {S} (hQS) : IsCompl S (Q.orthoCompl S)   -- [proved]
noncomputable def Submodule.prodOrthoComplEquiv (hQ) {U} (hU) : ((Q.restrict U).prod (Q.restrict (Q.orthoCompl U))).IsometryEquiv Q   -- [proved]
lemma QuadraticForm.equivalent_isHyperbolic_add (hQ : Q.Isotropic) (hQ' : Q.Nondegenerate) : ∃ (A : QuadraticForm K (Fin 2 → K)) (B : QuadraticForm K (Fin (finrank K V - 2) → K)), A.IsHyperbolic ∧ Q.Equivalent (A.prod B)   -- [proved]
lemma QuadraticForm.represents_of_isotropic_of_nondegenerate (hQ) (hQ') (r : K) : Q.represents r   -- [proved]
lemma QuadraticForm.nondegenerate_iff_discr_ne_zero : Q.Nondegenerate ↔ Q.discr b ≠ 0   -- [sorry]
lemma QuadraticForm.nondegenerate_baseChange (hQ : Q.Nondegenerate) : (Q.baseChange A).Nondegenerate   -- [proved]
theorem QuadraticForm.toMatrix_prod (b) (b') : toMatrix (b.prod b') (Q.prod Q') = Matrix.fromBlocks (toMatrix b Q) 0 0 (toMatrix b' Q')   -- [proved]
theorem QuadraticForm.discr_prod (b) (b') : discr (b.prod b') (Q.prod Q') = discr b Q * discr b' Q'   -- [proved]
lemma QuadraticForm.nondegenerate_prod (hQ) (hQ') : (Q.prod Q').Nondegenerate   -- [proved]
theorem QuadraticForm.polar_weightedSumSquares (w : ι → S) : polar (weightedSumSquares R w) = fun x y ↦ ∑ i, 2 * (w i) • (x i) * (y i)   -- [proved]
lemma QuadraticForm.baseChange_prod (Q₁) (Q₂) : ((Q₁.prod Q₂).baseChange A).Equivalent ((Q₁.baseChange A).prod (Q₂.baseChange A))   -- [proved]
lemma QuadraticForm.baseChange_prod_neg (Q₁) (Q₂) : ((Q₁.prod (-Q₂)).baseChange A).Equivalent ((Q₁.baseChange A).prod (- Q₂.baseChange A))   -- [proved]
theorem QuadraticForm.baseChange_weightedSumSquares (w : ι → R) : ((weightedSumSquares R w).baseChange A).Equivalent (weightedSumSquares A (fun i ↦ algebraMap R A (w i)))   -- [proved]
```

Porting notes: three local `HassePrinciple.ForMathlib.LinearAlgebra.*` modules are imported and are
not in Mathlib 4.33 — port/duplicate them first. 5 sorry declarations:
`isotropic_iff_weightedSumSquares_squarefree_units_of_nondegenerate`, `represents_iff_sub_isotropic`,
`prod_isotropic_iff`, `prod_isotropic_iff'`, `nondegenerate_iff_discr_ne_zero`. 901 lines.

---

## 6. QuadraticForm/HasseMinkowskiInvariant.lean — 306 lines, 5 sorry

Imports: `HassePrinciple.ForMathlib.LinearAlgebra.Determinant`, `HassePrinciple.HilbertSymbol.Basic`,
`HassePrinciple.HilbertSymbol.ExistenceTheorem`, `HassePrinciple.QuadraticForm.LowRank`,
`HassePrinciple.QuadraticForm.Chain`, `HassePrinciple.NumberTheory.ApproximationTheorem`,
`Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv`, `Mathlib.Data.Fin.Basic`.

```lean
lemma LinearMap.separatingLeft_of_equivalent (h : Q.Equivalent Q') (hQ : LinearMap.SeparatingLeft Q.associated) : LinearMap.SeparatingLeft Q'.associated   -- [sorry]
private noncomputable def QuadraticForm.finThreeLinearEquivProd : (Fin 3 → k) ≃ₗ[k] (Fin 2 → k) × (Fin 1 → k)   -- [proved]
private theorem QuadraticForm.weightedSumSquares_equiv_prod (w : Fin 2 → kˣ) (a : kˣ) : (weightedSumSquares k ![w 0, w 1, a]).Equivalent ((weightedSumSquares k w).prod (weightedSumSquares k ![a]))   -- [proved]
noncomputable def QuadraticForm.hasseMinkowskiInvAux {n : ℕ} (w : Fin n → kˣ) : ℤ := ∏ p : Fin n × Fin n with p.1 < p.2, hilbertSym (w p.1 : k) (w p.2)   -- [proved]
lemma QuadraticForm.hasseMinkowskiInvAux_def {n : ℕ} (w : Fin n → kˣ) : hasseMinkowskiInvAux w = ∏ p : Fin n × Fin n with p.1 < p.2, hilbertSym (w p.1) (w p.2)   -- [proved]
lemma QuadraticForm.hasseMinkowskiInvAux.eq_of_equivalent {n m} {w : Fin n → kˣ} {w' : Fin m → kˣ} (h : (weightedSumSquares k w).Equivalent (weightedSumSquares k w')) : hasseMinkowskiInvAux w = hasseMinkowskiInvAux w'   -- [sorry]
noncomputable def QuadraticForm.hasseMinkowskiInv {Q : QuadraticForm k V} (hQ : LinearMap.SeparatingLeft Q.associated) : ℤ := hasseMinkowskiInvAux (equivalent_weightedSumSquares_units_of_nondegenerate' Q hQ).choose   -- [proved]
lemma QuadraticForm.hasseMinkowskiInv.weightedSumSquares {n : ℕ} (w : Fin n → kˣ) : hasseMinkowskiInv (nondegenerate_associated_iff.mpr (nondegenerate_weightedSumSquares w)).1 = ∏ p : Fin n × Fin n with p.1 < p.2, hilbertSym (w p.1 : k) (w p.2)   -- [proved]
lemma QuadraticForm.hasseMinkowskiInv.weightedSumSquares_two (w : Fin 2 → kˣ) : hasseMinkowskiInv (nondegenerate_associated_iff.mpr (nondegenerate_weightedSumSquares w)).1 = hilbertSym (w 0 : k) (w 1)   -- [proved]
lemma QuadraticForm.hasseMinkowskiInv.weightedSumSquares_three (w : Fin 3 → kˣ) : hasseMinkowskiInv (nondegenerate_associated_iff.mpr (nondegenerate_weightedSumSquares w)).1 = hilbertSym (w 0 : k) (w 1) * hilbertSym (w 0 : k) (w 2) * hilbertSym (w 1 : k) (w 2)   -- [proved]
lemma QuadraticForm.hasseMinkowskiInv.eq_of_equivalent_weightedSumSquares {n} {w : Fin n → kˣ} (h : Q.Equivalent (weightedSumSquares k w)) : hasseMinkowskiInv hQ = hasseMinkowskiInv (LinearMap.separatingLeft_of_equivalent h hQ)   -- [sorry]
lemma QuadraticForm.hasseMinkowskiInv.eq_of_equivalent (h : Q.Equivalent Q') : hasseMinkowskiInv hQ = hasseMinkowskiInv (LinearMap.separatingLeft_of_equivalent h hQ)   -- [sorry]
lemma QuadraticForm.hasseMinkowskiInv.eq_one_or_neg_one : hasseMinkowskiInv hQ = 1 ∨ hasseMinkowskiInv hQ = - 1   -- [sorry]
lemma QuadraticForm.hasseMinkowskiInv.of_baseChange_weightedSumSquares (A) [Field R] [Invertible (2:R)] [Field A] [Invertible (2:A)] [Algebra R A] (w : Fin 2 → Rˣ) : hasseMinkowskiInv (...) = hilbertSym (algebraMap R A (w 0)) (algebraMap R A (w 1))   -- [proved]
lemma QuadraticForm.hasseMinkowskiInv.prod_rank_one [HasBilinHilbertSym k] (b : Basis (Fin 2) k V) (a : kˣ) (h : Q.Nondegenerate) : hasseMinkowskiInv (...) = hilbertSym (a : k) (Q.discr b) * hasseMinkowskiInv (...)   -- [proved]
private lemma QuadraticForm.represents_zero_iff_of_rank_three_aux (b : Basis (Fin 3) k V) (hQ) {w} (hw) (heq) : Q.Isotropic ↔ hilbertSym (-1) (-Q.discr b) = hasseMinkowskiInv (Q.nondegenerate_associated_iff.mpr hQ).1   -- [proved]
lemma QuadraticForm.represents_zero_iff_of_rank_three (b : Basis (Fin 3) k V) : Q.Isotropic ↔ hilbertSym (-1) (-Q.discr b) = hasseMinkowskiInv (Q.nondegenerate_associated_iff.mpr hQ).1   -- [proved]
lemma QuadraticForm.represents_iff_of_rank_two (b : Basis (Fin 2) k V) (a : kˣ) : Q.represents a ↔ hilbertSym (a : k) (-Q.discr b) = hasseMinkowskiInv (Q.nondegenerate_associated_iff.mpr hQ).1   -- [proved]
```

Porting notes: imports four local modules (`ForMathlib.LinearAlgebra.Determinant`,
`QuadraticForm.LowRank`, `QuadraticForm.Chain`, `NumberTheory.ApproximationTheorem`) absent from
Mathlib 4.33. `weightedSumSquares_isotropic_iff_hilbertSym_eq_one` (used in
`represents_zero_iff_of_rank_three_aux`) and `discr_three` (used in `represents_zero_iff_of_rank_three`)
were not found locally — they live in the unported repo files (likely `QuadraticForm/Rat.lean`).
5 sorry declarations. 306 lines.

---

## 7–9. Rank wrappers

### RankThree.lean — 22 lines, 1 sorry
Import: `HassePrinciple.QuadraticForm.Rat`. All decls `[sorry]`:
```lean
lemma QuadraticForm.EverywhereLocallyIsotropic.isotropic_of_rank_three (hr : Module.finrank ℚ V = 3) (hQ : Q.Nondegenerate) (hQ' : Q.EverywhereLocallyIsotropic) : Q.Isotropic   -- [sorry]
```
Porting note: only dependency is the local `HassePrinciple.QuadraticForm.Rat` (not in Mathlib 4.33).

### HighRank.lean — 22 lines, 1 sorry
Import: `HassePrinciple.QuadraticForm.RankFour`. All decls `[sorry]`:
```lean
lemma QuadraticForm.EverywhereLocallyIsotropic.isotropic_of_five_le_rank (hr : 5 ≤ Module.finrank ℚ V) (hQ : Q.Nondegenerate) (hQ' : Q.EverywhereLocallyIsotropic) : Q.Isotropic   -- [sorry]
```
Porting note: only dependency is the local `HassePrinciple.QuadraticForm.RankFour` (not in Mathlib).

### Chain.lean — 62 lines, 2 sorry
Import: `Mathlib.LinearAlgebra.QuadraticForm.Radical` (present in 4.33).
```lean
def Module.Basis.IsContiguous (b b' : Basis ι R M) : Prop := ∃ (i j : ι), b i = b' j   -- [proved]
structure Module.Basis.Chain (Q : QuadraticForm k V) (b b' : Basis (Fin (finrank k V)) k V) : Type _ where  -- [proved]
  m : ℕ;  basis : Fin (m + 1) → Basis (Fin (finrank k V)) k V
  basis_ortho (i : Fin (m + 1)) : Q.associated.IsOrthoᵢ (basis i)
  basis_zero : basis 0 = b;  basis_m_sub_one : basis ⟨m, lt_add_one m⟩ = b'
  basis_isContiguous {i : ℕ} (hi : i < m) : (basis ⟨i, by omega⟩).IsContiguous (basis ⟨i, by omega⟩)
lemma Module.Basis.exists_const (hdim : 3 ≤ finrank k V) (hQ : Q.Nondegenerate) {b b'} (hb) (hb') (h1) (h2) : ∃ (x : k), Q (b' ⟨1, by omega⟩ + x • b' ⟨2, by omega⟩) ≠ 0 ∧ ((Q.restrict (Submodule.span k {b ⟨1, by omega⟩, b' ⟨1, by omega⟩ + x • b' ⟨2, by omega⟩}))).Nondegenerate   -- [sorry]
def Module.Basis.chainOfNondegenerate (hdim : 3 ≤ finrank k V) (hQ : Q.Nondegenerate) {b b'} (hb) (hb') : Chain Q b b'   -- [sorry]
```
Porting note: no missing Mathlib lemmas identified; the two obligations are geometric sorrys.

---

## Sorry inventory (all sorry-bearing declarations)

- Padics/Lemmas.lean: `exists_padicInt_solution`, `lift_solutions_to_int_first`,
  `exists_nontrivial_zero`, `common_root_tfae`, `multivariable_hensel`, `multivariable_hensel'`.
- HilbertSymbol/Basic.lean: `padic_odd_case00/10/11`, `padic_odd_eq`, `two_adic_case00/10/11`,
  `two_adic_eq`, `Padic.instHasBilinHilbertSym`, `almost_all_one`, `prod_eq_one`.
- HilbertSymbol/ExistenceTheorem.lean: `exists_rat_with_finite_prescribed_hilbertSym_of_int`.
- QuadraticForm/Basic.lean: `isotropic_iff_weightedSumSquares_squarefree_units_of_nondegenerate`,
  `represents_iff_sub_isotropic`, `prod_isotropic_iff`, `prod_isotropic_iff'`,
  `nondegenerate_iff_discr_ne_zero`.
- QuadraticForm/HasseMinkowskiInvariant.lean: `LinearMap.separatingLeft_of_equivalent`,
  `hasseMinkowskiInvAux.eq_of_equivalent`, `hasseMinkowskiInv.eq_of_equivalent_weightedSumSquares`,
  `hasseMinkowskiInv.eq_of_equivalent`, `hasseMinkowskiInv.eq_one_or_neg_one`.
- QuadraticForm/RankThree.lean: `isotropic_of_rank_three`.
- QuadraticForm/HighRank.lean: `isotropic_of_five_le_rank`.
- QuadraticForm/Chain.lean: `exists_const`, `chainOfNondegenerate`.
