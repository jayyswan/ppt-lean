import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.Constructions.SumProd

/-! # Pptc.NonicWitness — the real-collision witness for the nonic Tschirnhaus reduction

This file proves WP2 and WP3 of `PLAN-nonic-tschirnhaus.md`:

* `spread` is the real quadratic form `Re (Σ_ρ g(ρ)² - (Σ_ρ g(ρ))²/9)` attached to a
  polynomial `ψ` of degree `≤ 6` and a vector `v` of length `6`, where `g(ρ) = Σ_k v_k ψ(ρ)^{k+1}`
  runs over the nine complex roots `ρ` of `q`;
* `exists_real_signs` constructs real `ψ, v` making `spread` both negative and positive;
* `continuous_spread` and `exists_rat_signs` upgrade the real witness to a rational one.

The construction picks a real divisor `D` of `q` of degree `3` or `4`, forms `ψ₀ = (X - t)·D`
for a generic real `t`, collapses the roots of `D` onto `0`, and interpolates the two target
functions `±i` and `1` on the resulting set of at most seven nodes. -/

namespace Pconstructible

noncomputable section

open Polynomial

/-- The real part of `Σ_ρ g(ρ)² - (Σ_ρ g(ρ))²/9` over a finite set `R` of complex nodes. -/
@[irreducible] def spreadCore (R : Finset ℂ) (g : ℂ → ℂ) : ℝ :=
  ((∑ z ∈ R, g z ^ 2) - (∑ z ∈ R, g z) ^ 2 / 9).re

/-- The real quadratic form used by the nonic Tschirnhaus construction. -/
@[irreducible] noncomputable def spread (q : ℚ[X]) (ψ : Fin 7 → ℝ) (v : Fin 6 → ℝ) : ℝ :=
  spreadCore ((q.map (algebraMap ℚ ℂ)).roots.toFinset)
    (fun z => ∑ k : Fin 6, (v k : ℂ)
      * (∑ j : Fin 7, (ψ j : ℂ) * z ^ (j : ℕ)) ^ (k.val + 1))

-- Theorem: `spread q` is continuous as a function of `(ψ, v)`.
theorem continuous_spread (q : ℚ[X]) :
    Continuous fun p : (Fin 7 → ℝ) × (Fin 6 → ℝ) => spread q p.1 p.2 := by
  unfold spread spreadCore
  simp only
  fun_prop

/-! ### Invariance of `spread` under adding a constant to `g` -/

-- Theorem: shifting `g` by a constant does not change `spreadCore`, provided the finite set
-- of nodes has cardinality `9` (the trace zero-shift `-2·9c·S + 9c²` cancels the shift of the
-- square sum exactly).
theorem spreadCore_add_const (R : Finset ℂ) (hR : R.card = 9) (g : ℂ → ℂ) (c : ℂ) :
    spreadCore R (fun z => g z + c) = spreadCore R g := by
  unfold spreadCore
  have hsq : ∀ z : ℂ, (g z + c) ^ 2 = g z ^ 2 + (2 * c) * g z + c ^ 2 :=
    fun z => by ring
  have h1 : (∑ z ∈ R, (g z + c) ^ 2)
      = (∑ z ∈ R, g z ^ 2) + (2 * c) * (∑ z ∈ R, g z) + 9 * c ^ 2 := by
    simp_rw [hsq]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      hR]
    norm_num
  have h2 : (∑ z ∈ R, (g z + c)) = (∑ z ∈ R, g z) + 9 * c := by
    rw [Finset.sum_add_distrib, Finset.sum_const, hR]
    norm_num
  rw [h1, h2]
  ring_nf

/-! ### Density: real witnesses can be replaced by rational ones -/

set_option maxHeartbeats 800000 in
-- Theorem: if real witnesses give both signs of `spread`, then rational witnesses do too.
-- The set `{spread < 0 ∧ spread > 0}` is open and nonempty, and the rational points are dense
-- in the triple product `ℝ⁷ × ℝ⁶ × ℝ⁶`, so it contains a rational point.
theorem exists_rat_signs {q : ℚ[X]}
    (h : ∃ (ψ : Fin 7 → ℝ) (vm vp : Fin 6 → ℝ),
      spread q ψ vm < 0 ∧ 0 < spread q ψ vp) :
    ∃ (ψ : Fin 7 → ℚ) (vm vp : Fin 6 → ℚ),
      spread q (fun j => ψ j) (fun k => vm k) < 0
        ∧ 0 < spread q (fun j => ψ j) (fun k => vp k) := by
  classical
  obtain ⟨ψ, vm, vp, hneg, hpos⟩ := h
  have hcs := continuous_spread q
  let f1 : (Fin 7 → ℚ) → (Fin 7 → ℝ) := Pi.map fun _ => (Rat.cast : ℚ → ℝ)
  let f2 : (Fin 6 → ℚ) → (Fin 6 → ℝ) := Pi.map fun _ => (Rat.cast : ℚ → ℝ)
  have hdense1 : DenseRange f1 := DenseRange.piMap (fun _ => Rat.denseRange_cast)
  have hdense2 : DenseRange f2 := DenseRange.piMap (fun _ => Rat.denseRange_cast)
  have hdense : DenseRange (Prod.map f1 (Prod.map f2 f2)) :=
    DenseRange.prodMap hdense1 (DenseRange.prodMap hdense2 hdense2)
  have hcont1 : Continuous fun p : (Fin 7 → ℝ) × (Fin 6 → ℝ) × (Fin 6 → ℝ) =>
      spread q p.1 p.2.1 :=
    hcs.comp (Continuous.prodMap continuous_id continuous_fst)
  have hcont2 : Continuous fun p : (Fin 7 → ℝ) × (Fin 6 → ℝ) × (Fin 6 → ℝ) =>
      spread q p.1 p.2.2 :=
    hcs.comp (Continuous.prodMap continuous_id continuous_snd)
  have hopen : IsOpen {p : (Fin 7 → ℝ) × (Fin 6 → ℝ) × (Fin 6 → ℝ) |
      spread q p.1 p.2.1 < 0 ∧ 0 < spread q p.1 p.2.2} :=
    (isOpen_lt hcont1 continuous_const).inter (isOpen_lt continuous_const hcont2)
  obtain ⟨x, hxrange, hxU⟩ := Dense.exists_mem_open hdense hopen
    ⟨(ψ, (vm, vp)), hneg, hpos⟩
  rcases hxrange with ⟨⟨ψ', vm', vp'⟩, hx⟩
  rw [← hx] at hxU
  have e1 : f1 ψ' = fun j => (ψ' j : ℝ) := by
    funext j; simp [f1, Pi.map_apply]
  have e2 : f2 vm' = fun k => (vm' k : ℝ) := by
    funext k; simp [f2, Pi.map_apply]
  have e3 : f2 vp' = fun k => (vp' k : ℝ) := by
    funext k; simp [f2, Pi.map_apply]
  exact ⟨ψ', vm', vp', by rw [← e1, ← e2]; exact hxU.1,
    by rw [← e1, ← e3]; exact hxU.2⟩

/-! ### Real interpolation on a conjugation-closed node set -/

-- Theorem: a conjugation-equivariant target function `r` on a conjugation-closed set `N` of at
-- most seven complex nodes is realised by a real polynomial of degree at most six.  Take the
-- complex Lagrange interpolant `L`, and the real parts of its coefficients: at a node `ν`,
-- `Σ_k Re(L.coeff k) ν^k = (L(ν) + conj (L (conj ν)))/2 = (r ν + conj (r (conj ν)))/2 = r ν`.
theorem exists_real_interp (N : Finset ℂ) (hN : N.card ≤ 7)
    (hc : ∀ ν ∈ N, star ν ∈ N) (r : ℂ → ℂ) (hr : ∀ ν ∈ N, r (star ν) = star (r ν)) :
    ∃ c : Fin 7 → ℝ, ∀ ν ∈ N, ∑ k : Fin 7, (c k : ℂ) * ν ^ (k : ℕ) = r ν := by
  classical
  let L : ℂ[X] := Lagrange.interpolate N id r
  have hinj : Set.InjOn (id : ℂ → ℂ) ↑N := fun a _ b _ hab => hab
  have hL : ∀ ν ∈ N, L.eval ν = r ν :=
    fun ν hν => Lagrange.eval_interpolate_at_node r hinj hν
  have hdeg : L.degree < (N.card : WithBot ℕ) := Lagrange.degree_interpolate_lt r hinj
  have hcoeff0 : ∀ j : ℕ, 7 ≤ j → L.coeff j = 0 := by
    intro j hj
    refine Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hdeg ?_)
    calc (N.card : WithBot ℕ) ≤ (7 : ℕ) := by exact_mod_cast hN
      _ ≤ (j : WithBot ℕ) := by exact_mod_cast hj
  let F : ℂ[X] := ∑ k : Fin 7,
    Polynomial.C ((L.coeff (k : ℕ)).re : ℂ) * Polynomial.X ^ (k : ℕ)
  have hFcoeff : ∀ j : ℕ, F.coeff j = ((L.coeff j).re : ℂ) := by
    intro j
    rcases lt_or_ge j 7 with hj | hj
    · simp only [F, Polynomial.finsetSum_coeff]
      rw [Finset.sum_eq_single ⟨j, hj⟩]
      · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl]
        simp
      · intro k _ hk
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
          if_neg (by intro h; exact hk (Fin.ext h.symm))]
        ring
      · intro hk
        exact absurd (Finset.mem_univ _) hk
    · have hz : ((L.coeff j).re : ℂ) = 0 := by rw [hcoeff0 j hj]; simp
      rw [hz]
      simp only [F, Polynomial.finsetSum_coeff]
      refine Finset.sum_eq_zero (fun k _ => ?_)
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        if_neg (by intro h; exact absurd h (by have := k.isLt; omega))]
      ring
  have hGcoeff : ∀ j : ℕ,
      (Polynomial.C (1 / 2 : ℂ) * (L + L.map (starRingEnd ℂ))).coeff j
        = ((L.coeff j).re : ℂ) := by
    intro j
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_add, Polynomial.coeff_map, Complex.add_conj]
    push_cast
    ring
  have hFG : F = Polynomial.C (1 / 2 : ℂ) * (L + L.map (starRingEnd ℂ)) := by
    ext j
    rw [hFcoeff j, hGcoeff j]
  refine ⟨fun k => (L.coeff (k : ℕ)).re, fun ν hν => ?_⟩
  have hFeval : F.eval ν = ∑ k : Fin 7, ((L.coeff (k : ℕ)).re : ℂ) * ν ^ (k : ℕ) := by
    simp only [F, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
  have hmap : (L.map (starRingEnd ℂ)).eval ν = star (L.eval (star ν)) := by
    have h := Polynomial.eval_map_apply (starRingEnd ℂ) (star ν) (p := L)
    simpa using h
  have hGval : (Polynomial.C (1 / 2 : ℂ) * (L + L.map (starRingEnd ℂ))).eval ν
      = (r ν + r ν) * (1 / 2 : ℂ) := by
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add, hmap, hL ν hν,
      hL (star ν) (hc ν hν), hr ν hν, star_star]
    ring
  rw [← hFeval, hFG, hGval]
  ring

/-! ### Root bookkeeping for a monic separable nonic -/

-- Theorem: mapping `q` to `ℂ` and then conjugating is the same as mapping directly.
theorem qmap_star (q : ℚ[X]) :
    (q.map (algebraMap ℚ ℂ)).map (starRingEnd ℂ) = q.map (algebraMap ℚ ℂ) := by
  rw [Polynomial.map_map]
  congr 1
  ext r
  simp

-- Theorem: the complexification of `q : ℚ[X]` is conjugation-equivariant on evaluations.
theorem qmap_star_eval (q : ℚ[X]) (ρ : ℂ) :
    (q.map (algebraMap ℚ ℂ)).eval (star ρ) = star ((q.map (algebraMap ℚ ℂ)).eval ρ) := by
  have h := Polynomial.eval_map_apply (starRingEnd ℂ) ρ (p := q.map (algebraMap ℚ ℂ))
  rwa [qmap_star] at h

-- Theorem: the complexification of a monic `q` is nonzero.
theorem qmap_ne_zero {q : ℚ[X]} (hmon : q.Monic) : q.map (algebraMap ℚ ℂ) ≠ 0 := by
  intro h
  exact hmon.ne_zero (Polynomial.map_injective (algebraMap ℚ ℂ)
    (algebraMap ℚ ℂ).injective (by rw [h, Polynomial.map_zero]))

-- Theorem: the roots of a separable polynomial are distinct.
theorem roots_nodup {q : ℚ[X]} (hsep : q.Separable) :
    (q.map (algebraMap ℚ ℂ)).roots.Nodup :=
  Polynomial.nodup_roots (hsep.map (f := algebraMap ℚ ℂ))

-- Theorem: a nonic has nine complex roots.
theorem roots_card {q : ℚ[X]} (h9 : q.natDegree = 9) :
    (q.map (algebraMap ℚ ℂ)).roots.card = 9 := by
  have hnat : (q.map (algebraMap ℚ ℂ)).natDegree = 9 := by
    rw [Polynomial.natDegree_map_eq_of_injective (algebraMap ℚ ℂ).injective]; exact h9
  rw [← hnat]
  exact (IsAlgClosed.splits _).natDegree_eq_card_roots.symm

-- Theorem: the complex roots of a rational polynomial are closed under conjugation.
theorem roots_conj_mem {q : ℚ[X]} {ρ : ℂ} (hmon : q.Monic)
    (hρ : ρ ∈ (q.map (algebraMap ℚ ℂ)).roots) :
    star ρ ∈ (q.map (algebraMap ℚ ℂ)).roots := by
  rw [Polynomial.mem_roots (qmap_ne_zero hmon)] at hρ ⊢
  have hρ' : (q.map (algebraMap ℚ ℂ)).eval ρ = 0 := hρ
  change (q.map (algebraMap ℚ ℂ)).eval (star ρ) = 0
  rw [qmap_star_eval, hρ']
  simp

/-! ### Evaluating `spreadCore` on a two-point support -/

-- Theorem: if `g` takes the values `i` and `-i` at two points `z, w` of `R` and vanishes on
-- the rest, then `spreadCore R g = -2`: the squared sum is `i² + (-i)² = -2` and the linear
-- sum is `i + (-i) = 0`.
theorem spreadCore_pair_neg {R : Finset ℂ} {z w : ℂ} {g : ℂ → ℂ}
    (hz : z ∈ R) (hw : w ∈ R) (hzw : z ≠ w)
    (hval : ∀ ρ ∈ R, ρ ≠ z → ρ ≠ w → g ρ = 0)
    (hgz : g z = Complex.I) (hgw : g w = -Complex.I) :
    spreadCore R g = -2 := by
  unfold spreadCore
  have hsub : ({z, w} : Finset ℂ) ⊆ R := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hz
    · rw [Finset.mem_singleton] at hx; rw [hx]; exact hw
  have hzero1 : ∀ x ∈ R, x ∉ ({z, w} : Finset ℂ) → g x = 0 := by
    intro x hx hxnot
    refine hval x hx ?_ ?_
    · intro h; exact hxnot (by rw [h]; exact Finset.mem_insert_self z {w})
    · intro h; exact hxnot (by rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self w))
  have hzero2 : ∀ x ∈ R, x ∉ ({z, w} : Finset ℂ) → g x ^ 2 = 0 :=
    fun x hx hxnot => by rw [hzero1 x hx hxnot]; ring
  have hpairg : (∑ x ∈ ({z, w} : Finset ℂ), g x) = g z + g w := Finset.sum_pair hzw
  have hpairg2 : (∑ x ∈ ({z, w} : Finset ℂ), g x ^ 2) = g z ^ 2 + g w ^ 2 :=
    Finset.sum_pair hzw
  have h1 : (∑ ρ ∈ R, g ρ) = 0 := by
    rw [← Finset.sum_subset hsub hzero1, hpairg, hgz, hgw]
    simp
  have h2 : (∑ ρ ∈ R, g ρ ^ 2) = -2 := by
    rw [← Finset.sum_subset hsub hzero2, hpairg2, hgz, hgw, sq, sq, Complex.I_mul_I,
      neg_mul_neg, Complex.I_mul_I]
    norm_num
  rw [h1, h2]
  norm_num

-- Theorem: if `g` takes the value `1` at two points `z, w` of `R` and vanishes on the rest,
-- then `spreadCore R g = 2 - 4/9 = 14/9`.
theorem spreadCore_pair_pos {R : Finset ℂ} {z w : ℂ} {g : ℂ → ℂ}
    (hz : z ∈ R) (hw : w ∈ R) (hzw : z ≠ w)
    (hval : ∀ ρ ∈ R, ρ ≠ z → ρ ≠ w → g ρ = 0)
    (hgz : g z = 1) (hgw : g w = 1) :
    spreadCore R g = 2 - 4 / 9 := by
  unfold spreadCore
  have hsub : ({z, w} : Finset ℂ) ⊆ R := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hz
    · rw [Finset.mem_singleton] at hx; rw [hx]; exact hw
  have hzero1 : ∀ x ∈ R, x ∉ ({z, w} : Finset ℂ) → g x = 0 := by
    intro x hx hxnot
    refine hval x hx ?_ ?_
    · intro h; exact hxnot (by rw [h]; exact Finset.mem_insert_self z {w})
    · intro h; exact hxnot (by rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self w))
  have hzero2 : ∀ x ∈ R, x ∉ ({z, w} : Finset ℂ) → g x ^ 2 = 0 :=
    fun x hx hxnot => by rw [hzero1 x hx hxnot]; ring
  have hpairg : (∑ x ∈ ({z, w} : Finset ℂ), g x) = g z + g w := Finset.sum_pair hzw
  have hpairg2 : (∑ x ∈ ({z, w} : Finset ℂ), g x ^ 2) = g z ^ 2 + g w ^ 2 :=
    Finset.sum_pair hzw
  have h1 : (∑ ρ ∈ R, g ρ) = 2 := by
    rw [← Finset.sum_subset hsub hzero1, hpairg, hgz, hgw]
    norm_num
  have h2 : (∑ ρ ∈ R, g ρ ^ 2) = 2 := by
    rw [← Finset.sum_subset hsub hzero2, hpairg2, hgz, hgw]
    norm_num
  rw [h1, h2]
  norm_num

/-! ### A generic real `t` for the collapsed value map -/

-- Theorem: for any finite set `B` of reals, `1 + Σ_{x ∈ B} |x|` lies outside `B`.
theorem one_add_sum_abs_notMem (B : Finset ℝ) : 1 + ∑ x ∈ B, |x| ∉ B := by
  intro h
  have hle : abs (1 + ∑ x ∈ B, |x|) ≤ ∑ x ∈ B, |x| :=
    Finset.single_le_sum (fun x _ => abs_nonneg x) h
  have hsum : 0 ≤ ∑ x ∈ B, |x| := Finset.sum_nonneg (fun x _ => abs_nonneg x)
  have hpos : 0 < 1 + ∑ x ∈ B, |x| := by linarith
  rw [abs_of_pos hpos] at hle
  linarith

-- Theorem: there is a real `t` for which `ψ₀ = (X - t) · D` takes a nonreal value at the
-- nonreal root `z` and no other root of `q` maps to the same value.  The excluded values of
-- `t` are finitely many explicit candidates, and `1 + Σ |candidate|` avoids them all.
theorem exists_good_t {q : ℚ[X]} {D : ℝ[X]} {z : ℂ}
    (hzim : z.im ≠ 0) (hDz : (D.map (algebraMap ℝ ℂ)).eval z ≠ 0) :
    ∃ t : ℝ,
      ((z - (t : ℂ)) * (D.map (algebraMap ℝ ℂ)).eval z).im ≠ 0 ∧
      ∀ ρ ∈ (q.map (algebraMap ℚ ℂ)).roots, ρ ≠ z →
        (ρ - (t : ℂ)) * (D.map (algebraMap ℝ ℂ)).eval ρ
          ≠ (z - (t : ℂ)) * (D.map (algebraMap ℝ ℂ)).eval z := by
  classical
  set E : ℂ[X] := D.map (algebraMap ℝ ℂ) with hE
  set ta : ℝ := (z * E.eval z).im / (E.eval z).im with hta
  set tρ : ℂ → ℝ := fun ρ =>
    if E.eval ρ = E.eval z then 0
    else ((ρ * E.eval ρ - z * E.eval z) / (E.eval ρ - E.eval z)).re with htρ
  set B : Finset ℝ := insert ta (((q.map (algebraMap ℚ ℂ)).roots.toFinset).image tρ) with hB
  set t : ℝ := 1 + ∑ x ∈ B, |x| with htdef
  have htB : t ∉ B := by rw [htdef]; exact one_add_sum_abs_notMem B
  refine ⟨t, ?_, ?_⟩
  · have hta_mem : ta ∈ B := by rw [hB]; exact Finset.mem_insert_self _ _
    have ht_ne_ta : t ≠ ta := fun hh => htB (hh ▸ hta_mem)
    have him : ((z - (t : ℂ)) * E.eval z).im = (z * E.eval z).im - t * (E.eval z).im := by
      simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
        Complex.ofReal_im]
      ring
    rw [him]
    by_cases hDaim : (E.eval z).im = 0
    · rw [hDaim, mul_zero, sub_zero]
      have hDare : (E.eval z).re ≠ 0 := by
        intro h0
        exact hDz (by rw [Complex.ext_iff]; exact ⟨h0, hDaim⟩)
      rw [show (z * E.eval z).im = z.im * (E.eval z).re by
        rw [Complex.mul_im, hDaim, mul_zero, zero_add]]
      exact mul_ne_zero hzim hDare
    · intro hzero
      have ht_eq : t = (z * E.eval z).im / (E.eval z).im := by
        rw [eq_div_iff hDaim]
        linarith
      exact ht_ne_ta (by rw [hta]; exact ht_eq)
  · intro ρ hρ hρz hcoll
    have htrho_mem : tρ ρ ∈ B := by
      rw [hB]
      exact Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨ρ, Multiset.mem_toFinset.mpr hρ, rfl⟩)
    have ht_ne_tρ : t ≠ tρ ρ := fun hh => htB (hh ▸ htrho_mem)
    have hsub : (ρ - (t : ℂ)) * E.eval ρ - (z - (t : ℂ)) * E.eval z
        = (ρ * E.eval ρ - z * E.eval z) - (t : ℂ) * (E.eval ρ - E.eval z) := by
      ring
    have hz0 : (ρ * E.eval ρ - z * E.eval z) - (t : ℂ) * (E.eval ρ - E.eval z) = 0 := by
      rw [← hsub, hcoll, sub_self]
    by_cases hEq : E.eval ρ = E.eval z
    · rw [hEq, sub_self, mul_zero, sub_zero] at hz0
      have hfac : (ρ - z) * E.eval z = 0 := by rw [← hz0]; ring
      rcases mul_eq_zero.mp hfac with h | h
      · exact hρz (sub_eq_zero.mp h)
      · exact hDz h
    · have h1 : E.eval ρ - E.eval z ≠ 0 := sub_ne_zero.mpr hEq
      have hquot : (ρ * E.eval ρ - z * E.eval z) / (E.eval ρ - E.eval z) = (t : ℂ) := by
        rw [div_eq_iff h1]
        exact sub_eq_zero.mp hz0
      have hre : ((ρ * E.eval ρ - z * E.eval z) / (E.eval ρ - E.eval z)).re = t := by
        rw [hquot, Complex.ofReal_re]
      refine ht_ne_tρ ?_
      rw [htρ]
      simp only [if_neg hEq]
      exact hre.symm

end
end Pconstructible
