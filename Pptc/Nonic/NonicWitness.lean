import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.Constructions.SumProd

/-! # Pptc.Nonic.NonicWitness — the real-collision witness for the nonic Tschirnhaus reduction

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

/-! ### A real quadratic through a complex number and its conjugate -/

/-- `quad w = X² - 2 Re(w)·X + |w|²`, the real quadratic with roots `w` and `w̄`. -/
def quad (w : ℂ) : ℝ[X] := X ^ 2 - C (2 * w.re) * X + C (w.re ^ 2 + w.im ^ 2)

-- Lemma: the complexification of `quad w` is `(X - w) * (X - w̄)`.
theorem quad_map (w : ℂ) :
    (quad w).map (algebraMap ℝ ℂ) = (X - C w) * (X - C (star w)) := by
  have h1 : ((2 * w.re : ℝ) : ℂ) = w + star w := (Complex.add_conj w).symm
  have h2 : ((w.re ^ 2 + w.im ^ 2 : ℝ) : ℂ) = w * star w := by
    rw [← starRingEnd_apply, Complex.mul_conj w, Complex.normSq_apply]
    congr 1
    ring
  rw [quad]
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C]
  change X ^ 2 - C (((2 * w.re : ℝ) : ℂ)) * X + C (((w.re ^ 2 + w.im ^ 2 : ℝ) : ℂ))
    = (X - C w) * (X - C (star w))
  rw [h1, h2, Polynomial.C_add, Polynomial.C_mul]
  ring

-- Lemma: `quad w` is monic.
theorem quad_monic (w : ℂ) : (quad w).Monic := by
  have h : ((quad w).map (algebraMap ℝ ℂ)).Monic := by
    rw [quad_map]
    exact (monic_X_sub_C w).mul (monic_X_sub_C (star w))
  have hlc : (quad w).leadingCoeff = 1 := by
    apply (algebraMap ℝ ℂ).injective
    rw [map_one, ← Polynomial.leadingCoeff_map (p := quad w) (algebraMap ℝ ℂ)]
    exact h
  exact hlc

-- Lemma: `quad w` has degree two.
theorem quad_natDegree (w : ℂ) : (quad w).natDegree = 2 := by
  have h : ((quad w).map (algebraMap ℝ ℂ)).natDegree = 2 := by
    rw [quad_map, Polynomial.Monic.natDegree_mul (monic_X_sub_C w) (monic_X_sub_C (star w)),
      Polynomial.natDegree_X_sub_C, Polynomial.natDegree_X_sub_C]
  rwa [Polynomial.natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective] at h

-- Lemma: `quad w` does not vanish at `z` when `z ∉ {w, w̄}`.
theorem quad_map_eval_ne {z w : ℂ} (h1 : z ≠ w) (h2 : z ≠ star w) :
    ((quad w).map (algebraMap ℝ ℂ)).eval z ≠ 0 := by
  rw [quad_map]
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  exact mul_ne_zero (sub_ne_zero.mpr h1) (sub_ne_zero.mpr h2)

/-! ### Evaluation helpers for real polynomials on `ℂ` -/

-- Lemma: evaluating a complexified real polynomial commutes with conjugation.
theorem eval_star (p : ℝ[X]) (ρ : ℂ) :
    (p.map (algebraMap ℝ ℂ)).eval ((starRingEnd ℂ) ρ)
      = (starRingEnd ℂ) ((p.map (algebraMap ℝ ℂ)).eval ρ) := by
  have h : (p.map (algebraMap ℝ ℂ)).map (starRingEnd ℂ) = p.map (algebraMap ℝ ℂ) := by
    rw [Polynomial.map_map]
    congr 1
    ext r
    simp
  have := Polynomial.eval_map_apply (starRingEnd ℂ) ρ (p := p.map (algebraMap ℝ ℂ))
  rwa [h] at this

-- Lemma: a real polynomial of degree at most six is the sum of its first seven monomials.
theorem map_eq_sum_fin7 {p : ℝ[X]} (hp : p.natDegree ≤ 6) :
    p.map (algebraMap ℝ ℂ)
      = ∑ j : Fin 7, Polynomial.C ((p.coeff (j : ℕ) : ℂ)) * Polynomial.X ^ (j : ℕ) := by
  ext n
  rw [Polynomial.coeff_map]
  rcases lt_or_ge n 7 with hn | hn
  · simp only [Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single ⟨n, hn⟩]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
      simp
    · intro k _ hk
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        if_neg (by intro h; exact hk (Fin.ext h.symm))]
      ring
    · intro hk; exact absurd (Finset.mem_univ _) hk
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero]
    symm
    simp only [Polynomial.finsetSum_coeff]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      if_neg (by intro h; omega)]
    ring

-- Lemma: the complex evaluation of a real polynomial of degree at most six is the
-- coefficient sum against `ρ`.
theorem eval_map_eq_sum_fin7 {p : ℝ[X]} (hp : p.natDegree ≤ 6) (ρ : ℂ) :
    (p.map (algebraMap ℝ ℂ)).eval ρ
      = ∑ j : Fin 7, (p.coeff (j : ℕ) : ℂ) * ρ ^ (j : ℕ) := by
  rw [map_eq_sum_fin7 hp, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

-- Lemma: unfolding `spread`.
theorem spread_def (q : ℚ[X]) (ψ : Fin 7 → ℝ) (v : Fin 6 → ℝ) :
    spread q ψ v = spreadCore ((q.map (algebraMap ℚ ℂ)).roots.toFinset)
      (fun z => ∑ k : Fin 6, (v k : ℂ)
        * (∑ j : Fin 7, (ψ j : ℂ) * z ^ (j : ℕ)) ^ (k.val + 1)) := by
  unfold spread
  rfl

/-! ### The real divisor of `q` with three conjugate-closed roots avoiding `z` -/

-- Theorem: a monic separable nonic with a nonreal root `z` has a monic real divisor `D` of
-- degree three or four, with `D(z) ≠ 0` and with three distinct roots of `q` that `D` kills.
-- The seven roots of `q` other than `z, z̄` are used: if one of them is nonreal, we take its
-- conjugate pair together with one further root (the product of the two `quad`s); otherwise
-- all seven are real and we take three of them.
theorem exists_real_divisor {q : ℚ[X]} (hmon : q.Monic) (h9 : q.natDegree = 9)
    (hsep : q.Separable) {z : ℂ}
    (hz : (q.map (algebraMap ℚ ℂ)).eval z = 0) (hzim : z.im ≠ 0) :
    ∃ D : ℝ[X], D.Monic ∧ 3 ≤ D.natDegree ∧ D.natDegree ≤ 4 ∧
      (D.map (algebraMap ℝ ℂ)).eval z ≠ 0 ∧
      ∃ T : Finset ℂ, T.card = 3 ∧ T ⊆ (q.map (algebraMap ℚ ℂ)).roots.toFinset ∧
        (∀ ρ ∈ T, (D.map (algebraMap ℝ ℂ)).eval ρ = 0) := by
  classical
  have hqmon : (q.map (algebraMap ℚ ℂ)).Monic := hmon.map (algebraMap ℚ ℂ)
  set R : Finset ℂ := (q.map (algebraMap ℚ ℂ)).roots.toFinset with hR
  have hRcard : R.card = 9 := by
    rw [hR, Multiset.toFinset_card_of_nodup (roots_nodup hsep), roots_card h9]
  have hRconj : ∀ ρ ∈ R, star ρ ∈ R := by
    intro ρ hρ
    rw [hR] at hρ ⊢
    exact Multiset.mem_toFinset.mpr (roots_conj_mem hmon (Multiset.mem_toFinset.mp hρ))
  have hzR : z ∈ R := by
    rw [hR]
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (qmap_ne_zero hmon)).mpr hz)
  have hzbarR : star z ∈ R := hRconj z hzR
  have hznezbar : z ≠ star z := by
    intro h
    exact hzim (Complex.conj_eq_iff_im.mp h.symm)
  set S : Finset ℂ := (R.erase z).erase (star z) with hS
  have hScard : S.card = 7 := by
    rw [hS, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hznezbar.symm, hzbarR⟩),
      Finset.card_erase_of_mem hzR, hRcard]
  have hS_sub : ∀ ⦃x : ℂ⦄, x ∈ S → x ∈ R := by
    intro x hx
    rw [hS] at hx
    exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)
  have hS_nz : ∀ ⦃x : ℂ⦄, x ∈ S → x ≠ z := by
    intro x hx
    rw [hS] at hx
    exact (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
  have hS_nsz : ∀ ⦃x : ℂ⦄, x ∈ S → x ≠ star z := by
    intro x hx
    rw [hS] at hx
    exact (Finset.mem_erase.mp hx).1
  have hSconj : ∀ w ∈ S, star w ∈ S := by
    intro w hw
    have hwsz : w ≠ star z := hS_nsz hw
    have hwz : w ≠ z := hS_nz hw
    rw [hS]
    exact Finset.mem_erase.mpr ⟨fun h => hwz (star_injective h),
      Finset.mem_erase.mpr ⟨fun h => hwsz (by have := congrArg star h; simpa using this),
        hRconj w (hS_sub hw)⟩⟩
  by_cases hne : ∃ w ∈ S, star w ≠ w
  · obtain ⟨w, hwS, hwne⟩ := hne
    have hwz : w ≠ z := hS_nz hwS
    have hwsz : w ≠ star z := hS_nsz hwS
    have hwR : w ∈ R := hS_sub hwS
    have hσ : ∃ σ ∈ S, σ ≠ w ∧ σ ≠ star w := by
      by_contra h
      have hsub : S ⊆ ({w, star w} : Finset ℂ) := by
        intro x hx
        by_contra hxnot
        have hxw : x ≠ w := fun hh =>
          hxnot (by rw [hh]; exact Finset.mem_insert_self w {star w})
        have hxsw : x ≠ star w := fun hh =>
          hxnot (by rw [hh]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self (star w)))
        exact h ⟨x, hx, hxw, hxsw⟩
      have h2 : ({w, star w} : Finset ℂ).card ≤ 2 := by
        simpa using Finset.card_insert_le w ({star w} : Finset ℂ)
      have := Finset.card_le_card hsub
      rw [hScard] at this
      omega
    obtain ⟨σ, hσS, hσw, hσsw⟩ := hσ
    have hσz : σ ≠ z := hS_nz hσS
    have hσsz : σ ≠ star z := hS_nsz hσS
    have hσR : σ ∈ R := hS_sub hσS
    have hzsw : z ≠ star w := by
      intro h; exact hwsz (by have := congrArg star h; simpa using this.symm)
    have hzsσ : z ≠ star σ := by
      intro h; exact hσsz (by have := congrArg star h; simpa using this.symm)
    have hDmon : (quad w * quad σ).Monic := (quad_monic w).mul (quad_monic σ)
    have hDnat : (quad w * quad σ).natDegree = 4 := by
      rw [Polynomial.Monic.natDegree_mul (quad_monic w) (quad_monic σ), quad_natDegree,
        quad_natDegree]
    have hDmap : (quad w * quad σ).map (algebraMap ℝ ℂ)
        = (X - C w) * (X - C (star w)) * (X - C σ) * (X - C (star σ)) := by
      rw [Polynomial.map_mul, quad_map, quad_map]
      ring
    refine ⟨quad w * quad σ, hDmon, ?_, ?_, ?_, ?_⟩
    · rw [hDnat]; norm_num
    · rw [hDnat]
    · rw [hDmap]
      simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hwz.symm)
        (sub_ne_zero.mpr hzsw)) (sub_ne_zero.mpr hσz.symm)) (sub_ne_zero.mpr hzsσ)
    · refine ⟨{w, star w, σ}, ?_, ?_, ?_⟩
      · exact Finset.card_eq_three.mpr ⟨w, star w, σ, hwne.symm, hσw.symm, hσsw.symm, rfl⟩
      · intro ρ hρ
        rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hρ
        rcases hρ with rfl | rfl | rfl
        · exact hwR
        · exact hRconj w hwR
        · exact hσR
      · intro ρ hρ
        rw [hDmap]
        rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hρ
        rcases hρ with rfl | rfl | rfl
        · simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
            Polynomial.eval_C]
          ring
        · simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
            Polynomial.eval_C]
          ring
        · simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
            Polynomial.eval_C]
          ring
  · simp only [not_exists, not_and, not_not] at hne
    obtain ⟨r₁, hr₁⟩ := Finset.card_pos.mp (by rw [hScard]; norm_num)
    have hr₁S : r₁ ∈ S := hr₁
    have h2 : (S.erase r₁).Nonempty :=
      Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hr₁, hScard]; norm_num)
    obtain ⟨r₂, hr₂⟩ := h2
    have hr₂S : r₂ ∈ S := Finset.mem_of_mem_erase hr₂
    have h21 : r₂ ≠ r₁ := (Finset.mem_erase.mp hr₂).1
    have h3 : ((S.erase r₁).erase r₂).Nonempty :=
      Finset.card_pos.mp (by
        rw [Finset.card_erase_of_mem hr₂, Finset.card_erase_of_mem hr₁, hScard]; norm_num)
    obtain ⟨r₃, hr₃⟩ := h3
    have hr₃S : r₃ ∈ S := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hr₃)
    have h31 : r₃ ≠ r₁ := (Finset.mem_erase.mp (Finset.mem_erase.mp hr₃).2).1
    have h32 : r₃ ≠ r₂ := (Finset.mem_erase.mp hr₃).1
    have hr₁z : r₁ ≠ z := hS_nz hr₁S
    have hr₂z : r₂ ≠ z := hS_nz hr₂S
    have hr₃z : r₃ ≠ z := hS_nz hr₃S
    have hr₁R : r₁ ∈ R := hS_sub hr₁S
    have hr₂R : r₂ ∈ R := hS_sub hr₂S
    have hr₃R : r₃ ∈ R := hS_sub hr₃S
    have hs₁ : (↑r₁.re : ℂ) = r₁ := by
      have him : r₁.im = 0 := Complex.conj_eq_iff_im.mp (hne r₁ hr₁S)
      rw [Complex.ext_iff]; exact ⟨by simp, by simp [him]⟩
    have hs₂ : (↑r₂.re : ℂ) = r₂ := by
      have him : r₂.im = 0 := Complex.conj_eq_iff_im.mp (hne r₂ hr₂S)
      rw [Complex.ext_iff]; exact ⟨by simp, by simp [him]⟩
    have hs₃ : (↑r₃.re : ℂ) = r₃ := by
      have him : r₃.im = 0 := Complex.conj_eq_iff_im.mp (hne r₃ hr₃S)
      rw [Complex.ext_iff]; exact ⟨by simp, by simp [him]⟩
    have hDmon : ((X - C r₁.re) * (X - C r₂.re) * (X - C r₃.re)).Monic :=
      ((monic_X_sub_C r₁.re).mul (monic_X_sub_C r₂.re)).mul (monic_X_sub_C r₃.re)
    have hDnat : ((X - C r₁.re) * (X - C r₂.re) * (X - C r₃.re)).natDegree = 3 := by
      rw [Polynomial.Monic.natDegree_mul ((monic_X_sub_C r₁.re).mul (monic_X_sub_C r₂.re))
            (monic_X_sub_C r₃.re),
          Polynomial.Monic.natDegree_mul (monic_X_sub_C r₁.re) (monic_X_sub_C r₂.re),
          Polynomial.natDegree_X_sub_C, Polynomial.natDegree_X_sub_C,
          Polynomial.natDegree_X_sub_C]
    have hDmap : ((X - C r₁.re) * (X - C r₂.re) * (X - C r₃.re)).map (algebraMap ℝ ℂ)
        = (X - C r₁) * (X - C r₂) * (X - C r₃) := by
      simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      rw [show (algebraMap ℝ ℂ) r₁.re = r₁ from hs₁,
        show (algebraMap ℝ ℂ) r₂.re = r₂ from hs₂,
        show (algebraMap ℝ ℂ) r₃.re = r₃ from hs₃]
    refine ⟨(X - C r₁.re) * (X - C r₂.re) * (X - C r₃.re), hDmon, ?_, ?_, ?_, ?_⟩
    · rw [hDnat]
    · rw [hDnat]; norm_num
    · rw [hDmap]
      simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hr₁z.symm) (sub_ne_zero.mpr hr₂z.symm))
        (sub_ne_zero.mpr hr₃z.symm)
    · refine ⟨{r₁, r₂, r₃}, ?_, ?_, ?_⟩
      · exact Finset.card_eq_three.mpr ⟨r₁, r₂, r₃, h21.symm, h31.symm, h32.symm, rfl⟩
      · intro ρ hρ
        rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hρ
        rcases hρ with rfl | rfl | rfl
        · exact hr₁R
        · exact hr₂R
        · exact hr₃R
      · intro ρ hρ
        rw [hDmap]
        rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hρ
        rcases hρ with rfl | rfl | rfl
        · simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
            Polynomial.eval_C]
          ring
        · simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
            Polynomial.eval_C]
          ring
        · simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
            Polynomial.eval_C]
          ring

/-! ### The two target functions and the assembly of `exists_real_signs` -/

/-- Target for the negative witness: `i` at `w`, `-i` at `w̄`, `0` elsewhere. -/
def targetNeg (w : ℂ) : ℂ → ℂ :=
  fun ν => if ν = w then Complex.I
    else if ν = (starRingEnd ℂ) w then -Complex.I else 0

/-- Target for the positive witness: `1` at `w` and `w̄`, `0` elsewhere. -/
def targetPos (w : ℂ) : ℂ → ℂ :=
  fun ν => if ν = w then 1 else if ν = (starRingEnd ℂ) w then 1 else 0

-- Lemma: `spreadCore` only depends on the values of `g` on `R`.
theorem spreadCore_congr {R : Finset ℂ} {g h : ℂ → ℂ} (H : ∀ ρ ∈ R, g ρ = h ρ) :
    spreadCore R g = spreadCore R h := by
  have h1 : (∑ ρ ∈ R, g ρ ^ 2) = ∑ ρ ∈ R, h ρ ^ 2 :=
    Finset.sum_congr rfl (fun ρ hρ => by rw [H ρ hρ])
  have h2 : (∑ ρ ∈ R, g ρ) = ∑ ρ ∈ R, h ρ :=
    Finset.sum_congr rfl (fun ρ hρ => H ρ hρ)
  unfold spreadCore
  rw [h1, h2]

-- Lemma: conjugation commutes with `if`, and `conj i = -i`.
theorem conj_ite (c : Prop) [Decidable c] (a b : ℂ) :
    (starRingEnd ℂ) (if c then a else b)
      = if c then (starRingEnd ℂ) a else (starRingEnd ℂ) b :=
  apply_ite (starRingEnd ℂ) c a b

theorem conj_I : (starRingEnd ℂ) Complex.I = -Complex.I := Complex.conj_I

-- Lemma: `targetNeg w` is conjugation-equivariant when `w` is nonreal.
theorem targetNeg_conj {w : ℂ} (hw : (starRingEnd ℂ) w ≠ w) (ν : ℂ) :
    targetNeg w ((starRingEnd ℂ) ν) = (starRingEnd ℂ) (targetNeg w ν) := by
  unfold targetNeg
  rw [conj_ite]
  by_cases h1 : ν = w
  · subst h1; simp [hw]
  · by_cases h2 : ν = (starRingEnd ℂ) w
    · subst h2; simp [hw]
    · have hsvw : (starRingEnd ℂ) ν ≠ w := fun h => h2 (by rw [← h]; simp)
      have hsvsw : (starRingEnd ℂ) ν ≠ (starRingEnd ℂ) w :=
        fun h => h1 ((starRingEnd ℂ).injective h)
      simp [h1, h2, hsvw, hsvsw]

-- Lemma: `targetPos w` is conjugation-equivariant when `w` is nonreal.
theorem targetPos_conj {w : ℂ} (hw : (starRingEnd ℂ) w ≠ w) (ν : ℂ) :
    targetPos w ((starRingEnd ℂ) ν) = (starRingEnd ℂ) (targetPos w ν) := by
  unfold targetPos
  rw [conj_ite]
  by_cases h1 : ν = w
  · subst h1; simp [hw]
  · by_cases h2 : ν = (starRingEnd ℂ) w
    · subst h2; simp [hw]
    · have hsvw : (starRingEnd ℂ) ν ≠ w := fun h => h2 (by rw [← h]; simp)
      have hsvsw : (starRingEnd ℂ) ν ≠ (starRingEnd ℂ) w :=
        fun h => h1 ((starRingEnd ℂ).injective h)
      simp [h1, h2, hsvw, hsvsw]

-- Lemma: `targetNeg w` vanishes away from `w` and `w̄`.
theorem targetNeg_zero {w ν : ℂ} (h1 : ν ≠ w) (h2 : ν ≠ (starRingEnd ℂ) w) :
    targetNeg w ν = 0 := by
  simp only [targetNeg, if_neg h1, if_neg h2]

-- Lemma: `targetPos w` vanishes away from `w` and `w̄`.
theorem targetPos_zero {w ν : ℂ} (h1 : ν ≠ w) (h2 : ν ≠ (starRingEnd ℂ) w) :
    targetPos w ν = 0 := by
  simp only [targetPos, if_neg h1, if_neg h2]

-- Theorem: a monic separable nonic with a nonreal root `z` has real witnesses of both signs.
-- The divisor `D` of `exists_real_divisor` collapses three roots of `q` onto `0`, giving a
-- node set `N` of at most seven values; interpolating `±i` and `1` at the two conjugate values
-- `w, w̄ = ψ₀(z), ψ₀(z̄)` produces the two witnesses.
theorem exists_real_signs {q : ℚ[X]} (hmon : q.Monic) (h9 : q.natDegree = 9)
    (hsep : q.Separable)
    (hrel : ∃ z : ℂ, (q.map (algebraMap ℚ ℂ)).eval z = 0 ∧ z.im ≠ 0) :
    ∃ (ψ : Fin 7 → ℝ) (vm vp : Fin 6 → ℝ), spread q ψ vm < 0 ∧ 0 < spread q ψ vp := by
  classical
  obtain ⟨z, hz, hzim⟩ := hrel
  obtain ⟨D, hDmon, hD3, hD4, hDz, T, hTcard, hTsub, hTval⟩ :=
    exists_real_divisor hmon h9 hsep hz hzim
  obtain ⟨t, htw, hgood⟩ := exists_good_t (q := q) (D := D) (z := z) hzim hDz
  set ψ₀ : ℝ[X] := (X - C t) * D with hψ₀def
  have hψ₀deg : ψ₀.natDegree ≤ 6 := by
    rw [hψ₀def]
    calc ((X - C t) * D).natDegree ≤ (X - C t).natDegree + D.natDegree :=
          Polynomial.natDegree_mul_le
      _ = 1 + D.natDegree := by rw [Polynomial.natDegree_X_sub_C]
      _ ≤ 6 := by omega
  set ψ : Fin 7 → ℝ := fun j => ψ₀.coeff (j : ℕ) with hψdef
  set R : Finset ℂ := (q.map (algebraMap ℚ ℂ)).roots.toFinset with hRdef
  have hRcard : R.card = 9 := by
    rw [hRdef, Multiset.toFinset_card_of_nodup (roots_nodup hsep), roots_card h9]
  have hRconj : ∀ ρ ∈ R, (starRingEnd ℂ) ρ ∈ R := by
    intro ρ hρ
    rw [hRdef] at hρ ⊢
    exact Multiset.mem_toFinset.mpr (roots_conj_mem hmon (Multiset.mem_toFinset.mp hρ))
  have hzR : z ∈ R := by
    rw [hRdef]
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (qmap_ne_zero hmon)).mpr hz)
  have hzbarR : (starRingEnd ℂ) z ∈ R := hRconj z hzR
  have hznezbar : z ≠ (starRingEnd ℂ) z := by
    intro h; exact hzim (Complex.conj_eq_iff_im.mp h.symm)
  let G : ℂ → ℂ := fun ρ => (ψ₀.map (algebraMap ℝ ℂ)).eval ρ
  have hG_eq : ∀ ρ : ℂ, G ρ = (ρ - (t : ℂ)) * (D.map (algebraMap ℝ ℂ)).eval ρ := by
    intro ρ
    change (ψ₀.map (algebraMap ℝ ℂ)).eval ρ
      = (ρ - (t : ℂ)) * (D.map (algebraMap ℝ ℂ)).eval ρ
    rw [show ψ₀ = (X - C t) * D from hψ₀def, Polynomial.map_mul, Polynomial.eval_mul,
      Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C]
    rfl
  have hG_star : ∀ ρ : ℂ, G ((starRingEnd ℂ) ρ) = (starRingEnd ℂ) (G ρ) := by
    intro ρ
    change (ψ₀.map (algebraMap ℝ ℂ)).eval ((starRingEnd ℂ) ρ)
      = (starRingEnd ℂ) ((ψ₀.map (algebraMap ℝ ℂ)).eval ρ)
    exact eval_star ψ₀ ρ
  let w : ℂ := G z
  have hwim : w.im ≠ 0 := by
    rw [show w = (z - (t : ℂ)) * (D.map (algebraMap ℝ ℂ)).eval z from hG_eq z]
    exact htw
  have hwstar : (starRingEnd ℂ) w ≠ w := by
    intro h; exact hwim (Complex.conj_eq_iff_im.mp h)
  have hGne : ∀ ρ ∈ R, ρ ≠ z → G ρ ≠ w := by
    intro ρ hρR hρz
    rw [hG_eq ρ, show w = (z - (t : ℂ)) * (D.map (algebraMap ℝ ℂ)).eval z from hG_eq z]
    have hρroot : ρ ∈ (q.map (algebraMap ℚ ℂ)).roots := by
      rw [hRdef] at hρR; exact Multiset.mem_toFinset.mp hρR
    exact hgood ρ hρroot hρz
  have hGneStar : ∀ ρ ∈ R, ρ ≠ (starRingEnd ℂ) z → G ρ ≠ (starRingEnd ℂ) w := by
    intro ρ hρR hρsz hcon
    have hρroot : ρ ∈ (q.map (algebraMap ℚ ℂ)).roots := by
      rw [hRdef] at hρR; exact Multiset.mem_toFinset.mp hρR
    have hsρroot : (starRingEnd ℂ) ρ ∈ (q.map (algebraMap ℚ ℂ)).roots :=
      roots_conj_mem hmon hρroot
    have hsρz : (starRingEnd ℂ) ρ ≠ z := by
      intro h; exact hρsz (by rw [← h]; simp)
    have hgood' := hgood ((starRingEnd ℂ) ρ) hsρroot hsρz
    rw [← hG_eq ((starRingEnd ℂ) ρ), ← hG_eq z] at hgood'
    exact hgood' (by rw [hG_star ρ, hcon, Complex.conj_conj])
  let R₁ : Finset ℂ := R.filter (fun ρ => (D.map (algebraMap ℝ ℂ)).eval ρ ≠ 0)
  let N : Finset ℂ := insert 0 (R₁.image G)
  have hG_mem_N : ∀ ρ ∈ R, G ρ ∈ N := by
    intro ρ hρR
    by_cases hDρ : (D.map (algebraMap ℝ ℂ)).eval ρ = 0
    · have hG0 : G ρ = 0 := by rw [hG_eq ρ, hDρ, mul_zero]
      rw [hG0]; exact Finset.mem_insert_self 0 _
    · refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨ρ, ?_, rfl⟩)
      simp only [R₁, Finset.mem_filter]
      exact ⟨hρR, hDρ⟩
  have hTfilter : T ⊆ R.filter (fun ρ => ¬ ((D.map (algebraMap ℝ ℂ)).eval ρ ≠ 0)) := by
    intro ρ hρ
    refine Finset.mem_filter.mpr ⟨hTsub hρ, ?_⟩
    rw [hTval ρ hρ]; simp
  have hNcard : N.card ≤ 7 := by
    have hsum := Finset.card_filter_add_card_filter_not (s := R)
      (p := fun ρ => (D.map (algebraMap ℝ ℂ)).eval ρ ≠ 0)
    rw [hRcard] at hsum
    have h3 : 3 ≤ (R.filter fun ρ => ¬ ((D.map (algebraMap ℝ ℂ)).eval ρ ≠ 0)).card := by
      calc 3 = T.card := hTcard.symm
        _ ≤ _ := Finset.card_le_card hTfilter
    have hR1 : R₁.card ≤ 6 := by
      simp only [R₁]
      omega
    calc N.card = (insert 0 (R₁.image G)).card := rfl
      _ ≤ (R₁.image G).card + 1 := Finset.card_insert_le _ _
      _ ≤ R₁.card + 1 := by
            have := Finset.card_image_le (s := R₁) (f := G); omega
      _ ≤ 6 + 1 := by omega
      _ = 7 := by norm_num
  have hNconj : ∀ ν ∈ N, (starRingEnd ℂ) ν ∈ N := by
    intro ν hν
    rcases Finset.mem_insert.mp hν with rfl | hν
    · simpa only [N, map_zero] using Finset.mem_insert_self (0 : ℂ) (R₁.image G)
    · rcases Finset.mem_image.mp hν with ⟨ρ, hρ, rfl⟩
      obtain ⟨hρR, hρD⟩ : ρ ∈ R ∧ (D.map (algebraMap ℝ ℂ)).eval ρ ≠ 0 := by
        simpa only [R₁, Finset.mem_filter] using hρ
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
        ⟨(starRingEnd ℂ) ρ, by
          simp only [R₁, Finset.mem_filter]
          refine ⟨hRconj ρ hρR, ?_⟩
          rw [eval_star D ρ]
          intro h
          exact hρD ((starRingEnd ℂ).injective (by rw [h, map_zero])), hG_star ρ⟩)
  have hconjN : ∀ ν ∈ N, targetNeg w ((starRingEnd ℂ) ν) = (starRingEnd ℂ) (targetNeg w ν) :=
    fun ν _ => targetNeg_conj hwstar ν
  have hconjP : ∀ ν ∈ N, targetPos w ((starRingEnd ℂ) ν) = (starRingEnd ℂ) (targetPos w ν) :=
    fun ν _ => targetPos_conj hwstar ν
  obtain ⟨cn, hcn⟩ := exists_real_interp N hNcard (fun ν hν => hNconj ν hν) (targetNeg w)
    (fun ν hν => hconjN ν hν)
  obtain ⟨cp, hcp⟩ := exists_real_interp N hNcard (fun ν hν => hNconj ν hν) (targetPos w)
    (fun ν hν => hconjP ν hν)
  have hinner_eq : ∀ z : ℂ, (∑ j : Fin 7, (ψ j : ℂ) * z ^ (j : ℕ)) = G z := by
    intro z
    exact (eval_map_eq_sum_fin7 hψ₀deg z).symm
  -- negative witness
  let Fn : ℂ[X] := ∑ j : Fin 7, Polynomial.C ((cn j : ℂ)) * Polynomial.X ^ (j : ℕ)
  have hFnval : ∀ ν : ℂ, Fn.eval ν = ∑ j : Fin 7, (cn j : ℂ) * ν ^ (j : ℕ) := by
    intro ν
    simp only [Fn, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
  have hFnN : ∀ ν ∈ N, Fn.eval ν = targetNeg w ν := by
    intro ν hν
    rw [hFnval]
    exact hcn ν hν
  have hsumN : ∀ z : ℂ, (∑ k : Fin 6, (cn k.succ : ℂ) * (G z) ^ (k.val + 1))
      = Fn.eval (G z) - (cn 0 : ℂ) := by
    intro z
    rw [hFnval]
    conv_rhs => rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ]
    ring
  have hspread_neg : spread q ψ (fun k => cn k.succ) < 0 := by
    rw [spread_def]
    rw [show (q.map (algebraMap ℚ ℂ)).roots.toFinset = R from hRdef.symm]
    simp_rw [hinner_eq]
    rw [show (fun z => ∑ k : Fin 6, (cn k.succ : ℂ) * (G z) ^ (k.val + 1))
          = (fun z => Fn.eval (G z) - (cn 0 : ℂ)) from funext hsumN]
    change spreadCore R (fun z => Fn.eval (G z) + (-(cn 0 : ℂ))) < 0
    rw [spreadCore_add_const R hRcard (fun z => Fn.eval (G z)) (-(cn 0 : ℂ))]
    rw [spreadCore_congr (fun ρ hρ => hFnN (G ρ) (hG_mem_N ρ hρ))]
    rw [spreadCore_pair_neg hzR hzbarR hznezbar
      (fun ρ hρ hρz hρsz => targetNeg_zero (hGne ρ hρ hρz) (hGneStar ρ hρ hρsz))
      (by show targetNeg w (G z) = Complex.I
          rw [show G z = w from rfl]; simp [targetNeg])
      (by rw [hG_star z, show G z = w from rfl]; simp [targetNeg, hwstar])]
    norm_num
  -- positive witness
  let Fp : ℂ[X] := ∑ j : Fin 7, Polynomial.C ((cp j : ℂ)) * Polynomial.X ^ (j : ℕ)
  have hFpval : ∀ ν : ℂ, Fp.eval ν = ∑ j : Fin 7, (cp j : ℂ) * ν ^ (j : ℕ) := by
    intro ν
    simp only [Fp, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
  have hFpN : ∀ ν ∈ N, Fp.eval ν = targetPos w ν := by
    intro ν hν
    rw [hFpval]
    exact hcp ν hν
  have hsumP : ∀ z : ℂ, (∑ k : Fin 6, (cp k.succ : ℂ) * (G z) ^ (k.val + 1))
      = Fp.eval (G z) - (cp 0 : ℂ) := by
    intro z
    rw [hFpval]
    conv_rhs => rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ]
    ring
  have hspread_pos : spread q ψ (fun k => cp k.succ) = 2 - 4 / 9 := by
    rw [spread_def]
    rw [show (q.map (algebraMap ℚ ℂ)).roots.toFinset = R from hRdef.symm]
    simp_rw [hinner_eq]
    rw [show (fun z => ∑ k : Fin 6, (cp k.succ : ℂ) * (G z) ^ (k.val + 1))
          = (fun z => Fp.eval (G z) - (cp 0 : ℂ)) from funext hsumP]
    change spreadCore R (fun z => Fp.eval (G z) + (-(cp 0 : ℂ))) = 2 - 4 / 9
    rw [spreadCore_add_const R hRcard (fun z => Fp.eval (G z)) (-(cp 0 : ℂ))]
    rw [spreadCore_congr (fun ρ hρ => hFpN (G ρ) (hG_mem_N ρ hρ))]
    rw [spreadCore_pair_pos hzR hzbarR hznezbar
      (fun ρ hρ hρz hρsz => targetPos_zero (hGne ρ hρ hρz) (hGneStar ρ hρ hρsz))
      (by show targetPos w (G z) = 1
          rw [show G z = w from rfl]; simp [targetPos])
      (by rw [hG_star z, show G z = w from rfl]; simp [targetPos, hwstar])]
  exact ⟨ψ, (fun k => cn k.succ), (fun k => cp k.succ), hspread_neg, by
    rw [hspread_pos]; norm_num⟩

end
end Pconstructible
