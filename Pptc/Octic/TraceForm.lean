/- Copyright (c) 2024 Lean Community. All rights reserved.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

This file is part of the Pptc (PowerPoint Constructibility) project.
-/

import Pptc.DegreeSeven
import Pptc.TotallyReal.YSpace

/-! # Pptc.Octic.TraceForm

The trace form of an octic, in the monomial basis.

For a monic separable `q : ℝ[X]` of degree `8` with companion matrix
`C = companionN (n := 8) q`, the trace form on the coefficient space `Fin 8 → ℝ` is
`v ↦ Tr ((aeval C (polyOfVec8 v)) ^ 2)`.  Its polar form is the bilinear form with matrix
`Hmat8 q`, whose entries are `Tr (C ^ (i + j))`.  Restricted to the trace-zero hyperplane
`{p1vec8 q · = 0}` — a `7`-dimensional space of coefficient vectors — the form has signature
`(7 - s, s)`, where `s` is the number of non-real conjugate pairs of `q`.  The trace of the
identity on `Fin 8 → ℝ` contributes the constant `8` (`svec8_zero`), which is the one number
that changes from the septic case.

This file ports the trace-form block of `Pptc.DegreeSeven` (the septic data `Hmat`, `svec`,
`p1vec`, `p3vec`, `bvec`, `coeff6`, `Lcomb`, `Gram`) to degree `8`, on top of the generic
companion matrix `companionN` of `Pptc.TotallyReal.YSpace`.  The foundation is
`companionN_trace_pow_aeval8`, which identifies the trace of a power of `aeval C φ` with the
power sum of `φ` over the complex roots of `q`; every other lemma here is algebra.  The
generic quadratic/bilinear form algebra (`qform`, `bilin`, `bilin_comm`, `qform_add`,
`qform_smul_add`, …) is *not* duplicated: it is already polymorphic in `n` in `DegreeSeven`.
-/

open Polynomial Matrix

namespace Pconstructible

noncomputable section

/-! ### The spectral identity -/

-- Theorem: the trace of the `k`-th power of `aeval (companionN q) φ`, mapped to `ℂ`, is the
-- sum of the `k`-th powers of `φ` evaluated at the complex roots of `q`.
theorem companionN_trace_pow_aeval8 (q φ : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 8)
    (hsep : q.Separable) (k : ℕ) :
    algebraMap ℝ ℂ (Matrix.trace ((aeval (companionN (n := 8) q) φ) ^ k))
      = ((q.map (algebraMap ℝ ℂ)).roots.map
          (fun z => ((φ.map (algebraMap ℝ ℂ)).eval z) ^ k)).sum := by
  have hmon' : (q.map (algebraMap ℝ ℂ)).Monic := hmon.map (algebraMap ℝ ℂ)
  have hnat' : (q.map (algebraMap ℝ ℂ)).natDegree = 8 := by
    rw [Polynomial.natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective]
    exact hnat
  have hsep' : (q.map (algebraMap ℝ ℂ)).Separable := hsep.map
  have hmap : ((aeval (companionN (n := 8) q) φ) ^ k).map (algebraMap ℝ ℂ)
      = (aeval (companionN' (n := 8) (q.map (algebraMap ℝ ℂ)))
          (φ.map (algebraMap ℝ ℂ))) ^ k := by
    rw [← RingHom.mapMatrix_apply (algebraMap ℝ ℂ) ((aeval (companionN (n := 8) q) φ) ^ k),
      map_pow, RingHom.mapMatrix_apply, companionN_aeval_map_eq]
  rw [AddMonoidHom.map_trace (algebraMap ℝ ℂ), hmap,
    companionN'_trace_pow 8 (q.map (algebraMap ℝ ℂ)) (φ.map (algebraMap ℝ ℂ))
      hmon' (by norm_num) hnat' hsep' k]

/-! ### E1: the Hermite matrix entries are P-constructible -/

-- Theorem: the trace of the `k`-th power of the companion matrix is P-constructible.
theorem trace_pow_companion8_Pconstructible (q : ℝ[X])
    (hq : ∀ k, PConstructible (q.coeff k)) (k : ℕ) :
    PConstructible (Matrix.trace ((companionN (n := 8) q) ^ k)) := by
  rw [Matrix.trace]
  exact Finset.sum_induction _ PConstructible (fun _ _ ha hb => PConstructible.add ha hb)
    zero_Pconstructible (fun i _ => matrix_pow_entries_Pconstructible
      (companionN_entries_Pconstructible 8 q hq) k i i)

/-! ### The Hermite form built from the companion matrix -/

/-- The Hermite (trace) form of `q`, in the monomial basis `1, X, …, X⁷`. -/
noncomputable def hermiteForm8 (q : ℝ[X]) (v : Fin 8 → ℝ) : ℝ :=
  ∑ i, ∑ j, v i * Matrix.trace ((companionN (n := 8) q) ^ (i.val + j.val)) * v j

/-- The polynomial whose coefficient vector is `v`. -/
noncomputable def polyOfVec8 (v : Fin 8 → ℝ) : ℝ[X] :=
  ∑ i : Fin 8, Polynomial.monomial i.val (v i)

-- Theorem: `aeval` of the coefficient vector is the corresponding matrix polynomial.
theorem aeval_polyOfVec8 (q : ℝ[X]) (v : Fin 8 → ℝ) :
    aeval (companionN (n := 8) q) (polyOfVec8 v)
      = ∑ i : Fin 8, v i • (companionN (n := 8) q) ^ i.val := by
  rw [polyOfVec8, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one]
  rw [Matrix.smul_mul, Matrix.one_mul]

-- Theorem: the square of that matrix polynomial expands into the Hermite basis.
theorem aeval_polyOfVec8_sq (q : ℝ[X]) (v : Fin 8 → ℝ) :
    (aeval (companionN (n := 8) q) (polyOfVec8 v)) ^ 2 =
      ∑ i : Fin 8, ∑ j : Fin 8,
        (v i * v j) • (companionN (n := 8) q) ^ (i.val + j.val) := by
  rw [aeval_polyOfVec8, pow_two, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_add]

-- Theorem: the Hermite form is the trace of the square of the matrix polynomial.
theorem trace_aeval_polyOfVec8_sq (q : ℝ[X]) (v : Fin 8 → ℝ) :
    Matrix.trace ((aeval (companionN (n := 8) q) (polyOfVec8 v)) ^ 2)
      = hermiteForm8 q v := by
  rw [aeval_polyOfVec8_sq, hermiteForm8, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Matrix.trace_smul, smul_eq_mul]
  ring

-- Theorem: conversely, the Hermite form equals that trace.
theorem hermiteForm8_eq_trace_sq (q : ℝ[X]) (v : Fin 8 → ℝ) :
    hermiteForm8 q v = Matrix.trace ((aeval (companionN (n := 8) q) (polyOfVec8 v)) ^ 2) :=
  (trace_aeval_polyOfVec8_sq q v).symm

/-! ### Trace form data

`Hmat8 q` is the Hermite/trace form of `q` in the monomial basis: `H i j = Tr (M ^ (i+j))`
with `M = companionN (n := 8) q`.  `p1vec8` is the associated linear functional
`v ↦ ∑ sᵢ vᵢ = Tr (aeval M (polyOfVec8 v))`, so that `{p1vec8 = 0}` is the trace-zero
hyperplane, and `p3vec8` is the cubic `v ↦ Tr ((aeval M (polyOfVec8 v)) ^ 3)`. -/

/-- The trace form of `q` in the monomial basis. -/
def Hmat8 (q : ℝ[X]) : Matrix (Fin 8) (Fin 8) ℝ :=
  fun i j => Matrix.trace ((companionN (n := 8) q) ^ (i.val + j.val))

/-- The first moment functional: `sᵢ = Tr (M ^ i)`. -/
def svec8 (q : ℝ[X]) : Fin 8 → ℝ :=
  fun i => Matrix.trace ((companionN (n := 8) q) ^ i.val)

/-- The linear functional `v ↦ ∑ sᵢ vᵢ = Tr (aeval M (polyOfVec8 v))`. -/
def p1vec8 (q : ℝ[X]) (v : Fin 8 → ℝ) : ℝ := ∑ i, svec8 q i * v i

/-- The cubic functional `v ↦ Tr ((aeval M (polyOfVec8 v)) ^ 3)`. -/
def p3vec8 (q : ℝ[X]) (v : Fin 8 → ℝ) : ℝ :=
  Matrix.trace ((aeval (companionN (n := 8) q) (polyOfVec8 v)) ^ 3)

-- Theorem: the entries of the Hermite matrix are P-constructible.
theorem Hmat8_Pconstructible (q : ℝ[X]) (hq : ∀ k, PConstructible (q.coeff k))
    (i j : Fin 8) : PConstructible (Hmat8 q i j) :=
  trace_pow_companion8_Pconstructible q hq (i.val + j.val)

-- Theorem: the Hermite matrix is symmetric.
theorem Hmat8_symm (q : ℝ[X]) : (Hmat8 q)ᵀ = Hmat8 q := by
  ext i j
  simp only [Matrix.transpose_apply, Hmat8]
  rw [Nat.add_comm]

-- Theorem: the moment vector has P-constructible entries.
theorem svec8_Pconstructible (q : ℝ[X]) (hq : ∀ k, PConstructible (q.coeff k))
    (i : Fin 8) : PConstructible (svec8 q i) :=
  trace_pow_companion8_Pconstructible q hq i.val

-- Theorem: the zeroth moment is the dimension `8` (the trace of the identity).
theorem svec8_zero (q : ℝ[X]) : svec8 q 0 = 8 := by
  change Matrix.trace ((companionN (n := 8) q) ^ 0) = 8
  rw [pow_zero, Matrix.trace_one]
  norm_num

-- Theorem: `p1vec8` is the trace of the matrix polynomial.
theorem p1vec8_eq_trace (q : ℝ[X]) (v : Fin 8 → ℝ) :
    p1vec8 q v = Matrix.trace (aeval (companionN (n := 8) q) (polyOfVec8 v)) := by
  rw [p1vec8, aeval_polyOfVec8, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.trace_smul, smul_eq_mul]
  simp only [svec8]
  ring

-- Theorem: the quadratic form of `Hmat8` is the Hermite form.
theorem qform_Hmat8_eq_hermiteForm8 (q : ℝ[X]) (v : Fin 8 → ℝ) :
    qform (Hmat8 q) v = hermiteForm8 q v := by
  simp only [qform, Hmat8, hermiteForm8, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-! ### A basis of the hyperplane `{p1 = 0}`

Since `s 0 = 8 ≠ 0`, the seven vectors `bⱼ = e_{j+1} - (s_{j+1}/8) e₀` (`j : Fin 7`) are a
P-constructible basis of `{p1vec8 = 0}`.  Every `v` with `p1vec8 q v = 0` is `Lcomb8 q (coeff7
v)` where `coeff7` reads off coordinates `1, …, 7`; this makes the restricted form computable
as a `7 × 7` Gram matrix with no kernel to avoid. -/

/-- The `k`-th standard basis vector of `Fin 8 → ℝ`. -/
def e8 (k : Fin 8) : Fin 8 → ℝ := Pi.single k 1

-- Theorem: the standard basis vector evaluates to `1` at its own index.
@[simp] theorem e8_apply_self (k : Fin 8) : e8 k k = 1 := Pi.single_eq_same k 1

-- Theorem: the standard basis vector evaluates to `0` elsewhere.
theorem e8_apply_ne {i k : Fin 8} (h : i ≠ k) : e8 k i = 0 := Pi.single_eq_of_ne h 1

/-- The basis vector `bⱼ = e_{j+1} - (s_{j+1}/8) e₀`, `j : Fin 7`. -/
def bvec8 (q : ℝ[X]) (j : Fin 7) : Fin 8 → ℝ :=
  e8 (Fin.succ j) - (svec8 q (Fin.succ j) / 8) • e8 (0 : Fin 8)

/-- Coordinates `1, …, 7` of a vector, i.e. those not involving `e₀`. -/
def coeff7 (v : Fin 8 → ℝ) : Fin 7 → ℝ := fun k => v (Fin.succ k)

/-- The combination `∑ j, x j • bⱼ`. -/
def Lcomb8 (q : ℝ[X]) (x : Fin 7 → ℝ) : Fin 8 → ℝ := ∑ j : Fin 7, x j • bvec8 q j

/-- The Gram matrix of the trace form in the basis `b`. -/
def Gram8 (q : ℝ[X]) : Matrix (Fin 7) (Fin 7) ℝ :=
  fun j k => bilin (Hmat8 q) (bvec8 q j) (bvec8 q k)

-- Theorem: the zeroth coordinate of a basis vector.
theorem bvec8_apply_zero (q : ℝ[X]) (j : Fin 7) :
    bvec8 q j 0 = -svec8 q (Fin.succ j) / 8 := by
  simp [bvec8, e8_apply_ne (Fin.succ_ne_zero j).symm]
  ring

-- Theorem: the remaining coordinates of a basis vector are the standard ones.
theorem bvec8_apply_succ (q : ℝ[X]) (j k : Fin 7) :
    bvec8 q j (Fin.succ k) = if k = j then 1 else 0 := by
  simp only [bvec8, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    e8_apply_ne (Fin.succ_ne_zero k), mul_zero, sub_zero]
  by_cases h : k = j
  · subst h
    rw [e8_apply_self, if_pos rfl]
  · rw [e8_apply_ne (fun hh => h (by simpa using hh)), if_neg h]

-- Theorem: the entries of a basis vector are P-constructible.
theorem bvec8_Pconstructible (q : ℝ[X]) (hq : ∀ k, PConstructible (q.coeff k))
    (j : Fin 7) (i : Fin 8) : PConstructible (bvec8 q j i) := by
  rw [bvec8]
  refine PConstructible.sub ?_ ?_
  · by_cases h : i = Fin.succ j
    · rw [h, e8_apply_self]; exact PConstructible.base_one
    · rw [e8_apply_ne h]; exact zero_Pconstructible
  · refine PConstructible.mul ?_ ?_
    · exact PConstructible.div (svec8_Pconstructible q hq (Fin.succ j)) (by pconstructible)
    · by_cases h : i = (0 : Fin 8)
      · rw [h, e8_apply_self]; exact PConstructible.base_one
      · rw [e8_apply_ne h]; exact zero_Pconstructible

-- Theorem: every basis vector of the hyperplane lies in the hyperplane `{p1 = 0}`.
theorem p1vec8_bvec8 (q : ℝ[X]) (j : Fin 7) : p1vec8 q (bvec8 q j) = 0 := by
  rw [p1vec8, Fin.sum_univ_succ]
  simp only [bvec8_apply_zero, bvec8_apply_succ, svec8_zero]
  rw [Finset.sum_eq_single j]
  · simp only [↓reduceIte, mul_one]
    ring
  · intro k _ hk
    rw [if_neg hk]
    simp
  · intro hj; exact absurd (Finset.mem_univ j) hj

-- Theorem: every combination of basis vectors lies in the hyperplane `{p1 = 0}`.
theorem p1vec8_Lcomb8 (q : ℝ[X]) (x : Fin 7 → ℝ) : p1vec8 q (Lcomb8 q x) = 0 := by
  rw [Lcomb8, p1vec8]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  have : (∑ i, svec8 q i * (x j * bvec8 q j i)) = x j * p1vec8 q (bvec8 q j) := by
    rw [p1vec8, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  rw [this, p1vec8_bvec8, mul_zero]

-- Theorem: a vector in the hyperplane `{p1 = 0}` is the combination of basis vectors given
-- by its last seven coordinates.
theorem Lcomb8_coeff7 (q : ℝ[X]) {v : Fin 8 → ℝ} (hv : p1vec8 q v = 0) :
    Lcomb8 q (coeff7 v) = v := by
  have hsum : (∑ j : Fin 7, v (Fin.succ j) * svec8 q (Fin.succ j)) = -8 * v 0 := by
    have h := hv
    rw [p1vec8, Fin.sum_univ_succ, svec8_zero] at h
    have h2 : (∑ j : Fin 7, svec8 q (Fin.succ j) * v (Fin.succ j)) = -8 * v 0 := by
      linarith
    rw [← h2]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  funext i
  refine Fin.cases ?_ ?_ i
  · rw [Lcomb8, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, bvec8_apply_zero, coeff7]
    have : (∑ j : Fin 7, v (Fin.succ j) * (-svec8 q (Fin.succ j) / 8))
        = -(1 / 8) * ∑ j : Fin 7, v (Fin.succ j) * svec8 q (Fin.succ j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    rw [this, hsum]
    ring
  · intro i
    rw [Lcomb8, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, bvec8_apply_succ, coeff7]
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hk
      rw [if_neg (Ne.symm hk)]
      ring
    · intro hi; exact absurd (Finset.mem_univ i) hi

-- Theorem: the map `x ↦ Lcomb8 q x` is injective.
theorem Lcomb8_injective (q : ℝ[X]) {x : Fin 7 → ℝ} (h : Lcomb8 q x = 0) : x = 0 := by
  funext k
  have hk := congrFun h (Fin.succ k)
  rw [Lcomb8, Finset.sum_apply] at hk
  simp only [Pi.smul_apply, smul_eq_mul, bvec8_apply_succ, Pi.zero_apply] at hk
  rw [Finset.sum_eq_single k] at hk
  · simpa using hk
  · intro j _ hj
    rw [if_neg (Ne.symm hj), mul_zero]
  · intro hk'; exact absurd (Finset.mem_univ k) hk'

-- Theorem: the bilinear form of `Hmat8` on two combinations of basis vectors is the
-- bilinear form of `Gram8` on the coordinates.
theorem bilin_Gram8_Lcomb8 (q : ℝ[X]) (x y : Fin 7 → ℝ) :
    bilin (Hmat8 q) (Lcomb8 q x) (Lcomb8 q y)
      = ∑ j, ∑ k, x j * y k * bilin (Hmat8 q) (bvec8 q j) (bvec8 q k) := by
  rw [Lcomb8, bilin_sum_left]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Lcomb8, bilin_sum_right]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [bilin_smul_left, bilin_smul_right]
  ring

-- Theorem: the quadratic form of `Hmat8` on a combination of basis vectors is the
-- quadratic form of `Gram8` on the coordinates.
theorem qform_Gram8_Lcomb8 (q : ℝ[X]) (x : Fin 7 → ℝ) :
    qform (Hmat8 q) (Lcomb8 q x) = qform (Gram8 q) x := by
  rw [qform_eq_bilin (Hmat8 q) (Lcomb8 q x), bilin_Gram8_Lcomb8, qform_eq_sum]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
  simp only [Gram8]
  ring

-- Theorem: the restricted form is the trace of the square of the matrix polynomial.
theorem qform_Gram8_eq_trace_sq (q : ℝ[X]) (x : Fin 7 → ℝ) :
    qform (Gram8 q) x =
      Matrix.trace ((aeval (companionN (n := 8) q) (polyOfVec8 (Lcomb8 q x))) ^ 2) := by
  rw [← qform_Gram8_Lcomb8, qform_Hmat8_eq_hermiteForm8, hermiteForm8_eq_trace_sq]

-- Theorem: the entries of the Gram matrix are P-constructible.
theorem Gram8_Pconstructible (q : ℝ[X]) (hq : ∀ k, PConstructible (q.coeff k))
    (j k : Fin 7) : PConstructible (Gram8 q j k) :=
  bilin_Pconstructible (Hmat8_Pconstructible q hq) (bvec8_Pconstructible q hq j)
    (bvec8_Pconstructible q hq k)

-- Theorem: the Gram matrix is symmetric.
theorem Gram8_symm (q : ℝ[X]) : (Gram8 q)ᵀ = Gram8 q := by
  ext j k
  simp only [Matrix.transpose_apply, Gram8]
  rw [bilin_comm (Hmat8_symm q)]

/-! ### From polynomials to coefficient vectors

`vecOf8 f = (f.coeff 0, …, f.coeff 7)` reads off the coefficients of a degree-`≤ 7`
polynomial.  It makes `p1vec8`, `qform Hmat8` and `p3vec8` computable in terms of
`trace`/`hermiteForm8`, which is what turns the abstract sign results into explicit
directions for the Gram matrix. -/

/-- The coefficient vector `(f.coeff 0, …, f.coeff 7)` of a polynomial. -/
def vecOf8 (f : ℝ[X]) : Fin 8 → ℝ := fun i => f.coeff i.val

-- Theorem: reading off the coefficients of a degree-`≤ 7` polynomial and rebuilding it is
-- the identity.
theorem polyOfVec8_vecOf8 {f : ℝ[X]} (hf : f.natDegree ≤ 7) : polyOfVec8 (vecOf8 f) = f := by
  rw [polyOfVec8]
  simp only [vecOf8]
  rw [Fin.sum_univ_eq_sum_range (fun k => Polynomial.monomial k (f.coeff k)) 8]
  exact (Polynomial.as_sum_range' f 8 (by omega)).symm

-- Theorem: `polyOfVec8` is compatible with linear combinations of polynomials.
theorem polyOfVec8_smul_add {a b : ℝ} {f g : ℝ[X]} (hf : f.natDegree ≤ 7)
    (hg : g.natDegree ≤ 7) :
    polyOfVec8 (a • vecOf8 f + b • vecOf8 g) = C a * f + C b * g := by
  have h1 : a • vecOf8 f + b • vecOf8 g = vecOf8 (C a * f + C b * g) := by
    ext i
    simp only [vecOf8, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Polynomial.coeff_add,
      Polynomial.coeff_C_mul]
  rw [h1, polyOfVec8_vecOf8]
  refine le_trans (Polynomial.natDegree_add_le _ _) ?_
  exact max_le (le_trans (Polynomial.natDegree_C_mul_le a f) hf)
    (le_trans (Polynomial.natDegree_C_mul_le b g) hg)

-- Theorem: `p1vec8` of the coefficient vector is the trace of the polynomial.
theorem p1vec8_vecOf8 (q : ℝ[X]) (f : ℝ[X]) (hf : f.natDegree ≤ 7) :
    p1vec8 q (vecOf8 f) = Matrix.trace (aeval (companionN (n := 8) q) f) := by
  rw [p1vec8_eq_trace, polyOfVec8_vecOf8 hf]

-- Theorem: `aeval` of `C a * f + C b * g` is the corresponding matrix combination.
theorem aeval_C_mul_smul8 (q : ℝ[X]) (a b : ℝ) (f g : ℝ[X]) :
    aeval (companionN (n := 8) q) (C a * f + C b * g)
      = a • aeval (companionN (n := 8) q) f + b • aeval (companionN (n := 8) q) g := by
  rw [map_add, map_mul, map_mul]
  simp only [Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul,
    Matrix.one_mul]

-- Theorem: `qform Hmat8` on a combination of coefficient vectors is the trace of the square
-- of the corresponding combination of matrix polynomials.
theorem qform_Hmat8_smul_add_vecOf8 (q : ℝ[X]) (a b : ℝ) (f g : ℝ[X])
    (hf : f.natDegree ≤ 7) (hg : g.natDegree ≤ 7) :
    qform (Hmat8 q) (a • vecOf8 f + b • vecOf8 g) =
      Matrix.trace ((aeval (companionN (n := 8) q) (C a * f + C b * g)) ^ 2) := by
  rw [qform_Hmat8_eq_hermiteForm8, hermiteForm8_eq_trace_sq, polyOfVec8_smul_add hf hg]

-- Theorem: scalar multiplication of matrix products.
theorem smul_mul_smul8 (a b : ℝ) (A B : Matrix (Fin 8) (Fin 8) ℝ) :
    (a • A) * (b • B) = (a * b) • (A * B) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]

-- Theorem: expansion of the trace of the square of a two-term combination.
theorem trace_sq_smul_add8 (A B : Matrix (Fin 8) (Fin 8) ℝ) (a b : ℝ) :
    Matrix.trace ((a • A + b • B) ^ 2) =
      a ^ 2 * Matrix.trace (A ^ 2) + 2 * a * b * Matrix.trace (A * B)
        + b ^ 2 * Matrix.trace (B ^ 2) := by
  rw [sq, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
  simp only [smul_mul_smul8, Matrix.trace_add, Matrix.trace_smul]
  rw [Matrix.trace_mul_comm B A]
  simp only [pow_two, smul_eq_mul]
  ring

-- Theorem: `Lcomb8` is compatible with linear combinations of coordinates.
theorem Lcomb8_smul_add (q : ℝ[X]) (a b : ℝ) (x y : Fin 7 → ℝ) :
    Lcomb8 q (a • x + b • y) = a • Lcomb8 q x + b • Lcomb8 q y := by
  rw [Lcomb8, Lcomb8, Lcomb8, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, add_smul]
  module

-- Theorem: `aeval` of `f - C c` is `aeval f` minus `c` times the identity.
theorem aeval_sub_C8 (q : ℝ[X]) (c : ℝ) (f : ℝ[X]) :
    aeval (companionN (n := 8) q) (f - C c)
      = aeval (companionN (n := 8) q) f - c • (1 : Matrix (Fin 8) (Fin 8) ℝ) := by
  rw [map_sub, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]

-- Theorem: expansion of the trace of the square of `A - c • 1`.
theorem trace_sq_sub_scalar8 (A : Matrix (Fin 8) (Fin 8) ℝ) (c : ℝ) :
    Matrix.trace ((A - c • 1) ^ 2) =
      Matrix.trace (A ^ 2) - 2 * c * Matrix.trace A + c ^ 2 * 8 := by
  have h : A - c • 1 = (1 : ℝ) • A + (-c) • (1 : Matrix (Fin 8) (Fin 8) ℝ) := by
    rw [one_smul, neg_smul, sub_eq_add_neg]
  rw [h, trace_sq_smul_add8, Matrix.mul_one]
  simp only [pow_two, one_mul, mul_one, Matrix.trace_one]
  norm_num
  ring

-- Theorem: `aeval` of a combination of shifted polynomials.
theorem aeval_sub_C_smul_add8 (q : ℝ[X]) (a b c : ℝ) (f g : ℝ[X]) :
    aeval (companionN (n := 8) q) (C a * (f - C c) + C b * (g - C c))
      = a • aeval (companionN (n := 8) q) f + b • aeval (companionN (n := 8) q) g
        - ((a + b) * c) • 1 := by
  rw [aeval_C_mul_smul8, aeval_sub_C8, aeval_sub_C8]
  module

/-! ### The cube expansion -/

-- Theorem: expansion of `(X + Y) ^ 3` for non-commuting matrices.
theorem cube_add8 (X Y : Matrix (Fin 8) (Fin 8) ℝ) :
    (X + Y) ^ 3 = X ^ 3 + X ^ 2 * Y + X * Y * X + Y * X ^ 2 + X * Y ^ 2
      + Y * X * Y + Y ^ 2 * X + Y ^ 3 := by
  noncomm_ring

-- Theorem: `(c • M) ^ n = (c ^ n) • M ^ n`.
theorem smul_pow8 (c : ℝ) (M : Matrix (Fin 8) (Fin 8) ℝ) (n : ℕ) :
    (c • M) ^ n = (c ^ n) • M ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, smul_mul_smul8, ← pow_succ, ← pow_succ]

-- Theorem: expansion of `(a • A + b • B) ^ 3`.
theorem cube_smul_add8 (A B : Matrix (Fin 8) (Fin 8) ℝ) (a b : ℝ) :
    (a • A + b • B) ^ 3 =
      (a * a * a) • (A * A * A) + (a * a * b) • (A * A * B) + (a * a * b) • (A * B * A)
        + (a * b * b) • (A * B * B) + (a * a * b) • (B * A * A)
        + (a * b * b) • (B * A * B) + (a * b * b) • (B * B * A)
        + (b * b * b) • (B * B * B) := by
  rw [show (a • A + b • B) ^ 3 = _ from cube_add8 (a • A) (b • B)]
  simp only [smul_mul_smul8, pow_succ, pow_zero, Matrix.one_mul, mul_assoc, mul_comm,
    mul_left_comm]
  abel

-- Theorem: expansion of the trace of the cube of a two-term combination.
theorem trace_cube_smul_add8 (A B : Matrix (Fin 8) (Fin 8) ℝ) (a b : ℝ) :
    Matrix.trace ((a • A + b • B) ^ 3) = a ^ 3 * Matrix.trace (A ^ 3)
      + 3 * a ^ 2 * b * Matrix.trace (A ^ 2 * B) + 3 * a * b ^ 2 * Matrix.trace (A * B ^ 2)
      + b ^ 3 * Matrix.trace (B ^ 3) := by
  rw [cube_smul_add8, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add,
    Matrix.trace_add, Matrix.trace_add, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.trace_smul, Matrix.trace_smul]
  rw [show Matrix.trace (A * A * A) = Matrix.trace (A ^ 3) by rw [← pow_two, ← pow_succ],
    show Matrix.trace (A * A * B) = Matrix.trace (A ^ 2 * B) by rw [← pow_two],
    show Matrix.trace (A * B * A) = Matrix.trace (A ^ 2 * B) by
      rw [Matrix.trace_mul_comm (A * B) A, ← Matrix.mul_assoc, ← pow_two],
    show Matrix.trace (A * B * B) = Matrix.trace (A * B ^ 2) by rw [Matrix.mul_assoc, ← pow_two],
    show Matrix.trace (B * A * A) = Matrix.trace (A ^ 2 * B) by
      rw [Matrix.mul_assoc, Matrix.trace_mul_comm B (A * A), ← pow_two],
    show Matrix.trace (B * A * B) = Matrix.trace (A * B ^ 2) by
      rw [Matrix.mul_assoc, Matrix.trace_mul_comm B (A * B), Matrix.mul_assoc, ← pow_two],
    show Matrix.trace (B * B * A) = Matrix.trace (A * B ^ 2) by
      rw [Matrix.trace_mul_comm (B * B) A, ← pow_two],
    show Matrix.trace (B * B * B) = Matrix.trace (B ^ 3) by rw [← pow_two, ← pow_succ]]
  simp only [smul_eq_mul]
  ring

/-! ### Remaining transport helpers -/

-- Theorem: `Lcomb8` is homogeneous.
theorem Lcomb8_smul (q : ℝ[X]) (c : ℝ) (x : Fin 7 → ℝ) :
    Lcomb8 q (c • x) = c • Lcomb8 q x := by
  rw [Lcomb8, Lcomb8, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Pi.smul_apply, smul_eq_mul, smul_smul]

-- Theorem: `Lcomb8` is additive in the coordinates.
theorem Lcomb8_sub (q : ℝ[X]) (x y : Fin 7 → ℝ) :
    Lcomb8 q (x - y) = Lcomb8 q x - Lcomb8 q y := by
  rw [Lcomb8, Lcomb8, Lcomb8, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Pi.sub_apply, sub_smul]

-- Theorem: the entries of `Lcomb8` are P-constructible.
theorem Lcomb8_Pconstructible (q : ℝ[X]) (hq : ∀ k, PConstructible (q.coeff k))
    {x : Fin 7 → ℝ} (hx : ∀ j, PConstructible (x j)) :
    ∀ i, PConstructible (Lcomb8 q x i) := by
  intro i
  rw [Lcomb8, Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_Pconstructible Finset.univ (fun j => x j * bvec8 q j i)
    (fun j _ => PConstructible.mul (hx j) (bvec8_Pconstructible q hq j i))

-- Theorem: the bilinear form as a double sum.
theorem bilin_eq_sum8 (A : Matrix (Fin 8) (Fin 8) ℝ) (x y : Fin 8 → ℝ) :
    bilin A x y = ∑ j, ∑ k, x j * A j k * y k := by
  simp only [bilin, dotProduct, Matrix.mulVec_apply, Matrix.row]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

-- Theorem: the bilinear form of `Hmat8` on two combinations of basis vectors is the
-- bilinear form of `Gram8`.
theorem bilin_Hmat8_Lcomb8 (q : ℝ[X]) (x y : Fin 7 → ℝ) :
    bilin (Hmat8 q) (Lcomb8 q x) (Lcomb8 q y) = bilin (Gram8 q) x y := by
  rw [bilin_Gram8_Lcomb8, bilin_eq_sum (Gram8 q) x y]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
  simp only [Gram8]
  ring

-- Theorem: the trace of any power of a matrix with P-constructible entries is
-- P-constructible.
theorem trace_pow_Pconstructible8 {M : Matrix (Fin 8) (Fin 8) ℝ}
    (hM : ∀ i j, PConstructible (M i j)) (k : ℕ) :
    PConstructible (Matrix.trace (M ^ k)) := by
  rw [Matrix.trace]
  exact Finset.sum_Pconstructible Finset.univ (fun i => (M ^ k) i i)
    (fun i _ => matrix_pow_entries_Pconstructible hM k i i)

-- Theorem: the trace of a product of two matrices with P-constructible entries is
-- P-constructible.
theorem trace_mul_Pconstructible8 {A B : Matrix (Fin 8) (Fin 8) ℝ}
    (hA : ∀ i j, PConstructible (A i j)) (hB : ∀ i j, PConstructible (B i j)) :
    PConstructible (Matrix.trace (A * B)) := by
  rw [Matrix.trace]
  exact Finset.sum_Pconstructible Finset.univ (fun i => (A * B) i i)
    (fun i _ => matrix_mul_entries_Pconstructible hA hB i i)

-- Theorem: the coefficients of `polyOfVec8` of a P-constructible vector are
-- P-constructible.
theorem polyOfVec8_coeff_Pconstructible (v : Fin 8 → ℝ) (hv : ∀ i, PConstructible (v i))
    (k : ℕ) : PConstructible ((polyOfVec8 v).coeff k) := by
  rw [polyOfVec8, Polynomial.finsetSum_coeff]
  refine Finset.sum_Pconstructible Finset.univ
    (fun i => (Polynomial.monomial i.val (v i)).coeff k) (fun i _ => ?_)
  rw [Polynomial.coeff_monomial]
  split_ifs with h
  · exact hv i
  · exact zero_Pconstructible

-- Theorem: `polyOfVec8` has degree at most `7`.
theorem polyOfVec8_natDegree_le (v : Fin 8 → ℝ) : (polyOfVec8 v).natDegree ≤ 7 := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (fun k hk => ?_)
  rw [polyOfVec8, Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [Polynomial.coeff_monomial]
  split_ifs with h
  · exact absurd h (by omega)
  · rfl

-- Theorem: a nonzero coefficient vector gives a nonzero polynomial.
theorem polyOfVec8_ne_zero {v : Fin 8 → ℝ} (hv : v ≠ 0) : polyOfVec8 v ≠ 0 := by
  intro h
  apply hv
  funext i
  have hc : (polyOfVec8 v).coeff i.val = 0 := by rw [h, Polynomial.coeff_zero]
  rw [polyOfVec8, Polynomial.finsetSum_coeff] at hc
  rw [Finset.sum_eq_single i] at hc
  · simpa [Polynomial.coeff_monomial] using hc
  · intro j _ hji
    rw [Polynomial.coeff_monomial]
    split_ifs with h'
    · exact absurd (Fin.ext h') hji
    · rfl
  · intro hi; exact absurd (Finset.mem_univ i) hi

-- Theorem: `aeval` of `polyOfVec8` is additive and homogeneous.
theorem aeval_polyOfVec8_smul_add (q : ℝ[X]) (s t : ℝ) (x y : Fin 8 → ℝ) :
    aeval (companionN (n := 8) q) (polyOfVec8 (s • x + t • y))
      = s • aeval (companionN (n := 8) q) (polyOfVec8 x)
        + t • aeval (companionN (n := 8) q) (polyOfVec8 y) := by
  rw [aeval_polyOfVec8, aeval_polyOfVec8, aeval_polyOfVec8, Finset.smul_sum, Finset.smul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, add_smul, smul_smul,
    smul_smul]

-- Theorem: `p1vec8` is additive and homogeneous.
theorem p1vec8_smul_add (q : ℝ[X]) (s t : ℝ) (x y : Fin 8 → ℝ) :
    p1vec8 q (s • x + t • y) = s * p1vec8 q x + t * p1vec8 q y := by
  rw [p1vec8_eq_trace, aeval_polyOfVec8_smul_add, Matrix.trace_add, Matrix.trace_smul,
    Matrix.trace_smul, p1vec8_eq_trace q x, p1vec8_eq_trace q y]
  simp only [smul_eq_mul]

/-! ### B. The triple-sum formula and continuity of the cubic

`p3vec8 q w = Tr ((aeval M (polyOfVec8 w)) ^ 3)` expands, in the monomial basis, into the
triple sum `∑ i j k, wᵢ wⱼ wₖ Tr (M ^ (i + j + k))`.  This makes `p3vec8` a polynomial
function of `w`, hence continuous, and is the bridge that turns the parametrised cone into a
sextic in the line parameter. -/

-- Theorem: `p3vec8` is the triple sum of `wᵢ wⱼ wₖ Tr (M ^ (i + j + k))`.
theorem p3vec8_eq_sum (q : ℝ[X]) (w : Fin 8 → ℝ) :
    p3vec8 q w = ∑ i, ∑ j, ∑ k,
      w i * w j * w k
        * Matrix.trace ((companionN (n := 8) q) ^ (i.val + j.val + k.val)) := by
  have hcube : (aeval (companionN (n := 8) q) (polyOfVec8 w)) ^ 3 =
      ∑ i, ∑ j, ∑ k, (w i * w j * w k) •
        (companionN (n := 8) q) ^ (i.val + j.val + k.val) := by
    rw [pow_succ, aeval_polyOfVec8_sq, aeval_polyOfVec8]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_add]
  rw [p3vec8, hcube, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Matrix.trace_smul, smul_eq_mul]

-- Theorem: `p3vec8` is continuous in its vector argument.
theorem continuous_p3vec8 (q : ℝ[X]) : Continuous (p3vec8 q) := by
  rw [show p3vec8 q = fun w : Fin 8 → ℝ => ∑ i, ∑ j, ∑ k,
      w i * w j * w k
        * Matrix.trace ((companionN (n := 8) q) ^ (i.val + j.val + k.val)) from
    funext (p3vec8_eq_sum q)]
  fun_prop

-- Theorem: `p3vec8` is homogeneous of degree three.
theorem p3vec8_smul (q : ℝ[X]) (c : ℝ) (x : Fin 8 → ℝ) :
    p3vec8 q (c • x) = c ^ 3 * p3vec8 q x := by
  rw [p3vec8, p3vec8]
  have h : aeval (companionN (n := 8) q) (polyOfVec8 (c • x))
      = c • aeval (companionN (n := 8) q) (polyOfVec8 x) := by
    have := aeval_polyOfVec8_smul_add q c 0 x 0
    simpa using this
  rw [h, smul_pow8, Matrix.trace_smul, smul_eq_mul]

end

end Pconstructible
