import Pptc.ScratchH
import Pptc.ScratchK
import Pptc.ScratchE
import Pptc.ScratchC
import Pptc.ScratchC2
import Pptc.ScratchAB

open Polynomial Matrix

namespace Pconstructible

noncomputable section

/-! ### Trace form data

`Hmat q` is the Hermite/trace form of `q` in the monomial basis: `H i j = trace (M ^ (i+j))`
with `M = companion7 q`.  `p1vec` is the associated linear functional `v ↦ ∑ sᵢ vᵢ =
trace (aeval M (polyOfVec v))`, so that `{p1vec = 0}` is the trace-zero hyperplane, and `p3vec`
is the cubic `v ↦ trace ((aeval M (polyOfVec v)) ^ 3)`.  The plan is to find a
P-constructible `v` on which all three of `p1vec`, `qform Hmat` (= `p2`) and `p3vec` vanish. -/

/-- The trace form of `q` in the monomial basis. -/
def Hmat (q : ℝ[X]) : Matrix (Fin 7) (Fin 7) ℝ :=
  fun i j => Matrix.trace ((companion7 q) ^ (i.val + j.val))

/-- The first moment functional: `sᵢ = trace (M ^ i)`. -/
def svec (q : ℝ[X]) : Fin 7 → ℝ := fun i => Matrix.trace ((companion7 q) ^ i.val)

/-- The linear functional `v ↦ ∑ sᵢ vᵢ = trace (aeval M (polyOfVec v))`. -/
def p1vec (q : ℝ[X]) (v : Fin 7 → ℝ) : ℝ := ∑ i, svec q i * v i

/-- The cubic functional `v ↦ trace ((aeval M (polyOfVec v)) ^ 3)`. -/
def p3vec (q : ℝ[X]) (v : Fin 7 → ℝ) : ℝ :=
  Matrix.trace ((aeval (companion7 q) (polyOfVec v)) ^ 3)

theorem Hmat_Pconstructible (q : ℝ[X]) (hq : ∀ k, PConstructible (q.coeff k))
    (i j : Fin 7) : PConstructible (Hmat q i j) :=
  traceH_Pconstructible q hq i j

theorem Hmat_symm (q : ℝ[X]) : (Hmat q)ᵀ = Hmat q := by
  ext i j
  simp only [Matrix.transpose_apply, Hmat]
  rw [Nat.add_comm]

theorem svec_Pconstructible (q : ℝ[X]) (hq : ∀ k, PConstructible (q.coeff k))
    (i : Fin 7) : PConstructible (svec q i) :=
  trace_pow_companion7_Pconstructible q hq i.val

theorem svec_zero (q : ℝ[X]) : svec q 0 = 7 := by
  show Matrix.trace ((companion7 q) ^ 0) = 7
  rw [pow_zero, Matrix.trace_one]
  norm_num

theorem p1vec_eq_trace (q : ℝ[X]) (v : Fin 7 → ℝ) :
    p1vec q v = Matrix.trace (aeval (companion7 q) (polyOfVec v)) := by
  rw [p1vec, aeval_polyOfVec, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.trace_smul, smul_eq_mul]
  simp only [svec]
  ring

theorem qform_Hmat_eq_hermiteForm (q : ℝ[X]) (v : Fin 7 → ℝ) :
    qform (Hmat q) v = hermiteForm q v := by
  simp only [qform, Hmat, hermiteForm, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-! ### Basic bilinearity of `bilin` -/

theorem bilin_comm {A : Matrix (Fin n) (Fin n) ℝ} (hA : Aᵀ = A) (x y : Fin n → ℝ) :
    bilin A x y = bilin A y x := by
  simp only [bilin, dotProduct, Matrix.mulVec_apply, Matrix.row, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  have hji : A j i = A i j := by
    have h := congrFun (congrFun hA i) j
    simpa [Matrix.transpose_apply] using h
  rw [hji]
  ring

theorem bilin_add_left (A : Matrix (Fin n) (Fin n) ℝ) (x₁ x₂ y : Fin n → ℝ) :
    bilin A (x₁ + x₂) y = bilin A x₁ y + bilin A x₂ y := by
  unfold bilin dotProduct
  simp only [Matrix.mulVec_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem bilin_add_right (A : Matrix (Fin n) (Fin n) ℝ) (x y₁ y₂ : Fin n → ℝ) :
    bilin A x (y₁ + y₂) = bilin A x y₁ + bilin A x y₂ := by
  unfold bilin dotProduct
  simp only [Matrix.mulVec_apply, dotProduct_add, mul_add, Finset.sum_add_distrib]

theorem bilin_smul_left (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (x y : Fin n → ℝ) :
    bilin A (c • x) y = c * bilin A x y := by
  unfold bilin dotProduct
  simp only [Matrix.mulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

theorem bilin_smul_right (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (x y : Fin n → ℝ) :
    bilin A x (c • y) = c * bilin A x y := by
  unfold bilin dotProduct
  simp only [Matrix.mulVec_apply, smul_eq_mul, dotProduct_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

theorem qform_eq_bilin (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    qform A x = bilin A x x := rfl

theorem qform_add (A : Matrix (Fin n) (Fin n) ℝ) (hA : Aᵀ = A) (x y : Fin n → ℝ) :
    qform A (x + y) = qform A x + 2 * bilin A x y + qform A y := by
  rw [qform_eq_bilin, qform_eq_bilin A x, qform_eq_bilin A y,
    bilin_add_left, bilin_add_right, bilin_add_right, bilin_comm hA y x]
  ring

theorem qform_eq_sum (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    qform A x = ∑ j, ∑ k, x j * A j k * x k := by
  simp only [qform, dotProduct, Matrix.mulVec_apply, Matrix.row]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

theorem bilin_sum_left {A : Matrix (Fin n) (Fin n) ℝ} {ι : Type*} [Fintype ι]
    (f : ι → Fin n → ℝ) (y : Fin n → ℝ) :
    bilin A (∑ i, f i) y = ∑ i, bilin A (f i) y := by
  simp only [bilin, dotProduct, Finset.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem bilin_sum_right {A : Matrix (Fin n) (Fin n) ℝ} {ι : Type*} [Fintype ι]
    (x : Fin n → ℝ) (f : ι → Fin n → ℝ) :
    bilin A x (∑ i, f i) = ∑ i, bilin A x (f i) := by
  rw [bilin, Matrix.mulVec_sum, dotProduct_sum]
  rfl

theorem bilin_Pconstructible {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, PConstructible (A i j)) {u v : Fin n → ℝ}
    (hu : ∀ i, PConstructible (u i)) (hv : ∀ i, PConstructible (v i)) :
    PConstructible (bilin A u v) := by
  simp only [bilin, dotProduct, Matrix.mulVec_apply, Matrix.row]
  refine Finset.sum_Pconstructible Finset.univ (fun i => u i * ∑ j, A i j * v j)
    (fun i _ => ?_)
  refine PConstructible.mul (hu i) ?_
  exact Finset.sum_Pconstructible Finset.univ (fun j => A i j * v j)
    (fun j _ => PConstructible.mul (hA i j) (hv j))

/-! ### A basis of the hyperplane `{p1 = 0}`

Since `s 0 = 7 ≠ 0`, the six vectors `bⱼ = e_{j+1} - (s_{j+1}/7) e₀` (`j : Fin 6`) are a
P-constructible basis of `{p1vec = 0}`.  Every `v` with `p1vec q v = 0` is `Lcomb q (coeff6 v)`
where `coeff6` reads off coordinates `1, …, 6`; this makes the restricted form computable as a
`6 × 6` Gram matrix with no kernel to avoid. -/

/-- The basis vector `bⱼ = e_{j+1} - (s_{j+1}/7) e₀`, `j : Fin 6`. -/
def bvec (q : ℝ[X]) (j : Fin 6) : Fin 7 → ℝ :=
  e7 (Fin.succ j) - (svec q (Fin.succ j) / 7) • e7 (0 : Fin 7)

/-- Coordinates `1, …, 6` of a vector, i.e. those not involving `e₀`. -/
def coeff6 (v : Fin 7 → ℝ) : Fin 6 → ℝ := fun k => v (Fin.succ k)

/-- The combination `∑ j, x j • bⱼ`. -/
def Lcomb (q : ℝ[X]) (x : Fin 6 → ℝ) : Fin 7 → ℝ := ∑ j : Fin 6, x j • bvec q j

/-- The Gram matrix of the trace form in the basis `b`. -/
def Gram (q : ℝ[X]) : Matrix (Fin 6) (Fin 6) ℝ :=
  fun j k => bilin (Hmat q) (bvec q j) (bvec q k)

theorem bvec_apply_zero (q : ℝ[X]) (j : Fin 6) :
    bvec q j 0 = -svec q (Fin.succ j) / 7 := by
  simp [bvec, e7_apply_ne (Fin.succ_ne_zero j).symm]
  ring

theorem bvec_apply_succ (q : ℝ[X]) (j k : Fin 6) :
    bvec q j (Fin.succ k) = if k = j then 1 else 0 := by
  simp only [bvec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    e7_apply_ne (Fin.succ_ne_zero k), mul_zero, sub_zero]
  by_cases h : k = j
  · subst h
    rw [e7_apply_self, if_pos rfl]
  · rw [e7_apply_ne (fun hh => h (by simpa using hh)), if_neg h]

theorem bvec_Pconstructible (q : ℝ[X]) (hq : ∀ k, PConstructible (q.coeff k))
    (j : Fin 6) (i : Fin 7) : PConstructible (bvec q j i) := by
  rw [bvec]
  refine PConstructible.sub ?_ ?_
  · by_cases h : i = Fin.succ j
    · rw [h, e7_apply_self]; exact PConstructible.base_one
    · rw [e7_apply_ne h]; exact zero_Pconstructible
  · refine PConstructible.mul ?_ ?_
    · exact PConstructible.div (svec_Pconstructible q hq (Fin.succ j)) (by pconstructible)
    · by_cases h : i = (0 : Fin 7)
      · rw [h, e7_apply_self]; exact PConstructible.base_one
      · rw [e7_apply_ne h]; exact zero_Pconstructible

theorem coeff6_Pconstructible {v : Fin 7 → ℝ} (hv : ∀ i, PConstructible (v i))
    (k : Fin 6) : PConstructible (coeff6 v k) := hv (Fin.succ k)

theorem p1vec_bvec (q : ℝ[X]) (j : Fin 6) : p1vec q (bvec q j) = 0 := by
  rw [p1vec, Fin.sum_univ_succ]
  simp only [bvec_apply_zero, bvec_apply_succ, svec_zero]
  rw [Finset.sum_eq_single j]
  · simp only [↓reduceIte, mul_one]
    ring
  · intro k _ hk
    rw [if_neg hk]
    simp
  · intro hj; exact absurd (Finset.mem_univ j) hj

theorem p1vec_Lcomb (q : ℝ[X]) (x : Fin 6 → ℝ) : p1vec q (Lcomb q x) = 0 := by
  rw [Lcomb, p1vec]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  have : (∑ i, svec q i * (x j * bvec q j i)) = x j * p1vec q (bvec q j) := by
    rw [p1vec, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  rw [this, p1vec_bvec, mul_zero]

theorem Lcomb_coeff6 (q : ℝ[X]) {v : Fin 7 → ℝ} (hv : p1vec q v = 0) :
    Lcomb q (coeff6 v) = v := by
  have hsum : (∑ j : Fin 6, v (Fin.succ j) * svec q (Fin.succ j)) = -7 * v 0 := by
    have h := hv
    rw [p1vec, Fin.sum_univ_succ, svec_zero] at h
    have h2 : (∑ j : Fin 6, svec q (Fin.succ j) * v (Fin.succ j)) = -7 * v 0 := by
      linarith
    rw [← h2]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  funext i
  refine Fin.cases ?_ ?_ i
  · rw [Lcomb, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, bvec_apply_zero, coeff6]
    have : (∑ j : Fin 6, v (Fin.succ j) * (-svec q (Fin.succ j) / 7))
        = -(1 / 7) * ∑ j : Fin 6, v (Fin.succ j) * svec q (Fin.succ j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    rw [this, hsum]
    ring
  · intro i
    rw [Lcomb, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, bvec_apply_succ, coeff6]
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hk
      rw [if_neg (Ne.symm hk)]
      ring
    · intro hi; exact absurd (Finset.mem_univ i) hi

theorem Lcomb_injective (q : ℝ[X]) {x : Fin 6 → ℝ} (h : Lcomb q x = 0) : x = 0 := by
  funext k
  have hk := congrFun h (Fin.succ k)
  rw [Lcomb, Finset.sum_apply] at hk
  simp only [Pi.smul_apply, smul_eq_mul, bvec_apply_succ, Pi.zero_apply] at hk
  rw [Finset.sum_eq_single k] at hk
  · simpa using hk
  · intro j _ hj
    rw [if_neg (Ne.symm hj), mul_zero]
  · intro hk'; exact absurd (Finset.mem_univ k) hk'

theorem bilin_Lcomb (q : ℝ[X]) (x y : Fin 6 → ℝ) :
    bilin (Hmat q) (Lcomb q x) (Lcomb q y)
      = ∑ j, ∑ k, x j * y k * bilin (Hmat q) (bvec q j) (bvec q k) := by
  rw [Lcomb, bilin_sum_left]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Lcomb, bilin_sum_right]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [bilin_smul_left, bilin_smul_right]
  ring

theorem qform_Hmat_Lcomb (q : ℝ[X]) (x : Fin 6 → ℝ) :
    qform (Hmat q) (Lcomb q x) = qform (Gram q) x := by
  rw [qform_eq_bilin (Hmat q) (Lcomb q x), bilin_Lcomb, qform_eq_sum]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
  simp only [Gram]
  ring

theorem Gram_Pconstructible (q : ℝ[X]) (hq : ∀ k, PConstructible (q.coeff k))
    (j k : Fin 6) : PConstructible (Gram q j k) :=
  bilin_Pconstructible (Hmat_Pconstructible q hq) (bvec_Pconstructible q hq j)
    (bvec_Pconstructible q hq k)

theorem Gram_symm (q : ℝ[X]) : (Gram q)ᵀ = Gram q := by
  ext j k
  simp only [Matrix.transpose_apply, Gram]
  rw [bilin_comm (Hmat_symm q)]

/-! ### From polynomials to coefficient vectors

`vecOf f = (f.coeff 0, …, f.coeff 6)` reads off the coefficients of a degree-`≤ 6` polynomial.
It makes `p1vec`, `qform Hmat` and `p3vec` computable in terms of `trace`/`hermiteForm`, which
is what turns the abstract sign results `exists_neg_pair` / `exists_pos_pair` into explicit
directions for the Gram matrix. -/

/-- The coefficient vector `(f.coeff 0, …, f.coeff 6)` of a polynomial. -/
def vecOf (f : ℝ[X]) : Fin 7 → ℝ := fun i => f.coeff i.val

theorem vecOf_Pconstructible {f : ℝ[X]} (hf : ∀ k, PConstructible (f.coeff k))
    (i : Fin 7) : PConstructible (vecOf f i) := hf i.val

theorem polyOfVec_vecOf {f : ℝ[X]} (hf : f.natDegree ≤ 6) : polyOfVec (vecOf f) = f := by
  rw [polyOfVec]
  simp only [vecOf]
  rw [Fin.sum_univ_eq_sum_range (fun k => Polynomial.monomial k (f.coeff k)) 7]
  exact (Polynomial.as_sum_range' f 7 (by omega)).symm

theorem polyOfVec_smul_add {a b : ℝ} {f g : ℝ[X]} (hf : f.natDegree ≤ 6)
    (hg : g.natDegree ≤ 6) :
    polyOfVec (a • vecOf f + b • vecOf g) = C a * f + C b * g := by
  have h1 : a • vecOf f + b • vecOf g = vecOf (C a * f + C b * g) := by
    ext i
    simp only [vecOf, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Polynomial.coeff_add,
      Polynomial.coeff_C_mul]
  rw [h1, polyOfVec_vecOf]
  refine le_trans (Polynomial.natDegree_add_le _ _) ?_
  exact max_le (le_trans (Polynomial.natDegree_C_mul_le a f) hf)
    (le_trans (Polynomial.natDegree_C_mul_le b g) hg)

theorem p1vec_vecOf (q : ℝ[X]) (f : ℝ[X]) (hf : f.natDegree ≤ 6) :
    p1vec q (vecOf f) = Matrix.trace (aeval (companion7 q) f) := by
  rw [p1vec_eq_trace, polyOfVec_vecOf hf]

theorem p1vec_smul_add_vecOf (q : ℝ[X]) (a b : ℝ) (f g : ℝ[X])
    (hf : f.natDegree ≤ 6) (hg : g.natDegree ≤ 6) :
    p1vec q (a • vecOf f + b • vecOf g) =
      a * Matrix.trace (aeval (companion7 q) f) + b * Matrix.trace (aeval (companion7 q) g) := by
  rw [p1vec_eq_trace, polyOfVec_smul_add hf hg, map_add, map_mul, map_mul]
  simp only [Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul,
    Matrix.one_mul, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]

theorem aeval_C_mul_smul (q : ℝ[X]) (a b : ℝ) (f g : ℝ[X]) :
    aeval (companion7 q) (C a * f + C b * g)
      = a • aeval (companion7 q) f + b • aeval (companion7 q) g := by
  rw [map_add, map_mul, map_mul]
  simp only [Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul,
    Matrix.one_mul]

theorem qform_Hmat_smul_add_vecOf (q : ℝ[X]) (a b : ℝ) (f g : ℝ[X])
    (hf : f.natDegree ≤ 6) (hg : g.natDegree ≤ 6) :
    qform (Hmat q) (a • vecOf f + b • vecOf g) =
      Matrix.trace ((aeval (companion7 q) (C a * f + C b * g)) ^ 2) := by
  rw [qform_Hmat_eq_hermiteForm, hermiteForm_eq_trace_sq, polyOfVec_smul_add hf hg]

theorem smul_mul_smul (a b : ℝ) (A B : Matrix (Fin 7) (Fin 7) ℝ) :
    (a • A) * (b • B) = (a * b) • (A * B) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]

theorem trace_sq_smul_add (A B : Matrix (Fin 7) (Fin 7) ℝ) (a b : ℝ) :
    Matrix.trace ((a • A + b • B) ^ 2) =
      a ^ 2 * Matrix.trace (A ^ 2) + 2 * a * b * Matrix.trace (A * B)
        + b ^ 2 * Matrix.trace (B ^ 2) := by
  rw [sq, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
  simp only [smul_mul_smul, Matrix.trace_add, Matrix.trace_smul]
  rw [Matrix.trace_mul_comm B A]
  simp only [pow_two, smul_eq_mul]
  ring

theorem qform_smul (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (x : Fin n → ℝ) :
    qform A (c • x) = c ^ 2 * qform A x := by
  rw [qform_eq_bilin, qform_eq_bilin A x, bilin_smul_left, bilin_smul_right]
  ring

theorem bilin_smul_smul (A : Matrix (Fin n) (Fin n) ℝ) (a b : ℝ) (u v : Fin n → ℝ) :
    bilin A (a • u) (b • v) = a * b * bilin A u v := by
  rw [bilin_smul_left, bilin_smul_right]
  ring

theorem qform_smul_add (A : Matrix (Fin n) (Fin n) ℝ) (hA : Aᵀ = A) (a b : ℝ)
    (u v : Fin n → ℝ) :
    qform A (a • u + b • v) =
      a ^ 2 * qform A u + 2 * a * b * bilin A u v + b ^ 2 * qform A v := by
  rw [qform_add A hA, qform_smul, qform_smul, bilin_smul_smul]
  ring

theorem Lcomb_smul_add (q : ℝ[X]) (a b : ℝ) (x y : Fin 6 → ℝ) :
    Lcomb q (a • x + b • y) = a • Lcomb q x + b • Lcomb q y := by
  rw [Lcomb, Lcomb, Lcomb, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, add_smul]
  module

theorem bilin_congr (A U : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ) :
    bilin (Uᵀ * A * U) x y = bilin A (U *ᵥ x) (U *ᵥ y) := by
  unfold bilin
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

theorem bilin_diag {D : Matrix (Fin n) (Fin n) ℝ} (hdiag : ∀ i j, i ≠ j → D i j = 0)
    (v w : Fin n → ℝ) :
    bilin D v w = ∑ i, D i i * v i * w i := by
  simp only [bilin, dotProduct, Matrix.mulVec_apply, Matrix.row]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_eq_single i]
  · ring
  · intro j _ hji
    simp [hdiag i j (Ne.symm hji)]
  · intro hi; exact absurd (Finset.mem_univ i) hi

/-! ### Negative and positive two-planes in `{p1 = 0}`

`exists_neg_pair` / `exists_pos_pair` produce polynomials supported on two distinct conjugate
pairs.  Their coefficient vectors land in `{p1vec = 0}` (after subtracting the mean in the
positive case), which lets us read them as coordinates in the `b`-basis; the trace identities
then say the restricted form `Gram` is negative definite (resp. positive definite) on the
spanned plane. -/

theorem neg_dir_of_pair (q : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 7)
    (hsep : q.Separable) {z w : ℂ}
    (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0) (hzim : z.im ≠ 0)
    (hw : (q.map (algebraMap ℝ ℂ)).eval w = 0) (hwim : w.im ≠ 0)
    (hzw : z ≠ w) (hzw' : z ≠ starRingEnd ℂ w) :
    ∃ v1 v2 : Fin 6 → ℝ,
      ∀ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) → qform (Gram q) (a • v1 + b • v2) < 0 := by
  obtain ⟨f, g, hfdeg, hgdeg, htrf, htrg, hsqf, hsqg, hcross⟩ :=
    exists_neg_pair q hmon hnat hsep hz hzim hw hwim hzw hzw'
  refine ⟨coeff6 (vecOf f), coeff6 (vecOf g), ?_⟩
  have hpf : p1vec q (vecOf f) = 0 := by rw [p1vec_vecOf q f hfdeg, htrf]
  have hpg : p1vec q (vecOf g) = 0 := by rw [p1vec_vecOf q g hgdeg, htrg]
  intro a b hab
  rw [← qform_Hmat_Lcomb q, Lcomb_smul_add, Lcomb_coeff6 q hpf, Lcomb_coeff6 q hpg]
  rw [qform_Hmat_smul_add_vecOf q a b f g hfdeg hgdeg, aeval_C_mul_smul,
    trace_sq_smul_add, hsqf, hcross, hsqg]
  have hpos : 0 < a ^ 2 + b ^ 2 := by
    rcases hab with ha | hb
    · nlinarith [sq_pos_of_ne_zero ha, sq_nonneg b]
    · nlinarith [sq_nonneg a, sq_pos_of_ne_zero hb]
  nlinarith

theorem aeval_sub_C (q : ℝ[X]) (c : ℝ) (f : ℝ[X]) :
    aeval (companion7 q) (f - C c)
      = aeval (companion7 q) f - c • (1 : Matrix (Fin 7) (Fin 7) ℝ) := by
  rw [map_sub, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]

theorem trace_sq_sub_scalar (A : Matrix (Fin 7) (Fin 7) ℝ) (c : ℝ) :
    Matrix.trace ((A - c • 1) ^ 2) =
      Matrix.trace (A ^ 2) - 2 * c * Matrix.trace A + c ^ 2 * 7 := by
  have h : A - c • 1 = (1 : ℝ) • A + (-c) • (1 : Matrix (Fin 7) (Fin 7) ℝ) := by
    rw [one_smul, neg_smul, sub_eq_add_neg]
  rw [h, trace_sq_smul_add, Matrix.mul_one]
  simp only [pow_two, one_mul, mul_one, Matrix.trace_one]
  norm_num
  ring

theorem aeval_sub_C_smul_add (q : ℝ[X]) (a b c : ℝ) (f g : ℝ[X]) :
    aeval (companion7 q) (C a * (f - C c) + C b * (g - C c))
      = a • aeval (companion7 q) f + b • aeval (companion7 q) g - ((a + b) * c) • 1 := by
  rw [aeval_C_mul_smul, aeval_sub_C, aeval_sub_C]
  module

theorem pos_dir_of_pair (q : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 7)
    (hsep : q.Separable) {z w : ℂ}
    (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0) (hzim : z.im ≠ 0)
    (hw : (q.map (algebraMap ℝ ℂ)).eval w = 0) (hwim : w.im ≠ 0)
    (hzw : z ≠ w) (hzw' : z ≠ starRingEnd ℂ w) :
    ∃ v1 v2 : Fin 6 → ℝ,
      ∀ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) → 0 < qform (Gram q) (a • v1 + b • v2) := by
  obtain ⟨f, g, hfdeg, hgdeg, htrf, htrg, hsqf, hsqg, hcross⟩ :=
    exists_pos_pair q hmon hnat hsep hz hzim hw hwim hzw hzw'
  refine ⟨coeff6 (vecOf (f - C (2 / 7))), coeff6 (vecOf (g - C (2 / 7))), ?_⟩
  have hf'deg : (f - C (2 / 7)).natDegree ≤ 6 := by
    refine le_trans (Polynomial.natDegree_sub_le f (C (2 / 7))) ?_
    rw [Polynomial.natDegree_C, max_eq_left (Nat.zero_le _)]
    exact hfdeg
  have hg'deg : (g - C (2 / 7)).natDegree ≤ 6 := by
    refine le_trans (Polynomial.natDegree_sub_le g (C (2 / 7))) ?_
    rw [Polynomial.natDegree_C, max_eq_left (Nat.zero_le _)]
    exact hgdeg
  have hpf : p1vec q (vecOf (f - C (2 / 7))) = 0 := by
    rw [p1vec_vecOf q (f - C (2 / 7)) hf'deg, aeval_sub_C, Matrix.trace_sub,
      Matrix.trace_smul, htrf, Matrix.trace_one]
    norm_num
  have hpg : p1vec q (vecOf (g - C (2 / 7))) = 0 := by
    rw [p1vec_vecOf q (g - C (2 / 7)) hg'deg, aeval_sub_C, Matrix.trace_sub,
      Matrix.trace_smul, htrg, Matrix.trace_one]
    norm_num
  intro a b hab
  rw [← qform_Hmat_Lcomb q, Lcomb_smul_add, Lcomb_coeff6 q hpf, Lcomb_coeff6 q hpg]
  rw [qform_Hmat_smul_add_vecOf q a b (f - C (2 / 7)) (g - C (2 / 7)) hf'deg hg'deg,
    aeval_sub_C_smul_add, trace_sq_sub_scalar]
  have htrA : Matrix.trace (a • aeval (companion7 q) f + b • aeval (companion7 q) g)
      = 2 * a + 2 * b := by
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, htrf, htrg]
    simp only [smul_eq_mul]
    ring
  have hsqA : Matrix.trace ((a • aeval (companion7 q) f + b • aeval (companion7 q) g) ^ 2)
      = 2 * a ^ 2 + 2 * b ^ 2 := by
    rw [trace_sq_smul_add, hsqf, hcross, hsqg]
    ring
  rw [htrA, hsqA]
  have hpos : 0 < a ^ 2 + b ^ 2 := by
    rcases hab with ha | hb
    · nlinarith [sq_pos_of_ne_zero ha, sq_nonneg b]
    · nlinarith [sq_nonneg a, sq_pos_of_ne_zero hb]
  nlinarith [sq_nonneg (a - 2 * b), sq_nonneg a, sq_nonneg b]

theorem sq_smul_add (A B : Matrix (Fin 7) (Fin 7) ℝ) (a b : ℝ) :
    (a • A + b • B) ^ 2 =
      a ^ 2 • A ^ 2 + (a * b) • (A * B) + (a * b) • (B * A) + b ^ 2 • B ^ 2 := by
  rw [sq, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
  simp only [smul_mul_smul, pow_two]
  rw [mul_comm b a]
  abel

theorem cube_add (X Y : Matrix (Fin 7) (Fin 7) ℝ) :
    (X + Y) ^ 3 = X ^ 3 + X ^ 2 * Y + X * Y * X + Y * X ^ 2 + X * Y ^ 2
      + Y * X * Y + Y ^ 2 * X + Y ^ 3 := by
  noncomm_ring

theorem smul_pow (c : ℝ) (M : Matrix (Fin 7) (Fin 7) ℝ) (n : ℕ) :
    (c • M) ^ n = (c ^ n) • M ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, smul_mul_smul, ← pow_succ, ← pow_succ]

theorem cube_smul_add (A B : Matrix (Fin 7) (Fin 7) ℝ) (a b : ℝ) :
    (a • A + b • B) ^ 3 =
      (a * a * a) • (A * A * A) + (a * a * b) • (A * A * B) + (a * a * b) • (A * B * A)
        + (a * b * b) • (A * B * B) + (a * a * b) • (B * A * A)
        + (a * b * b) • (B * A * B) + (a * b * b) • (B * B * A) + (b * b * b) • (B * B * B) := by
  rw [show (a • A + b • B) ^ 3 = _ from cube_add (a • A) (b • B)]
  simp only [smul_mul_smul, pow_succ, pow_zero, Matrix.one_mul, mul_assoc, mul_comm,
    mul_left_comm]
  abel

theorem trace_cube_smul_add (A B : Matrix (Fin 7) (Fin 7) ℝ) (a b : ℝ) :
    Matrix.trace ((a • A + b • B) ^ 3) = a ^ 3 * Matrix.trace (A ^ 3)
      + 3 * a ^ 2 * b * Matrix.trace (A ^ 2 * B) + 3 * a * b ^ 2 * Matrix.trace (A * B ^ 2)
      + b ^ 3 * Matrix.trace (B ^ 3) := by
  rw [cube_smul_add, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add,
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

theorem Lcomb_smul (q : ℝ[X]) (c : ℝ) (x : Fin 6 → ℝ) :
    Lcomb q (c • x) = c • Lcomb q x := by
  rw [Lcomb, Lcomb, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Pi.smul_apply, smul_eq_mul, smul_smul]

theorem Lcomb_sub (q : ℝ[X]) (x y : Fin 6 → ℝ) :
    Lcomb q (x - y) = Lcomb q x - Lcomb q y := by
  rw [Lcomb, Lcomb, Lcomb, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Pi.sub_apply, sub_smul]

theorem mulVec_Pconstructible {U : Matrix (Fin 6) (Fin 6) ℝ}
    (hU : ∀ i j, PConstructible (U i j)) {x : Fin 6 → ℝ}
    (hx : ∀ j, PConstructible (x j)) (i : Fin 6) :
    PConstructible ((U *ᵥ x) i) := by
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_Pconstructible Finset.univ (fun j => U i j * x j)
    (fun j _ => PConstructible.mul (hU i j) (hx j))

theorem Lcomb_Pconstructible (q : ℝ[X]) (hq : ∀ k, PConstructible (q.coeff k))
    {x : Fin 6 → ℝ} (hx : ∀ j, PConstructible (x j)) :
    ∀ i, PConstructible (Lcomb q x i) := by
  intro i
  rw [Lcomb, Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_Pconstructible Finset.univ (fun j => x j * bvec q j i)
    (fun j _ => PConstructible.mul (hx j) (bvec_Pconstructible q hq j i))

theorem mulVec_eq_zero_of_det_ne_zero {U : Matrix (Fin n) (Fin n) ℝ} (hU : U.det ≠ 0)
    {z : Fin n → ℝ} (h : U *ᵥ z = 0) : z = 0 := by
  have h1 : U⁻¹ * U = 1 := nonsing_inv_mul U (isUnit_iff_ne_zero.mpr hU)
  calc z = 1 *ᵥ z := (Matrix.one_mulVec z).symm
    _ = (U⁻¹ * U) *ᵥ z := by rw [h1]
    _ = U⁻¹ *ᵥ (U *ᵥ z) := by rw [Matrix.mulVec_mulVec]
    _ = 0 := by rw [h, Matrix.mulVec_zero]

theorem bilin_eq_sum (A : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ) :
    bilin A x y = ∑ j, ∑ k, x j * A j k * y k := by
  simp only [bilin, dotProduct, Matrix.mulVec_apply, Matrix.row]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

theorem bilin_Hmat_Lcomb (q : ℝ[X]) (x y : Fin 6 → ℝ) :
    bilin (Hmat q) (Lcomb q x) (Lcomb q y) = bilin (Gram q) x y := by
  rw [bilin_Lcomb, bilin_eq_sum]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
  simp only [Gram]
  ring

theorem trace_pow_Pconstructible {M : Matrix (Fin 7) (Fin 7) ℝ}
    (hM : ∀ i j, PConstructible (M i j)) (k : ℕ) :
    PConstructible (Matrix.trace (M ^ k)) := by
  rw [Matrix.trace]
  exact Finset.sum_Pconstructible Finset.univ (fun i => (M ^ k) i i)
    (fun i _ => matrix_pow_entries_Pconstructible hM k i i)

theorem trace_mul_Pconstructible {A B : Matrix (Fin 7) (Fin 7) ℝ}
    (hA : ∀ i j, PConstructible (A i j)) (hB : ∀ i j, PConstructible (B i j)) :
    PConstructible (Matrix.trace (A * B)) := by
  rw [Matrix.trace]
  exact Finset.sum_Pconstructible Finset.univ (fun i => (A * B) i i)
    (fun i _ => matrix_mul_entries_Pconstructible hA hB i i)

theorem coeff_finset_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ[X]) (k : ℕ) :
    (∑ i ∈ s, f i).coeff k = ∑ i ∈ s, (f i).coeff k := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Polynomial.coeff_add, ih]

theorem polyOfVec_coeff_Pconstructible (v : Fin 7 → ℝ) (hv : ∀ i, PConstructible (v i))
    (k : ℕ) : PConstructible ((polyOfVec v).coeff k) := by
  rw [polyOfVec, coeff_finset_sum]
  refine Finset.sum_Pconstructible Finset.univ
    (fun i => (Polynomial.monomial i.val (v i)).coeff k) (fun i _ => ?_)
  rw [Polynomial.coeff_monomial]
  split_ifs with h
  · exact hv i
  · exact zero_Pconstructible

theorem polyOfVec_natDegree_le (v : Fin 7 → ℝ) : (polyOfVec v).natDegree ≤ 6 := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (fun k hk => ?_)
  rw [polyOfVec, coeff_finset_sum]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [Polynomial.coeff_monomial]
  split_ifs with h
  · exact absurd h (by omega)
  · rfl

theorem polyOfVec_ne_zero {v : Fin 7 → ℝ} (hv : v ≠ 0) : polyOfVec v ≠ 0 := by
  intro h
  apply hv
  funext i
  have hc : (polyOfVec v).coeff i.val = 0 := by rw [h, Polynomial.coeff_zero]
  rw [polyOfVec, coeff_finset_sum] at hc
  rw [Finset.sum_eq_single i] at hc
  · simpa [Polynomial.coeff_monomial] using hc
  · intro j _ hji
    rw [Polynomial.coeff_monomial]
    split_ifs with h'
    · exact absurd (Fin.ext h') hji
    · rfl
  · intro hi; exact absurd (Finset.mem_univ i) hi

theorem aeval_polyOfVec_smul_add (q : ℝ[X]) (s t : ℝ) (x y : Fin 7 → ℝ) :
    aeval (companion7 q) (polyOfVec (s • x + t • y))
      = s • aeval (companion7 q) (polyOfVec x)
        + t • aeval (companion7 q) (polyOfVec y) := by
  rw [aeval_polyOfVec, aeval_polyOfVec, aeval_polyOfVec, Finset.smul_sum, Finset.smul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, add_smul, smul_smul,
    smul_smul]

theorem p1vec_smul_add (q : ℝ[X]) (s t : ℝ) (x y : Fin 7 → ℝ) :
    p1vec q (s • x + t • y) = s * p1vec q x + t * p1vec q y := by
  rw [p1vec_eq_trace, aeval_polyOfVec_smul_add, Matrix.trace_add, Matrix.trace_smul,
    Matrix.trace_smul, p1vec_eq_trace q x, p1vec_eq_trace q y]
  simp only [smul_eq_mul]


/-! ### The main trace-killing Tschirnhaus polynomial

Assembly of the `s ≥ 2` construction: the two definite two-planes from `neg_dir_of_pair` and
`pos_dir_of_pair` produce, via inertia and diagonalisation, a totally isotropic plane for the
quadratic part on `{p1 = 0}`; the cubic part restricted to that plane is a binary cubic, and
`binary_cubic_zero` picks a P-constructible zero `s • cv + t • cw`. The resulting `φ` has
vanishing first three trace power sums. -/

-- Theorem: if `w` is not a scalar multiple of a nonzero `v`, then `s • v + t • w = 0` forces
-- `s = t = 0` (used to show the constructed `φ` is nonzero).
theorem smul_add_smul_eq_zero_of_not_parallel {V : Type*} [AddCommGroup V] [Module ℝ V]
    {v w : V} (hv : v ≠ 0) (h : ¬ ∃ c : ℝ, w = c • v) {s t : ℝ}
    (hst : s • v + t • w = 0) : s = 0 ∧ t = 0 := by
  by_cases ht : t = 0
  · subst ht
    simp only [zero_smul, add_zero] at hst
    rcases smul_eq_zero.mp hst with h1 | h1
    · exact ⟨h1, rfl⟩
    · exact absurd h1 hv
  · exfalso
    apply h
    refine ⟨-(s * t⁻¹), ?_⟩
    have h1 : t • w = -(s • v) := eq_neg_of_add_eq_zero_right hst
    calc w = t⁻¹ • (t • w) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
      _ = t⁻¹ • (-(s • v)) := by rw [h1]
      _ = (-(s * t⁻¹)) • v := by rw [smul_neg, smul_smul, ← neg_smul, mul_comm]

theorem exists_tschirnhaus_traces (q : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 7)
    (hsep : q.Separable) (hq : ∀ k, PConstructible (q.coeff k)) {z w : ℂ}
    (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0) (hzim : z.im ≠ 0)
    (hw : (q.map (algebraMap ℝ ℂ)).eval w = 0) (hwim : w.im ≠ 0)
    (hzw : z ≠ w) (hzw' : z ≠ starRingEnd ℂ w) :
    ∃ φ : ℝ[X], (∀ k, PConstructible (φ.coeff k)) ∧ φ.natDegree ≤ 6 ∧ φ ≠ 0 ∧
      Matrix.trace (aeval (companion7 q) φ) = 0 ∧
      Matrix.trace ((aeval (companion7 q) φ) ^ 2) = 0 ∧
      Matrix.trace ((aeval (companion7 q) φ) ^ 3) = 0 := by
  obtain ⟨v1, v2, hneg⟩ := neg_dir_of_pair q hmon hnat hsep hz hzim hw hwim hzw hzw'
  obtain ⟨w1, w2, hpos⟩ := pos_dir_of_pair q hmon hnat hsep hz hzim hw hwim hzw hzw'
  obtain ⟨U, D, hUP, hDP, hDdiag, hUD, hUdet⟩ :=
    exists_diag_congruence (Gram q) (Gram_symm q) (Gram_Pconstructible q hq)
  obtain ⟨i1, i2, hi12, hi1, hi2⟩ := two_neg_diag_of_pair hDdiag hUD hUdet hneg
  obtain ⟨j1, j2, hj12, hj1, hj2⟩ := two_pos_diag_of_pair hDdiag hUD hUdet hpos
  obtain ⟨v, wv, hvP, hwP, hvne, hwne, hqv, hqw, hbvw, hindep⟩ :=
    exists_diagonal_isotropic_vectors (fun i => D i i) (fun i => hDP i i) (by norm_num)
      ⟨j1, j2, hj12, hj1, hj2⟩ ⟨i1, i2, hi12, hi1, hi2⟩
  set cv : Fin 7 → ℝ := Lcomb q (U *ᵥ v) with hcv
  set cw : Fin 7 → ℝ := Lcomb q (U *ᵥ wv) with hcw
  have hcvP : ∀ i, PConstructible (cv i) :=
    Lcomb_Pconstructible q hq (mulVec_Pconstructible hUP hvP)
  have hcwP : ∀ i, PConstructible (cw i) :=
    Lcomb_Pconstructible q hq (mulVec_Pconstructible hUP hwP)
  have hqformv : qform (Hmat q) cv = 0 := by
    rw [hcv, qform_Hmat_Lcomb, ← qform_congr, hUD, qform_diag hDdiag, hqv]
  have hqformw : qform (Hmat q) cw = 0 := by
    rw [hcw, qform_Hmat_Lcomb, ← qform_congr, hUD, qform_diag hDdiag, hqw]
  have hbilinc : bilin (Hmat q) cv cw = 0 := by
    rw [hcv, hcw, bilin_Hmat_Lcomb, ← bilin_congr, hUD, bilin_diag hDdiag, hbvw]
  have hp1v : p1vec q cv = 0 := by rw [hcv, p1vec_Lcomb]
  have hp1w : p1vec q cw = 0 := by rw [hcw, p1vec_Lcomb]
  have hindep' : ¬ ∃ c : ℝ, cw = c • cv := by
    rintro ⟨c, hc⟩
    have h1 : Lcomb q (U *ᵥ wv - c • (U *ᵥ v)) = 0 := by
      rw [Lcomb_sub, Lcomb_smul, ← hcw, ← hcv, hc, sub_self]
    have h2 : U *ᵥ wv - c • (U *ᵥ v) = 0 := Lcomb_injective q h1
    have h3 : U *ᵥ (wv - c • v) = 0 := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, h2]
    have h4 : wv - c • v = 0 := mulVec_eq_zero_of_det_ne_zero hUdet h3
    exact hindep ⟨c, sub_eq_zero.mp h4⟩
  have hcvne : cv ≠ 0 := by
    intro h0
    have h1 : U *ᵥ v = 0 := Lcomb_injective q (by rw [hcv] at h0; exact h0)
    exact hvne (mulVec_eq_zero_of_det_ne_zero hUdet h1)
  have hcwne : cw ≠ 0 := by
    intro h0
    have h1 : U *ᵥ wv = 0 := Lcomb_injective q (by rw [hcw] at h0; exact h0)
    exact hwne (mulVec_eq_zero_of_det_ne_zero hUdet h1)
  set Ncv : Matrix (Fin 7) (Fin 7) ℝ := aeval (companion7 q) (polyOfVec cv) with hNcv
  set Ncw : Matrix (Fin 7) (Fin 7) ℝ := aeval (companion7 q) (polyOfVec cw) with hNcw
  have hNcvP : ∀ i j, PConstructible (Ncv i j) := by
    intro i j
    rw [hNcv]
    exact aeval_entries_Pconstructible _ (companion7_entries_Pconstructible hq) _
      (polyOfVec_coeff_Pconstructible cv hcvP) i j
  have hNcwP : ∀ i j, PConstructible (Ncw i j) := by
    intro i j
    rw [hNcw]
    exact aeval_entries_Pconstructible _ (companion7_entries_Pconstructible hq) _
      (polyOfVec_coeff_Pconstructible cw hcwP) i j
  have hA : PConstructible (p3vec q cv) := by
    rw [p3vec, ← hNcv]; exact trace_pow_Pconstructible hNcvP 3
  have hDc : PConstructible (p3vec q cw) := by
    rw [p3vec, ← hNcw]; exact trace_pow_Pconstructible hNcwP 3
  have hB : PConstructible (3 * Matrix.trace (Ncv ^ 2 * Ncw)) :=
    PConstructible.mul (by pconstructible)
      (trace_mul_Pconstructible (matrix_pow_entries_Pconstructible hNcvP 2) hNcwP)
  have hC : PConstructible (3 * Matrix.trace (Ncv * Ncw ^ 2)) :=
    PConstructible.mul (by pconstructible)
      (trace_mul_Pconstructible hNcvP (matrix_pow_entries_Pconstructible hNcwP 2))
  obtain ⟨s, t, hsP, htP, _hstne, hcub⟩ :=
    binary_cubic_zero (a := p3vec q cv) (b := 3 * Matrix.trace (Ncv ^ 2 * Ncw))
      (c := 3 * Matrix.trace (Ncv * Ncw ^ 2)) (d := p3vec q cw) hA hB hC hDc
  set ψ : Fin 7 → ℝ := s • cv + t • cw with hψ
  have hψP : ∀ i, PConstructible (ψ i) := by
    intro i
    rw [hψ, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    exact PConstructible.add (PConstructible.mul hsP (hcvP i))
      (PConstructible.mul htP (hcwP i))
  have hψne : ψ ≠ 0 := by
    intro h0
    have hcomb : s • cv + t • cw = 0 := by rw [← hψ]; exact h0
    obtain ⟨hs0, ht0⟩ := smul_add_smul_eq_zero_of_not_parallel hcvne hindep' hcomb
    rcases _hstne with h | h
    · exact h hs0
    · exact h ht0
  refine ⟨polyOfVec ψ, polyOfVec_coeff_Pconstructible ψ hψP, polyOfVec_natDegree_le ψ,
    polyOfVec_ne_zero hψne, ?_, ?_, ?_⟩
  · rw [← p1vec_eq_trace, hψ, p1vec_smul_add, hp1v, hp1w]
    ring
  · rw [← hermiteForm_eq_trace_sq q ψ, ← qform_Hmat_eq_hermiteForm, hψ,
      qform_smul_add (Hmat q) (Hmat_symm q), hqformv, hbilinc, hqformw]
    ring
  · have haeval : aeval (companion7 q) (polyOfVec ψ) = s • Ncv + t • Ncw := by
      rw [hψ, aeval_polyOfVec_smul_add, hNcv, hNcw]
    have hAc : p3vec q cv = Matrix.trace (Ncv ^ 3) := by rw [p3vec, ← hNcv]
    have hDc' : p3vec q cw = Matrix.trace (Ncw ^ 3) := by rw [p3vec, ← hNcw]
    rw [haeval, trace_cube_smul_add]
    rw [hAc, hDc'] at hcub
    ring_nf at hcub ⊢
    linarith

end

end Pconstructible
