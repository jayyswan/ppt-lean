import Pptc.ScratchD
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

open Polynomial Matrix

namespace Pconstructible

/-! ### E1: the Hermite matrix entries are P-constructible -/

-- Theorem: the trace of the `k`-th power of the companion matrix is P-constructible.
theorem trace_pow_companion7_Pconstructible (q : ℝ[X])
    (hq : ∀ k, PConstructible (q.coeff k)) (k : ℕ) :
    PConstructible (Matrix.trace ((companion7 q) ^ k)) := by
  rw [Matrix.trace]
  exact Finset.sum_induction _ PConstructible (fun _ _ ha hb => PConstructible.add ha hb)
    zero_Pconstructible (fun i _ => matrix_pow_entries_Pconstructible
      (companion7_entries_Pconstructible hq) k i i)

-- Theorem: `H i j = trace (M ^ (i + j))` is P-constructible.
theorem traceH_Pconstructible (q : ℝ[X]) (hq : ∀ k, PConstructible (q.coeff k))
    (i j : Fin 7) :
    PConstructible (Matrix.trace ((companion7 q) ^ (i.val + j.val))) :=
  trace_pow_companion7_Pconstructible q hq (i.val + j.val)

/-! ### The Hermite form built from the companion matrix -/

/-- The Hermite (trace) form of `q`, in the monomial basis `1, X, …, X⁶`. -/
noncomputable def hermiteForm (q : ℝ[X]) (v : Fin 7 → ℝ) : ℝ :=
  ∑ i, ∑ j, v i * Matrix.trace ((companion7 q) ^ (i.val + j.val)) * v j

/-- The polynomial whose coefficient vector is `v`. -/
noncomputable def polyOfVec (v : Fin 7 → ℝ) : ℝ[X] :=
  ∑ i : Fin 7, Polynomial.monomial i.val (v i)

-- Theorem: the Hermite form of P-constructible coefficients is P-constructible.
theorem hermiteForm_Pconstructible (q : ℝ[X]) (hq : ∀ k, PConstructible (q.coeff k))
    (v : Fin 7 → ℝ) (hv : ∀ i, PConstructible (v i)) :
    PConstructible (hermiteForm q v) := by
  rw [hermiteForm]
  refine Finset.sum_induction _ PConstructible (fun _ _ ha hb => PConstructible.add ha hb)
    zero_Pconstructible (fun i _ => ?_)
  refine Finset.sum_induction _ PConstructible (fun _ _ ha hb => PConstructible.add ha hb)
    zero_Pconstructible (fun j _ => ?_)
  exact PConstructible.mul
    (PConstructible.mul (hv i) (traceH_Pconstructible q hq i j)) (hv j)

-- Theorem: `aeval` of the coefficient vector is the corresponding matrix polynomial.
theorem aeval_polyOfVec (q : ℝ[X]) (v : Fin 7 → ℝ) :
    aeval (companion7 q) (polyOfVec v) = ∑ i : Fin 7, v i • (companion7 q) ^ i.val := by
  rw [polyOfVec, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one]
  rw [Matrix.smul_mul, Matrix.one_mul]

-- Theorem: the square of that matrix polynomial expands into the Hermite basis.
theorem aeval_polyOfVec_sq (q : ℝ[X]) (v : Fin 7 → ℝ) :
    (aeval (companion7 q) (polyOfVec v)) ^ 2 =
      ∑ i : Fin 7, ∑ j : Fin 7, (v i * v j) • (companion7 q) ^ (i.val + j.val) := by
  rw [aeval_polyOfVec, pow_two, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_add]

-- Theorem: the Hermite form is the trace of the square of the matrix polynomial.
theorem trace_aeval_polyOfVec_sq (q : ℝ[X]) (v : Fin 7 → ℝ) :
    Matrix.trace ((aeval (companion7 q) (polyOfVec v)) ^ 2) = hermiteForm q v := by
  rw [aeval_polyOfVec_sq, hermiteForm, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Matrix.trace_smul, smul_eq_mul]
  ring

-- Theorem: conversely, the Hermite form equals that trace.
theorem hermiteForm_eq_trace_sq (q : ℝ[X]) (v : Fin 7 → ℝ) :
    hermiteForm q v = Matrix.trace ((aeval (companion7 q) (polyOfVec v)) ^ 2) :=
  (trace_aeval_polyOfVec_sq q v).symm

-- Theorem: a polynomial of degree at most six whose matrix square has negative trace
-- produces a negative direction for the Hermite form. This reduces the existence part
-- of E2 to a statement about real polynomials rather than vectors.
theorem traceForm_neg_of_poly (q : ℝ[X]) (f : ℝ[X]) (hdeg : f.natDegree ≤ 6)
    (hneg : Matrix.trace ((aeval (companion7 q) f) ^ 2) < 0) :
    ∃ v : Fin 7 → ℝ, hermiteForm q v < 0 := by
  refine ⟨fun i => f.coeff i.val, ?_⟩
  rw [hermiteForm_eq_trace_sq]
  have hpoly : polyOfVec (fun i : Fin 7 => f.coeff i.val) = f := by
    rw [polyOfVec]
    rw [Fin.sum_univ_eq_sum_range (fun k => Polynomial.monomial k (f.coeff k)) 7]
    exact (Polynomial.as_sum_range' f 7 (by omega)).symm
  rw [hpoly]
  exact hneg

-- Theorem: the Hermite form is symmetric.
theorem hermiteForm_comm (q : ℝ[X]) (v w : Fin 7 → ℝ) :
    (∑ i, ∑ j, v i * Matrix.trace ((companion7 q) ^ (i.val + j.val)) * w j) =
    (∑ i, ∑ j, w i * Matrix.trace ((companion7 q) ^ (i.val + j.val)) * v j) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [Nat.add_comm i.val j.val]
  ring

/-! ### Route to E2

By `hermiteForm_eq_trace_sq`, a negative direction for the Hermite form is exactly a
polynomial `F` of degree `≤ 6` with `trace (F(M)²) < 0`, and `traceForm_neg_of_poly`
turns such an `F` into the vector `v`. The remaining gap is producing `F`.

An elementary construction avoiding Hermite's inertia theorem: write `q = p * G` with
`p` the irreducible real quadratic annihilating the non-real root. Bezout gives
`e = v * G` with `e² = e`, `e ≡ 1 mod p`, `e ≡ 0 mod G`; then `e(M)` is the projector
onto the two-dimensional `p`-primary component, so `trace (e(M)) = 2`. Since the map
`h ↦ h(z)` from linear real polynomials to `ℂ` is onto, choose linear `h` whose value
at `z` is `1 / G(z)` times the imaginary unit; then `F = G * h` satisfies `F² = -e` in
`ℝ[X]/(q)`, whence
`trace (F(M)²) = -trace (e(M)) = -2 < 0`.

What is missing in Mathlib for this: `Matrix.charpoly (companion7 q) = q` (so
Cayley–Hamilton gives `q(M) = 0`), the analogue of the eigenvector lemmas over `ℂ`,
and `trace = rank` for idempotent matrices. -/

end Pconstructible
