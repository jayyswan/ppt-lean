import Pptc.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Notation

open Polynomial
open Matrix

namespace Pconstructible

/-! ## C1: completing the square in two variables -/

-- Theorem: completing the square in two variables: the binary quadratic form
-- `a x² + 2 b x y + c y²` becomes diagonal in the coordinates `X = x + (b/a) y`,
-- `Y = y`, namely `a X² + (c - b²/a) Y²`.
theorem complete_square2 {a b c : ℝ} (ha : a ≠ 0) :
    ∀ x y : ℝ,
      a * (x + b / a * y) ^ 2 + (c - b ^ 2 / a) * y ^ 2
        = a * x ^ 2 + 2 * b * x * y + c * y ^ 2 := by
  intro x y
  field_simp
  ring

-- Theorem: the same identity as an explicit congruence of symmetric `2 × 2` matrices,
-- by the invertible matrix `U = !![1, -b/a; 0, 1]`.
theorem complete_square2_congruence {a b c : ℝ} (ha : a ≠ 0) :
    ∃ U D : Matrix (Fin 2) (Fin 2) ℝ,
      U = !![1, -b / a; 0, 1] ∧
        D = !![a, 0; 0, c - b ^ 2 / a] ∧
        Uᵀ * !![a, b; b, c] * U = D := by
  refine ⟨!![1, -b / a; 0, 1], !![a, 0; 0, c - b ^ 2 / a], rfl, rfl, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> ring

-- Theorem: the P-constructible-entries version of `complete_square2_congruence`.
theorem complete_square2_congruence_Pconstructible {a b c : ℝ}
    (ha : PConstructible a) (hb : PConstructible b) (hc : PConstructible c) (hane : a ≠ 0) :
    ∃ U D : Matrix (Fin 2) (Fin 2) ℝ,
      (∀ i j, PConstructible (U i j)) ∧
        (∀ i j, PConstructible (D i j)) ∧
        (∀ i j, i ≠ j → D i j = 0) ∧
        Uᵀ * !![a, b; b, c] * U = D := by
  refine ⟨!![1, -b / a; 0, 1], !![a, 0; 0, c - b ^ 2 / a], ?_, ?_, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> simp <;> pconstructible
  · intro i j
    fin_cases i <;> fin_cases j <;> simp <;> pconstructible
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      field_simp <;> ring

/-! ## C2: diagonalizing a symmetric matrix with P-constructible entries

The `Fin 2` case is done explicitly, by the three-way case split on the diagonal entries
(diagonalize directly if the leading entry is nonzero, swap the coordinates if the other
diagonal entry is nonzero, and use the hyperbolic change of basis `!![1,1;1,-1]` when both
vanish). -/

-- Theorem: a symmetric `2 × 2` real matrix with P-constructible entries is congruent,
-- by a matrix with P-constructible entries, to a diagonal matrix with P-constructible
-- entries.
theorem exists_diag_congruence_two (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hsym : Aᵀ = A) (hA : ∀ i j, PConstructible (A i j)) :
    ∃ U D : Matrix (Fin 2) (Fin 2) ℝ,
      (∀ i j, PConstructible (U i j)) ∧
        (∀ i j, PConstructible (D i j)) ∧
        (∀ i j, i ≠ j → D i j = 0) ∧
        Uᵀ * A * U = D := by
  set a : ℝ := A 0 0 with ha'
  set b : ℝ := A 0 1 with hb'
  set c : ℝ := A 1 1 with hc'
  have haP : PConstructible a := hA 0 0
  have hbP : PConstructible b := hA 0 1
  have hcP : PConstructible c := hA 1 1
  have h10 : A 1 0 = b := by
    have h := congrFun (congrFun hsym 0) 1
    simpa [← hb'] using h
  have hAeq : A = !![a, b; b, c] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha', hb', hc', h10]
  by_cases hane : a ≠ 0
  · obtain ⟨U, D, hU, hD, hdiag, hUD⟩ :=
      complete_square2_congruence_Pconstructible haP hbP hcP hane
    exact ⟨U, D, hU, hD, hdiag, by simpa [hAeq] using hUD⟩
  · push Not at hane
    by_cases hcne : c ≠ 0
    · refine ⟨!![0, 1; 1, -b / c], !![c, 0; 0, -b ^ 2 / c], ?_, ?_, ?_, ?_⟩
      · intro i j
        fin_cases i <;> fin_cases j <;> simp <;> pconstructible
      · intro i j
        fin_cases i <;> fin_cases j <;> simp <;> pconstructible
      · intro i j hij
        fin_cases i <;> fin_cases j <;> simp at hij ⊢
      · rw [hAeq, hane]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
          field_simp <;> ring
    · push Not at hcne
      refine ⟨!![1, 1; 1, -1], !![2 * b, 0; 0, -(2 * b)], ?_, ?_, ?_, ?_⟩
      · intro i j
        fin_cases i <;> fin_cases j <;> simp <;> pconstructible
      · intro i j
        fin_cases i <;> fin_cases j <;> simp <;> pconstructible
      · intro i j hij
        fin_cases i <;> fin_cases j <;> simp at hij ⊢
      · rw [hAeq, hane, hcne]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
          ring

/-! ## C3: the totally isotropic plane of the `(2,2)` form, and cubics on it

On `ℝ⁴` with the standard form `Q(y) = y₀² + y₁² - y₂² - y₃²` of signature `(2,2)`, the
plane `y₂ = y₀`, `y₃ = y₁` is totally isotropic: `Q` and its polar form `B` both vanish
identically there. Reading a homogeneous cubic off that plane along `q = 1` gives an
ordinary real cubic, whose P-constructible root yields a P-constructible nonzero
isotropic vector. -/

/-- The standard quadratic form of signature `(2, 2)` on `ℝ⁴`. -/
def form22 (y : Fin 4 → ℝ) : ℝ := y 0 ^ 2 + y 1 ^ 2 - y 2 ^ 2 - y 3 ^ 2

/-- The polar bilinear form of `form22`. -/
def bilin22 (v w : Fin 4 → ℝ) : ℝ :=
  v 0 * w 0 + v 1 * w 1 - v 2 * w 2 - v 3 * w 3

/-- The point `(p, q, p, q)` of the plane `y₂ = y₀`, `y₃ = y₁`, written as a vector. -/
def planeVec (p q : ℝ) : Fin 4 → ℝ := ![p, q, p, q]

-- Theorem: the plane `y₂ = y₀`, `y₃ = y₁` is totally isotropic for `form22`: the quadratic
-- form vanishes at every point of it.
theorem form22_planeVec (p q : ℝ) : form22 (planeVec p q) = 0 := by
  simp [form22, planeVec]

-- Theorem: ... and so does the polar form, on every pair of points of it.
theorem bilin22_planeVec (p q p' q' : ℝ) :
    bilin22 (planeVec p q) (planeVec p' q') = 0 := by
  simp [bilin22, planeVec]

-- Theorem: the polar form of `form22` is the quadratic form itself when the two arguments
-- agree.
theorem bilin22_self (v : Fin 4 → ℝ) : bilin22 v v = form22 v := by
  simp [bilin22, form22]
  ring

/-- A homogeneous binary cubic `a p³ + b p² q + c p q² + d q³`. -/
def hCubic (a b c d p q : ℝ) : ℝ := a * p ^ 3 + b * p ^ 2 * q + c * p * q ^ 2 + d * q ^ 3

-- Theorem: restricting a binary cubic to the line `q = 1` recovers the ordinary cubic
-- `cubicVal d c b a` used by the root construction in `Pptc.Basic`.
theorem hCubic_one (a b c d p : ℝ) : hCubic a b c d p 1 = cubicVal d c b a p := by
  simp [hCubic, cubicVal]

-- Theorem: restricting any homogeneous cubic of four variables to the isotropic plane is a
-- binary cubic: scaling `(p, q)` scales the restriction by the cube.
theorem restrict_plane_homogeneous (F : (Fin 4 → ℝ) → ℝ)
    (hF : ∀ (t : ℝ) (y : Fin 4 → ℝ), F (t • y) = t ^ 3 * F y) (t p q : ℝ) :
    F (planeVec (t * p) (t * q)) = t ^ 3 * F (planeVec p q) := by
  have hscale : planeVec (t * p) (t * q) = t • planeVec p q := by
    ext i
    fin_cases i <;> simp [planeVec]
  rw [hscale, hF]

-- Theorem: a real root of the binary cubic on the isotropic plane gives a P-constructible
-- nonzero isotropic vector. The root `β` is P-constructible by
-- `cubicVal_root_Pconstructible`, and `(β, 1, β, 1)` is a nonzero point of the plane.
theorem exists_isotropic_vec_of_cubic_root {a b c d β : ℝ}
    (ha : PConstructible a) (hb : PConstructible b) (hc : PConstructible c)
    (hd : PConstructible d) (hne : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0)
    (hroot : cubicVal d c b a β = 0) :
    PConstructible β ∧
      (∀ i, PConstructible (planeVec β 1 i)) ∧
      planeVec β 1 ≠ 0 ∧
      form22 (planeVec β 1) = 0 ∧ bilin22 (planeVec β 1) (planeVec β 1) = 0 := by
  have hβP : PConstructible β := cubicVal_root_Pconstructible hd hc hb ha hne hroot
  refine ⟨hβP, ?_, ?_, form22_planeVec β 1, ?_⟩
  · intro i
    fin_cases i <;> simp [planeVec] <;> pconstructible
  · intro hv
    have h1 := congrFun hv 1
    simp [planeVec] at h1
  · rw [bilin22_self, form22_planeVec]

-- Theorem: as soon as the binary cubic has a real root, the form has a P-constructible
-- nonzero isotropic vector on its isotropic plane.
theorem exists_isotropic_vec_of_exists_root {a b c d : ℝ}
    (ha : PConstructible a) (hb : PConstructible b) (hc : PConstructible c)
    (hd : PConstructible d) (hne : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0)
    (hroot : ∃ β : ℝ, cubicVal d c b a β = 0) :
    ∃ v : Fin 4 → ℝ,
      (∀ i, PConstructible (v i)) ∧ v ≠ 0 ∧
        form22 v = 0 ∧ bilin22 v v = 0 := by
  obtain ⟨β, hβ⟩ := hroot
  obtain ⟨hβP, hvP, hvne, hv0, hvb⟩ :=
    exists_isotropic_vec_of_cubic_root ha hb hc hd hne hβ
  exact ⟨planeVec β 1, hvP, hvne, hv0, hvb⟩

end Pconstructible
