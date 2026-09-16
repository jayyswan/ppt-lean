/-
# Legendre relations and contiguous shifts for `₂F₁` at the elliptic parameters

This file collects the two ingredients the elliptic class `(1/2 + i, 1/2 + j, 1 + k)` of
`hyp` needs to be proved `PConstructible`:

* the *shift* relations that move one parameter of `hyp a b c` up or down at the cost of a
  factor of `z` and one derivative (DLMF 15.5.14 and 15.5.20), and
* the two *Legendre relations* expressing `deriv (hyp (1/2) (1/2) 1)` and
  `deriv (hyp (-1/2) (1/2) 1)` in terms of `hyp (1/2) (1/2) 1` and `hyp (-1/2) (1/2) 1`.

The Legendre relations are exactly the shift relations specialised to `(±1/2, 1/2, 1)`: with
`a = 1/2` the down-shift `hyp (a-1) b c` is `hyp (-1/2) (1/2) 1`, and with `a = -1/2` the
up-shift `hyp (a+1) b c` is `hyp (1/2) (1/2) 1`. Proving the general shift first is both
shorter and reusable; the coefficient identities that make the shifts true are
`a (a+1)ₙ = (a+n) (a)ₙ` (`mul_ascPochhammer_succ`, already in `Contiguous`).

Everything is proved by the `Contiguous` method: produce a `HasSum` for both sides and
compare coefficients, or combine two already-landed contiguous relations algebraically.
-/

import Pptc.Hypergeometric.Basic
import Pptc.Hypergeometric.Contiguous
import Pptc.Hypergeometric.Elliptic

open scoped Topology ENNReal

namespace Pconstructible

noncomputable section

/-! ### Shifting a numerator parameter up (DLMF 15.5.14)

The coefficient identity is `(a+1)ₙ = ((a+n)/a) (a)ₙ`, i.e. `a (a+1)ₙ = (a+n) (a)ₙ`. All the
other factors of `hypCoeff` — `(b)ₙ`, `(c)ₙ` and `n!` — are shared, so the relation is a pure
coefficient identity. The `z/a · d/dz` term is the power series `∑ₙ (n/a) cₙ zⁿ`, which is why
the coefficient at `zⁿ` is `(1 + n/a) cₙ = ((a+n)/a) cₙ`. -/

/-- `a · ₂F₁`-coefficient at `(a+1)` equals `(a+n)` times the coefficient at `a`:
`a * hypCoeff (a+1) b c n = (a+n) * hypCoeff a b c n`. -/
-- Theorem: `a * hypCoeff (a+1) b c n = (a + n) * hypCoeff a b c n`.
lemma mul_hypCoeff_succ_a (a b c : ℝ) (n : ℕ) :
    a * hypCoeff (a + 1) b c n = (a + n) * hypCoeff a b c n := by
  have h := mul_ascPochhammer_succ a n
  unfold hypCoeff ordinaryHypergeometricCoefficient
  linear_combination ((ascPochhammer ℝ n).eval b *
    ((ascPochhammer ℝ n).eval c * (n.factorial : ℝ))⁻¹) * h

/-- `b · ₂F₁`-coefficient at `(b+1)` equals `(b+n)` times the coefficient at `b`:
`b * hypCoeff a (b+1) c n = (b+n) * hypCoeff a b c n`. -/
-- Theorem: `b * hypCoeff a (b+1) c n = (b + n) * hypCoeff a b c n`.
lemma mul_hypCoeff_succ_b (a b c : ℝ) (n : ℕ) :
    b * hypCoeff a (b + 1) c n = (b + n) * hypCoeff a b c n := by
  have h := mul_ascPochhammer_succ b n
  unfold hypCoeff ordinaryHypergeometricCoefficient
  linear_combination ((ascPochhammer ℝ n).eval a *
    ((ascPochhammer ℝ n).eval c * (n.factorial : ℝ))⁻¹) * h

/-- **DLMF 15.5.14**: `₂F₁(a+1,b;c;z) = ₂F₁(a,b;c;z) + (z/a) ₂F₁′(a,b;c;z)` on `|z| < 1`,
for `a ≠ 0` and `c ∉ -ℕ`.

The `z ₂F₁′` term is `∑ₙ n cₙ zⁿ` (the `z` lowers the index by one), and the coefficient
identity `a (a+1)ₙ = (a+n) (a)ₙ` supplies `cₙ + (n/a) cₙ = ((a+n)/a) cₙ`, the coefficient of
`₂F₁(a+1,b;c;·)`. -/
-- Theorem: `hyp (a+1) b c z = hyp a b c z + (z/a) * deriv (hyp a b c) z`.
theorem hyp_shift_a {a b c z : ℝ} (ha : a ≠ 0) (hc : ∀ n : ℕ, c ≠ -(n : ℝ))
    (hz : |z| < 1) :
    hyp (a + 1) b c z = hyp a b c z + (z / a) * deriv (fun w => hyp a b c w) z := by
  have hF := hasSum_hyp (a := a) (b := b) (c := c) hz hc
  have hd := hasSum_deriv_hyp (a := a) (b := b) (c := c) hc hz
  have hR : HasSum (fun n : ℕ => a * (hypCoeff (a + 1) b c n * z ^ n))
      (a * hyp a b c z + deriv (fun w => hyp a b c w) z * z) :=
    ((hF.mul_left a).add (hasSum_mul_z_shift hd)).congr_fun fun n => by
      rcases n with _ | m
      · simp [hypCoeff, ordinaryHypergeometricCoefficient]
      · simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
        have h := mul_hypCoeff_succ_a a b c (m + 1)
        push_cast at h ⊢
        linear_combination (z ^ (m + 1)) * h
  have hL := (hasSum_hyp (a := a + 1) (b := b) (c := c) hz hc).mul_left a
  have key : a * hyp a b c z + deriv (fun w => hyp a b c w) z * z
      = a * hyp (a + 1) b c z := hR.unique hL
  have haz : a * (z / a) = z := by field_simp [ha]
  have hfin : a * (hyp a b c z + (z / a) * deriv (fun w => hyp a b c w) z)
      = a * hyp (a + 1) b c z := by
    rw [mul_add, ← mul_assoc, haz]
    linear_combination key
  exact (mul_left_cancel₀ ha hfin).symm

/-- **DLMF 15.5.14**, symmetric form: `₂F₁(a,b+1;c;z) = ₂F₁(a,b;c;z) + (z/b) ₂F₁′(a,b;c;z)`
on `|z| < 1`, for `b ≠ 0` and `c ∉ -ℕ`. -/
-- Theorem: `hyp a (b+1) c z = hyp a b c z + (z/b) * deriv (hyp a b c) z`.
theorem hyp_shift_b {a b c z : ℝ} (hb : b ≠ 0) (hc : ∀ n : ℕ, c ≠ -(n : ℝ))
    (hz : |z| < 1) :
    hyp a (b + 1) c z = hyp a b c z + (z / b) * deriv (fun w => hyp a b c w) z := by
  have hF := hasSum_hyp (a := a) (b := b) (c := c) hz hc
  have hd := hasSum_deriv_hyp (a := a) (b := b) (c := c) hc hz
  have hR : HasSum (fun n : ℕ => b * (hypCoeff a (b + 1) c n * z ^ n))
      (b * hyp a b c z + deriv (fun w => hyp a b c w) z * z) :=
    ((hF.mul_left b).add (hasSum_mul_z_shift hd)).congr_fun fun n => by
      rcases n with _ | m
      · simp [hypCoeff, ordinaryHypergeometricCoefficient]
      · simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
        have h := mul_hypCoeff_succ_b a b c (m + 1)
        push_cast at h ⊢
        linear_combination (z ^ (m + 1)) * h
  have hL := (hasSum_hyp (a := a) (b := b + 1) (c := c) hz hc).mul_left b
  have key : b * hyp a b c z + deriv (fun w => hyp a b c w) z * z
      = b * hyp a (b + 1) c z := hR.unique hL
  have hbz : b * (z / b) = z := by field_simp [hb]
  have hfin : b * (hyp a b c z + (z / b) * deriv (fun w => hyp a b c w) z)
      = b * hyp a (b + 1) c z := by
    rw [mul_add, ← mul_assoc, hbz]
    linear_combination key
  exact (mul_left_cancel₀ hb hfin).symm

/-! ### Shifting the denominator parameter up (DLMF 15.5.21)

The relation `c (1-z) ₂F₁′(a,b;c;z) = (c-a)(c-b) ₂F₁(a,b;c+1;z) + c(a+b-c) ₂F₁(a,b;c;z)`
already landed in `Contiguous` is exactly this shift after solving for `₂F₁(a,b;c+1;z)`. -/

/-- **DLMF 15.5.21** solved for `₂F₁(a,b;c+1;z)`: on `|z| < 1`, for `c ∉ -ℕ`,
`c+1 ∉ -ℕ` and `(c-a)(c-b) ≠ 0`,
`₂F₁(a,b;c+1;z) = (c(1-z) ₂F₁′(a,b;c;z) - c(a+b-c) ₂F₁(a,b;c;z)) / ((c-a)(c-b))`. -/
-- Theorem: `hyp a b (c+1) z = (c*(1-z)*deriv (hyp a b c) z - c*(a+b-c)*hyp a b c z)
--   / ((c-a)*(c-b))`.
theorem hyp_shift_c_up {a b c z : ℝ} (hc : ∀ n : ℕ, c ≠ -(n : ℝ))
    (hc1 : ∀ n : ℕ, c + 1 ≠ -(n : ℝ)) (hca : c - a ≠ 0) (hcb : c - b ≠ 0)
    (hz : |z| < 1) :
    hyp a b (c + 1) z = (c * (1 - z) * deriv (fun w => hyp a b c w) z
      - c * (a + b - c) * hyp a b c z) / ((c - a) * (c - b)) := by
  rw [eq_div_iff (mul_ne_zero hca hcb)]
  have h21 := hyp_contiguous_21 (a := a) (b := b) (c := c) hc hc1 hz
  linear_combination (-1 : ℝ) * h21

/-! ### Shifting a numerator parameter down (DLMF 15.5.20a)

`(c-a) ₂F₁(a-1,b;c;z) = z(1-z) ₂F₁′(a,b;c;z) - (a - c + bz) ₂F₁(a,b;c;z)`.

This is DLMF 15.5.13 with `a` and `b` interchanged, `₂F₁(a,b+1;c;z)` then eliminated with the
up-shift `hyp_shift_b`. Writing `F = ₂F₁(a,b;c;·)`, `F' = dF/dz`, `G = ₂F₁(a-1,b;c;·)`, the
interchanged 15.5.13 reads `(c-a-b)F + (1-z)(bF + zF') = (c-a)G`, whose both sides rearrange to
`(c-a)G = (c-a-bz)F + z(1-z)F'`; that is the stated relation after `(c-a-bz) = -(a-c+bz)`. -/

/-- **DLMF 15.5.20a**: on `|z| < 1`, for `b ≠ 0`, `c ∉ -ℕ` and `c ≠ a`,
`₂F₁(a-1,b;c;z) = (z(1-z) ₂F₁′(a,b;c;z) - (a-c+bz) ₂F₁(a,b;c;z)) / (c-a)`. -/
-- Theorem: `hyp (a-1) b c z = (z*(1-z)*deriv (hyp a b c) z - (a-c+b*z)*hyp a b c z)/(c-a)`.
theorem hyp_shift_a_down {a b c z : ℝ} (hb : b ≠ 0) (hca : c - a ≠ 0)
    (hc : ∀ n : ℕ, c ≠ -(n : ℝ)) (hz : |z| < 1) :
    hyp (a - 1) b c z = (z * (1 - z) * deriv (fun w => hyp a b c w) z
      - (a - c + b * z) * hyp a b c z) / (c - a) := by
  have hbz : b * (z / b) = z := by field_simp [hb]
  have hsb' : b * hyp a (b + 1) c z
      = b * hyp a b c z + z * deriv (fun w => hyp a b c w) z := by
    rw [hyp_shift_b (a := a) (b := b) (c := c) hb hc hz, mul_add, ← mul_assoc, hbz]
  have h13 := hyp_contiguous_13 (a := b) (b := a) (c := c) hc hz
  rw [hyp_comm b a c z, hyp_comm (b + 1) a c z, hyp_comm b (a - 1) c z] at h13
  have h13' : (c - b - a) * hyp a b c z + (1 - z) * (b * hyp a (b + 1) c z)
      - (c - a) * hyp (a - 1) b c z = 0 := by
    linear_combination h13
  rw [hsb'] at h13'
  rw [eq_div_iff hca]
  linear_combination (-1 : ℝ) * h13'

/-! ### The three-term recurrences in the numerator parameters

Eliminating `₂F₁′` between the up-shift (`hyp_shift_a`) and the down-shift
(`hyp_shift_a_down`) gives a second-order recurrence for the sequence `a ↦ ₂F₁(a,b;c;z)` over
`ℚ(b,c,z)`:

`(a-1)(1-z) F(a) = (c-a+1) F(a-2) + (2(a-1) - c + z(b-a+1)) F(a-1)`.

It is what makes the class theorem derivative-free in the `a` and `b` directions: two
consecutive values determine the whole sequence. -/

-- Theorem: the three-term recurrence in `a`.
-- Derived by eliminating `₂F₁′` between `hyp_shift_a` at `a-1` and `hyp_shift_a_down` at `a-1`.
theorem hyp_three_term_a {a b c z : ℝ} (ha1 : a ≠ 1) (hb : b ≠ 0)
    (hca : c - a + 1 ≠ 0) (hc : ∀ n : ℕ, c ≠ -(n : ℝ)) (hz : |z| < 1) (hz1 : z ≠ 1) :
    (a - 1) * (1 - z) * hyp a b c z
      = (c - a + 1) * hyp (a - 2) b c z
        + (2 * (a - 1) - c + z * (b - a + 1)) * hyp (a - 1) b c z := by
  have hane : a - 1 ≠ 0 := sub_ne_zero.mpr ha1
  have hca' : c - (a - 1) ≠ 0 := by
    rw [show c - (a - 1) = c - a + 1 by ring]; exact hca
  have h1z : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)
  have h1 := hyp_shift_a (a := a - 1) (b := b) (c := c) hane hc hz
  rw [show a - 1 + 1 = a by ring] at h1
  have h2 := hyp_shift_a_down (a := a - 1) (b := b) (c := c) hb hca' hc hz
  rw [show a - 1 - 1 = a - 2 by ring, show c - (a - 1) = c - a + 1 by ring] at h2
  rw [h2, mul_div_cancel₀ _ hca, h1]
  field_simp
  ring

-- Theorem: the three-term recurrence in `b` (the symmetric form).
theorem hyp_three_term_b {a b c z : ℝ} (hb1 : b ≠ 1) (ha : a ≠ 0)
    (hcb : c - b + 1 ≠ 0) (hc : ∀ n : ℕ, c ≠ -(n : ℝ)) (hz : |z| < 1) (hz1 : z ≠ 1) :
    (b - 1) * (1 - z) * hyp a b c z
      = (c - b + 1) * hyp a (b - 2) c z
        + (2 * (b - 1) - c + z * (a - b + 1)) * hyp a (b - 1) c z := by
  rw [hyp_comm a b c z, hyp_comm a (b - 2) c z, hyp_comm a (b - 1) c z]
  exact hyp_three_term_a (a := b) (b := a) hb1 ha hcb hc hz hz1

/-! ### The Legendre relations for `₂F₁(1/2,1/2;1)` and `₂F₁(-1/2,1/2;1)`

Both are immediate specialisations of the general shifts above, which is why they are proved
here rather than by a separate coefficient identity:

* at `(a,b,c) = (1/2,1/2,1)`, `hyp_shift_a_down` says
  `₂F₁(-1/2,1/2;1;z) = z(1-z)F' + (1-z)F`, i.e. `2z(1-z)F' = ₂F₁(-1/2,1/2;1;z) - (1-z)F`;
* at `(a,b,c) = (-1/2,1/2,1)`, `hyp_shift_a` says
  `₂F₁(1/2,1/2;1;z) = ₂F₁(-1/2,1/2;1;z) - 2z (₂F₁(-1/2,1/2;1;·))'(z)`.

The `z ≠ 0`, `z ≠ 1` conditions appear only in the `PConstructible` corollaries, where the
relation is solved for the derivative. -/

-- Theorem: `2z(1-z) * deriv (hyp (1/2)(1/2)1) z
--   = hyp (-1/2)(1/2)1 z - (1-z) * hyp (1/2)(1/2)1 z` for `|z| < 1`.
theorem hyp_deriv_half_half_one {z : ℝ} (hz : |z| < 1) :
    2 * z * (1 - z) * deriv (fun w => hyp (1 / 2) (1 / 2) 1 w) z
      = hyp (-1 / 2) (1 / 2) 1 z - (1 - z) * hyp (1 / 2) (1 / 2) 1 z := by
  have hc : ∀ n : ℕ, (1 : ℝ) ≠ -(n : ℝ) := fun n => by
    have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have h := hyp_shift_a_down (a := 1 / 2) (b := 1 / 2) (c := 1)
    (by norm_num) (by norm_num) hc hz
  norm_num at h
  rw [show (-(1 / 2) : ℝ) = -1 / 2 by norm_num] at h
  rw [h]
  ring

-- Theorem: `2z * deriv (hyp (-1/2)(1/2)1) z = hyp (-1/2)(1/2)1 z - hyp (1/2)(1/2)1 z`
--   for `|z| < 1`.
theorem hyp_deriv_neg_half_half_one {z : ℝ} (hz : |z| < 1) :
    2 * z * deriv (fun w => hyp (-1 / 2) (1 / 2) 1 w) z
      = hyp (-1 / 2) (1 / 2) 1 z - hyp (1 / 2) (1 / 2) 1 z := by
  have hc : ∀ n : ℕ, (1 : ℝ) ≠ -(n : ℝ) := fun n => by
    have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have h := hyp_shift_a (a := -1 / 2) (b := 1 / 2) (c := 1) (by norm_num) hc hz
  norm_num at h
  rw [show (-(1 / 2) : ℝ) = -1 / 2 by norm_num] at h
  rw [h]
  ring

/-! ### PConstructible corollaries

Solving each Legendre relation for the derivative needs exactly `z ≠ 0` and `z ≠ 1` (the two
zeros of the prefactor `2z(1-z)`), after which `PConstructible` is pure closure from
`hyp_half_half_one_Pconstructible` and `hyp_neg_half_half_one_Pconstructible`. -/

-- Theorem: `deriv (hyp (1/2)(1/2)1)` is P-constructible for P-constructible `z ∉ {0,1}`,
-- `|z| < 1`.
@[pconstructible_cond]
theorem deriv_half_half_one_Pconstructible {z : ℝ} (hzP : PConstructible z) (hz0 : z ≠ 0)
    (hz1 : z ≠ 1) (hzabs : |z| < 1) :
    PConstructible (deriv (fun w => hyp (1 / 2) (1 / 2) 1 w) z) := by
  have hden : 2 * z * (1 - z) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (by norm_num) hz0) ?_
    exact sub_ne_zero.mpr (Ne.symm hz1)
  have hmain := hyp_deriv_half_half_one hzabs
  have hD : deriv (fun w => hyp (1 / 2) (1 / 2) 1 w) z
      = (hyp (-1 / 2) (1 / 2) 1 z - (1 - z) * hyp (1 / 2) (1 / 2) 1 z)
        / (2 * z * (1 - z)) := by
    rw [eq_div_iff hden]
    linear_combination hmain
  rw [hD]
  exact PConstructible.div
    (PConstructible.sub (hyp_neg_half_half_one_Pconstructible hzP hzabs)
      (PConstructible.mul (PConstructible.sub PConstructible.base_one hzP)
        (hyp_half_half_one_Pconstructible hzP hzabs)))
    (PConstructible.mul (PConstructible.mul two_Pconstructible hzP)
      (PConstructible.sub PConstructible.base_one hzP))

-- Theorem: `deriv (hyp (-1/2)(1/2)1)` is P-constructible for P-constructible `z ≠ 0`,
-- `|z| < 1`.
@[pconstructible_cond]
theorem deriv_neg_half_half_one_Pconstructible {z : ℝ} (hzP : PConstructible z) (hz0 : z ≠ 0)
    (hzabs : |z| < 1) :
    PConstructible (deriv (fun w => hyp (-1 / 2) (1 / 2) 1 w) z) := by
  have hden : 2 * z ≠ 0 := mul_ne_zero (by norm_num) hz0
  have hmain := hyp_deriv_neg_half_half_one hzabs
  have hD : deriv (fun w => hyp (-1 / 2) (1 / 2) 1 w) z
      = (hyp (-1 / 2) (1 / 2) 1 z - hyp (1 / 2) (1 / 2) 1 z) / (2 * z) := by
    rw [eq_div_iff hden]
    linear_combination hmain
  rw [hD]
  exact PConstructible.div
    (PConstructible.sub (hyp_neg_half_half_one_Pconstructible hzP hzabs)
      (hyp_half_half_one_Pconstructible hzP hzabs))
    (PConstructible.mul two_Pconstructible hzP)

/-! ### The elliptic class `(1/2 + i, 1/2 + j, 1)` for all `i, j : ℤ`

The values `₂F₁(±1/2, ±1/2; 1; z)` and the two derivatives reached above are the whole
`|i|, |j| ≤ 1` corner of the lattice. The rest is reached by the three-term recurrences
`hyp_three_term_a` / `hyp_three_term_b`, which express `hyp a b 1 z` through
`hyp (a-1) b 1 z` and `hyp (a-2) b 1 z` and are derivative-free: strong induction on
`Int.natAbs i + Int.natAbs j` propagates them over the whole lattice once the nine corner
pairs are known. The `b`-direction uses the same recurrence through `hyp_comm`. -/

-- Theorem: `₂F₁(1/2 + i, 1/2 + j; 1; z)` is P-constructible for P-constructible `z`
-- with `z ∉ {0, 1}` and `|z| < 1`, for every pair of integers `i, j`.
theorem hyp_elliptic_class_level_zero_Pconstructible {i j : ℤ} {z : ℝ}
    (hz : PConstructible z) (hz0 : z ≠ 0) (hz1 : z ≠ 1) (hzabs : |z| < 1) :
    PConstructible (hyp (1 / 2 + i) (1 / 2 + j) 1 z) := by
  have hc : ∀ n : ℕ, (1 : ℝ) ≠ -(n : ℝ) := fun n => by
    have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  let P : ℤ → ℤ → Prop := fun i j =>
    PConstructible (hyp ((1 : ℝ) / 2 + (i : ℝ)) ((1 : ℝ) / 2 + (j : ℝ)) 1 z)
  -- the corner values
  have hK : PConstructible (hyp (1 / 2 : ℝ) (1 / 2 : ℝ) 1 z) :=
    hyp_half_half_one_Pconstructible hz hzabs
  have hE : PConstructible (hyp (-(1 / 2) : ℝ) (1 / 2 : ℝ) 1 z) := by
    have h := hyp_neg_half_half_one_Pconstructible hz hzabs
    convert h; norm_num
  have hE0 : PConstructible (hyp (1 / 2 : ℝ) (-(1 / 2) : ℝ) 1 z) := by
    rw [hyp_comm (1 / 2 : ℝ) (-(1 / 2) : ℝ) 1 z]
    exact hE
  have hK' : PConstructible (deriv (fun w => hyp (1 / 2 : ℝ) (1 / 2 : ℝ) 1 w) z) :=
    deriv_half_half_one_Pconstructible hz hz0 hz1 hzabs
  have hE' : PConstructible (deriv (fun w => hyp (-(1 / 2) : ℝ) (1 / 2 : ℝ) 1 w) z) := by
    have hfun : (fun w => hyp (-(1 / 2) : ℝ) (1 / 2 : ℝ) 1 w)
        = (fun w => hyp (-1 / 2 : ℝ) (1 / 2 : ℝ) 1 w) := by
      funext w; norm_num
    rw [hfun]; exact deriv_neg_half_half_one_Pconstructible hz hz0 hzabs
  have hE0' : PConstructible (deriv (fun w => hyp (1 / 2 : ℝ) (-(1 / 2) : ℝ) 1 w) z) := by
    have hfun : (fun w => hyp (1 / 2 : ℝ) (-(1 / 2) : ℝ) 1 w)
        = (fun w => hyp (-(1 / 2) : ℝ) (1 / 2 : ℝ) 1 w) := by
      funext w; exact hyp_comm (1 / 2 : ℝ) (-(1 / 2) : ℝ) 1 w
    rw [hfun]; exact hE'
  have hA : PConstructible (hyp (3 / 2 : ℝ) (1 / 2 : ℝ) 1 z) := by
    have h2 : PConstructible (hyp ((1 / 2 : ℝ) + 1) (1 / 2 : ℝ) 1 z) := by
      rw [hyp_shift_a (a := 1 / 2) (b := 1 / 2) (c := 1) (by norm_num) hc hzabs]
      pconstructible
    convert h2 using 2; norm_num
  have hB : PConstructible (hyp (3 / 2 : ℝ) (-(1 / 2) : ℝ) 1 z) := by
    have h2 : PConstructible (hyp ((1 / 2 : ℝ) + 1) (-(1 / 2) : ℝ) 1 z) := by
      rw [hyp_shift_a (a := 1 / 2) (b := -(1 / 2)) (c := 1) (by norm_num) hc hzabs]
      pconstructible
    convert h2 using 2; norm_num
  have hC : PConstructible (hyp (-(1 / 2) : ℝ) (-(1 / 2) : ℝ) 1 z) := by
    have h2 : PConstructible (hyp ((1 / 2 : ℝ) - 1) (-(1 / 2) : ℝ) 1 z) := by
      rw [hyp_shift_a_down (a := 1 / 2) (b := -(1 / 2)) (c := 1) (by norm_num)
        (by norm_num) hc hzabs]
      pconstructible
    convert h2 using 2; norm_num
  have h11 : PConstructible (hyp (3 / 2 : ℝ) (3 / 2 : ℝ) 1 z) := by
    have hden : ((1 / 2 : ℝ) * (1 - z)) ≠ 0 :=
      mul_ne_zero (by norm_num) (sub_ne_zero.mpr (Ne.symm hz1))
    have hrec := hyp_three_term_b (a := (3 / 2 : ℝ)) (b := (3 / 2 : ℝ)) (c := 1)
      (by norm_num) (by norm_num) (by norm_num) hc hzabs hz1
    norm_num at hrec
    have heq : hyp (3 / 2 : ℝ) (3 / 2 : ℝ) 1 z
        = ((1 / 2 : ℝ) * hyp (3 / 2 : ℝ) (-(1 / 2) : ℝ) 1 z
            + z * hyp (3 / 2 : ℝ) (1 / 2 : ℝ) 1 z) / ((1 / 2 : ℝ) * (1 - z)) := by
      rw [eq_div_iff hden]
      linear_combination hrec
    rw [heq]
    pconstructible
  have hA' : PConstructible (hyp (1 / 2 : ℝ) (3 / 2 : ℝ) 1 z) := by
    rw [hyp_comm (1 / 2 : ℝ) (3 / 2 : ℝ) 1 z]
    exact hA
  have hB' : PConstructible (hyp (-(1 / 2) : ℝ) (3 / 2 : ℝ) 1 z) := by
    rw [hyp_comm (-(1 / 2) : ℝ) (3 / 2 : ℝ) 1 z]
    exact hB
  have hmain : ∀ n, (∀ m < n, ∀ i j : ℤ, Int.natAbs i + Int.natAbs j = m → P i j) →
      ∀ i j : ℤ, Int.natAbs i + Int.natAbs j = n → P i j := by
    intro n ih i j hij
    change PConstructible (hyp ((1 : ℝ) / 2 + (i : ℝ)) ((1 : ℝ) / 2 + (j : ℝ)) 1 z)
    have hrec0 : ∀ a b : ℤ, Int.natAbs a + Int.natAbs b < n → P a b :=
      fun a b h => ih _ h a b rfl
    have hstep : ∀ (i' j' : ℤ), 2 ≤ Int.natAbs i' →
        Int.natAbs i' + Int.natAbs j' ≤ n →
        (∀ (a b : ℤ), Int.natAbs a + Int.natAbs b < n → P a b) → P i' j' := by
      intro i' j' hi2 hbound hrec0'
      change PConstructible (hyp ((1 : ℝ) / 2 + (i' : ℝ)) ((1 : ℝ) / 2 + (j' : ℝ)) 1 z)
      rcases (by omega : 2 ≤ i' ∨ i' ≤ -2) with hi_ge | hi_le
      · -- raise `i'`
        have ha1 : ((1 : ℝ) / 2 + (i' : ℝ)) ≠ 1 := by
          have h2 : (2 : ℝ) ≤ (i' : ℝ) := by exact_mod_cast hi_ge
          intro h; linarith
        have hb : ((1 : ℝ) / 2 + (j' : ℝ)) ≠ 0 := by
          intro h
          have h2 : ((2 * j' + 1 : ℤ) : ℝ) = 0 := by push_cast; linarith
          have h3 : (2 * j' + 1 : ℤ) = 0 := by exact_mod_cast h2
          omega
        have hca : 1 - ((1 : ℝ) / 2 + (i' : ℝ)) + 1 ≠ 0 := by
          intro h
          have h2 : ((2 * i' - 3 : ℤ) : ℝ) = 0 := by push_cast; linarith
          have h3 : (2 * i' - 3 : ℤ) = 0 := by exact_mod_cast h2
          omega
        have hsub : ((1 : ℝ) / 2 + (i' : ℝ)) - 1 ≠ 0 := by
          intro h
          have h2 : ((2 * i' - 1 : ℤ) : ℝ) = 0 := by push_cast; linarith
          have h3 : (2 * i' - 1 : ℤ) = 0 := by exact_mod_cast h2
          omega
        have hden : (((1 : ℝ) / 2 + (i' : ℝ)) - 1) * (1 - z) ≠ 0 :=
          mul_ne_zero hsub (sub_ne_zero.mpr (Ne.symm hz1))
        have hrec := hyp_three_term_a (a := (1 : ℝ) / 2 + (i' : ℝ))
          (b := (1 : ℝ) / 2 + (j' : ℝ)) (c := 1) ha1 hb hca hc hzabs hz1
        have heq : hyp ((1 : ℝ) / 2 + (i' : ℝ)) ((1 : ℝ) / 2 + (j' : ℝ)) 1 z =
            ((1 - ((1 : ℝ) / 2 + (i' : ℝ)) + 1)
                * hyp (((1 : ℝ) / 2 + (i' : ℝ)) - 2) ((1 : ℝ) / 2 + (j' : ℝ)) 1 z
             + (2 * (((1 : ℝ) / 2 + (i' : ℝ)) - 1) - 1
                + z * (((1 : ℝ) / 2 + (j' : ℝ)) - ((1 : ℝ) / 2 + (i' : ℝ)) + 1))
               * hyp (((1 : ℝ) / 2 + (i' : ℝ)) - 1) ((1 : ℝ) / 2 + (j' : ℝ)) 1 z)
             / ((((1 : ℝ) / 2 + (i' : ℝ)) - 1) * (1 - z)) := by
          rw [eq_div_iff hden]
          linear_combination hrec
        have hlt1 : Int.natAbs (i' - 1) < Int.natAbs i' :=
          Int.natAbs_lt_natAbs_of_nonneg_of_lt (by omega) (by omega)
        have hlt2 : Int.natAbs (i' - 2) < Int.natAbs i' :=
          Int.natAbs_lt_natAbs_of_nonneg_of_lt (by omega) (by omega)
        have hb1 : Int.natAbs (i' - 1) + Int.natAbs j' < n :=
          Nat.lt_of_lt_of_le (Nat.add_lt_add_right hlt1 (Int.natAbs j')) hbound
        have hb2 : Int.natAbs (i' - 2) + Int.natAbs j' < n :=
          Nat.lt_of_lt_of_le (Nat.add_lt_add_right hlt2 (Int.natAbs j')) hbound
        have hP1 : PConstructible
            (hyp (((1 : ℝ) / 2 + (i' : ℝ)) - 1) ((1 : ℝ) / 2 + (j' : ℝ)) 1 z) := by
          rw [← show (1 : ℝ) / 2 + ((i' - 1 : ℤ) : ℝ) = ((1 : ℝ) / 2 + (i' : ℝ)) - 1 by
            push_cast; ring]
          exact hrec0' (i' - 1) j' hb1
        have hP2 : PConstructible
            (hyp (((1 : ℝ) / 2 + (i' : ℝ)) - 2) ((1 : ℝ) / 2 + (j' : ℝ)) 1 z) := by
          rw [← show (1 : ℝ) / 2 + ((i' - 2 : ℤ) : ℝ) = ((1 : ℝ) / 2 + (i' : ℝ)) - 2 by
            push_cast; ring]
          exact hrec0' (i' - 2) j' hb2
        have hiP : PConstructible (i' : ℝ) := int_Pconstructible i'
        have hjP : PConstructible (j' : ℝ) := int_Pconstructible j'
        rw [heq]
        pconstructible
      · -- lower `i'`
        have ha1 : ((1 : ℝ) / 2 + (i' : ℝ) + 2) ≠ 1 := by
          have h2 : (i' : ℝ) ≤ -2 := by exact_mod_cast hi_le
          intro h; linarith
        have hb : ((1 : ℝ) / 2 + (j' : ℝ)) ≠ 0 := by
          intro h
          have h2 : ((2 * j' + 1 : ℤ) : ℝ) = 0 := by push_cast; linarith
          have h3 : (2 * j' + 1 : ℤ) = 0 := by exact_mod_cast h2
          omega
        have hca : 1 - ((1 : ℝ) / 2 + (i' : ℝ) + 2) + 1 ≠ 0 := by
          intro h
          have h2 : ((2 * i' + 1 : ℤ) : ℝ) = 0 := by push_cast; linarith
          have h3 : (2 * i' + 1 : ℤ) = 0 := by exact_mod_cast h2
          omega
        have hrec := hyp_three_term_a (a := (1 : ℝ) / 2 + (i' : ℝ) + 2)
          (b := (1 : ℝ) / 2 + (j' : ℝ)) (c := 1) ha1 hb hca hc hzabs hz1
        rw [show (1 : ℝ) / 2 + (i' : ℝ) + 2 - 2 = (1 : ℝ) / 2 + (i' : ℝ) by ring,
            show (1 : ℝ) / 2 + (i' : ℝ) + 2 - 1 = ((1 : ℝ) / 2 + (i' : ℝ)) + 1 by
              ring] at hrec
        have heq : hyp ((1 : ℝ) / 2 + (i' : ℝ)) ((1 : ℝ) / 2 + (j' : ℝ)) 1 z =
            ((((1 : ℝ) / 2 + (i' : ℝ)) + 1) * (1 - z)
                * hyp (((1 : ℝ) / 2 + (i' : ℝ)) + 2) ((1 : ℝ) / 2 + (j' : ℝ)) 1 z
             - (2 * (((1 : ℝ) / 2 + (i' : ℝ)) + 1) - 1
                + z * (((1 : ℝ) / 2 + (j' : ℝ)) - (((1 : ℝ) / 2 + (i' : ℝ)) + 2) + 1))
               * hyp (((1 : ℝ) / 2 + (i' : ℝ)) + 1) ((1 : ℝ) / 2 + (j' : ℝ)) 1 z)
             / (1 - (((1 : ℝ) / 2 + (i' : ℝ)) + 2) + 1) := by
          rw [eq_div_iff hca]
          linear_combination (-1 : ℝ) * hrec
        have hlt1 : Int.natAbs (i' + 1) < Int.natAbs i' := by
          rw [← Int.natAbs_neg (i' + 1), ← Int.natAbs_neg i']
          exact Int.natAbs_lt_natAbs_of_nonneg_of_lt (by omega) (by omega)
        have hlt2 : Int.natAbs (i' + 2) < Int.natAbs i' := by
          rw [← Int.natAbs_neg (i' + 2), ← Int.natAbs_neg i']
          exact Int.natAbs_lt_natAbs_of_nonneg_of_lt (by omega) (by omega)
        have hb1 : Int.natAbs (i' + 1) + Int.natAbs j' < n :=
          Nat.lt_of_lt_of_le (Nat.add_lt_add_right hlt1 (Int.natAbs j')) hbound
        have hb2 : Int.natAbs (i' + 2) + Int.natAbs j' < n :=
          Nat.lt_of_lt_of_le (Nat.add_lt_add_right hlt2 (Int.natAbs j')) hbound
        have hP1 : PConstructible
            (hyp (((1 : ℝ) / 2 + (i' : ℝ)) + 1) ((1 : ℝ) / 2 + (j' : ℝ)) 1 z) := by
          rw [← show (1 : ℝ) / 2 + ((i' + 1 : ℤ) : ℝ) = ((1 : ℝ) / 2 + (i' : ℝ)) + 1 by
            push_cast; ring]
          exact hrec0' (i' + 1) j' hb1
        have hP2 : PConstructible
            (hyp (((1 : ℝ) / 2 + (i' : ℝ)) + 2) ((1 : ℝ) / 2 + (j' : ℝ)) 1 z) := by
          rw [← show (1 : ℝ) / 2 + ((i' + 2 : ℤ) : ℝ) = ((1 : ℝ) / 2 + (i' : ℝ)) + 2 by
            push_cast; ring]
          exact hrec0' (i' + 2) j' hb2
        have hiP : PConstructible (i' : ℝ) := int_Pconstructible i'
        have hjP : PConstructible (j' : ℝ) := int_Pconstructible j'
        rw [heq]
        pconstructible
    by_cases hi2 : 2 ≤ Int.natAbs i
    · exact hstep i j hi2 (le_of_eq hij) hrec0
    · by_cases hj2 : 2 ≤ Int.natAbs j
      · have hbound' : Int.natAbs j + Int.natAbs i ≤ n := by
          rw [Nat.add_comm (Int.natAbs j) (Int.natAbs i), hij]
        have hji : P j i := hstep j i hj2 hbound' hrec0
        rw [hyp_comm ((1 : ℝ) / 2 + (i : ℝ)) ((1 : ℝ) / 2 + (j : ℝ)) 1 z]
        exact hji
      · have hi1 : -1 ≤ i := by omega
        have hi1' : i ≤ 1 := by omega
        have hj1 : -1 ≤ j := by omega
        have hj1' : j ≤ 1 := by omega
        interval_cases i <;> interval_cases j
        · convert hC using 2 <;> norm_num
        · convert hE using 2 <;> norm_num
        · convert hB' using 2 <;> norm_num
        · convert hE0 using 2 <;> norm_num
        · convert hK using 2 <;> norm_num
        · convert hA' using 2 <;> norm_num
        · convert hB using 2 <;> norm_num
        · convert hA using 2 <;> norm_num
        · convert h11 using 2 <;> norm_num
  exact Nat.strongRecOn
    (motive := fun n => ∀ i j : ℤ, Int.natAbs i + Int.natAbs j = n → P i j)
    (Int.natAbs i + Int.natAbs j) hmain i j rfl

/-! ### Advancing the denominator `c = 1 + k`

With the whole level `c = 1 + k` P-constructible, `hyp_shift_c_up` moves one step up. Its
right-hand side needs `₂F₁′(a,b;c;z)`, and `hyp_shift_a_down` expresses that derivative at the
*same* level as `((c-a) ₂F₁(a-1,b;c;z) + (a-c+bz) ₂F₁(a,b;c;z))/(z(1-z))`. So the step only
consumes the two level-`c` values `a-1` and `a`, and induction on `k` closes the class. -/

-- Theorem (L3b): `₂F₁(1/2+i, 1/2+j; 1+k; z)` is P-constructible for P-constructible `z`
-- with `z ∉ {0, 1}`, `|z| < 1`, and all `i, j : ℤ`, `k : ℕ`.
theorem hyp_elliptic_class_Pconstructible {i j : ℤ} {k : ℕ} {z : ℝ}
    (hz : PConstructible z) (hz0 : z ≠ 0) (hz1 : z ≠ 1) (hzabs : |z| < 1) :
    PConstructible (hyp (1 / 2 + i) (1 / 2 + j) (1 + k) z) := by
  have hode : ∀ m : ℤ, (1 / 2 + (m : ℝ)) ≠ 0 := fun m hm => by
    have h2 : (2 : ℝ) * (1 / 2 + (m : ℝ)) = 0 := by rw [hm]; ring
    have h3 : ((2 * m + 1 : ℤ) : ℝ) = 0 := by push_cast; linarith
    have h4 : (2 * m + 1 : ℤ) = 0 := by exact_mod_cast h3
    omega
  have hz1' : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)
  have hmain : ∀ k : ℕ, ∀ i j : ℤ, PConstructible (hyp (1 / 2 + i) (1 / 2 + j) (1 + k) z) := by
    intro k
    induction k with
    | zero =>
      intro i j
      simpa using hyp_elliptic_class_level_zero_Pconstructible (z := z) hz hz0 hz1 hzabs
        (i := i) (j := j)
    | succ k ih =>
      intro i j
      set a : ℝ := 1 / 2 + (i : ℝ) with ha
      set b : ℝ := 1 / 2 + (j : ℝ) with hb
      set c : ℝ := 1 + (k : ℝ) with hcdef
      have hbne : b ≠ 0 := by rw [hb]; exact hode j
      have hcane : c - a ≠ 0 := by
        have hEq : c - a = 1 / 2 + ((k - i : ℤ) : ℝ) := by
          simp only [hcdef, ha]; push_cast; ring
        rw [hEq]; exact hode (k - i)
      have hcbne : c - b ≠ 0 := by
        have hEq : c - b = 1 / 2 + ((k - j : ℤ) : ℝ) := by
          simp only [hcdef, hb]; push_cast; ring
        rw [hEq]; exact hode (k - j)
      have hcne : ∀ n : ℕ, c ≠ -(n : ℝ) := by
        intro n hn
        have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        have hcpos : 0 < c := by simp only [hcdef]; positivity
        linarith
      have hc1ne : ∀ n : ℕ, c + 1 ≠ -(n : ℝ) := by
        intro n hn
        have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        have hcpos : 0 < c := by simp only [hcdef]; positivity
        linarith
      have hshift := hyp_shift_c_up (a := a) (b := b) (c := c) hcne hc1ne hcane hcbne hzabs
      have hF' : deriv (fun w => hyp a b c w) z
          = ((c - a) * hyp (a - 1) b c z + (a - c + b * z) * hyp a b c z)
            / (z * (1 - z)) := by
        rw [eq_div_iff (mul_ne_zero hz0 hz1')]
        have h := hyp_shift_a_down (a := a) (b := b) (c := c) hbne hcane hcne hzabs
        rw [h, mul_div_cancel₀ _ hcane]
        ring
      have h1 : PConstructible (hyp (a - 1) b c z) := by
        have harg1 : a - 1 = 1 / 2 + ((i - 1 : ℤ) : ℝ) := by rw [ha]; push_cast; ring
        rw [harg1, hb]
        exact ih (i - 1) j
      have h0 : PConstructible (hyp a b c z) := by
        rw [ha, hb]
        exact ih i j
      have hiP : PConstructible (i : ℝ) := int_Pconstructible i
      have hjP : PConstructible (j : ℝ) := int_Pconstructible j
      have hkP : PConstructible (k : ℝ) := nat_Pconstructible k
      have haP : PConstructible a := by rw [ha]; pconstructible
      have hbP : PConstructible b := by rw [hb]; pconstructible
      have hcP : PConstructible c := by rw [hcdef]; pconstructible
      rw [show (1 + ((k + 1 : ℕ) : ℝ)) = c + 1 by
        simp only [hcdef]; push_cast; ring]
      rw [hshift, hF']
      pconstructible
  exact hmain k i j

end

end Pconstructible
