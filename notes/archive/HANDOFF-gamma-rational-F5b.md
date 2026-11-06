# HANDOFF: GammaRational Doubling (F5b)

Goal: fill proof of
```lean
theorem Gamma_rat_Pconstructible_of_dup
    (hdup : ∀ x : ℚ, 0 < x → PConstructible (Real.Gamma (x : ℝ) ^ 2 / Real.Gamma (2 * (x : ℝ))))
    (q : ℚ) : PConstructible (Real.Gamma (q : ℝ))
```
File: pptc/Pptc/GammaRational/Doubling.lean (absolute C:\dev\Powerpoint\lean\pptc\Pptc\GammaRational\Doubling.lean)
Namespace: Pconstructible. Imports Pptc.GammaFunctional (built).

Plan:
3. Gamma_pow_two_pow_div_Pconstructible (k): Γ(x)^(2^k)/Γ(2^k x) ∈ P by induction.
4. Gamma_odd_den_Pconstructible: odd den N, ℓ=φ(N), N|2^ℓ-1, x+m shift.
5. general q>0 by 2-adic induction, sqrt.
6. q≤0 shift by integer.

## Log
- [start] created log.
- [step] wrote first draft: 5 helpers (Gamma_add_nat_eq_Gamma_mul_prod, pochhammer_Pconstructible, Gamma_pow_two_pow_div_Pconstructible, Gamma_nat_div_odd_Pconstructible, Gamma_nat_div_two_pow_mul_Pconstructible, Gamma_rat_pos_Pconstructible) + main theorem. Now checking diagnostics.
- [names confirmed] Real.Gamma_pos_of_pos, Real.Gamma_add_one (s≠0), Real.Gamma_zero, Real.sqrt_sq, Rat.num_div_den, Rat.mul_den_eq_num, Nat.ModEq.pow_totient, Nat.totient_pos, Nat.coprime_two_left, Nat.exists_eq_two_pow_mul_odd, Int.toNat_of_nonneg, exists_nat_gt, Finset.prod_pos, Finset.prod_induction, Odd.pos, div_mul_cancel₀, Nat.one_le_two_pow.
- [fixes] added `import Mathlib.FieldTheory.Finite.Basic` (for Nat.ModEq.pow_totient); used `∏ i ∈ Finset.range` (the `in` binder was unavailable); converted base cases, hpowR via exact_mod_cast, exponent arithmetic via Nat.add_sub_cancel.
- [DONE] lean_diagnostic_messages: success=true, empty items (no errors/warnings). Next: lake_check + lake build + lean_verify.
- [FINAL] lake_check OK. `lake build Pptc.GammaRational.Doubling` OK. lean_verify Pconstructible.Gamma_rat_Pconstructible_of_dup → axioms {propext, Classical.choice, Quot.sound}, no warnings. No sorries.

## Final structure
Helpers (all `private`):
- `Gamma_add_nat_eq_Gamma_mul_prod (hx : 0 < x) (n)`: Γ(x+n) = Γ x · ∏_{i<n}(x+i).
- `pochhammer_Pconstructible (hx : P x) (n)`: the product is P.
- `Gamma_pow_two_pow_div_Pconstructible (hdup) (x>0) (j)`: Γ(x)^(2^(j+1))/Γ(2^(j+1)x) ∈ P.
- `Gamma_nat_div_odd_Pconstructible (hdup) (p N) (Odd N)`: Γ(p/N) ∈ P via ℓ=N.totient.
- `Gamma_nat_div_two_pow_mul_Pconstructible (hdup) (p N) (Odd N) (j)`: Γ(p/(2^j N)) ∈ P, induction on j + sqrt.
- `Gamma_rat_pos_Pconstructible (hdup) (q>0)`: uses Nat.exists_eq_two_pow_mul_odd on q.den.
Main: shift q by an archimedean N so q+N>0, apply the positive case, then `Gamma_add_intCast_Pconstructible` by -(N:ℤ).
