# HANDOFF: Pptc/Hypergeometric/SqrtSeries.lean

Goal (Lean syntax):
```lean
namespace Pconstructible
noncomputable def sqrtInvSeries : PowerSeries ℝ
theorem constantCoeff_sqrtInvSeries : PowerSeries.constantCoeff sqrtInvSeries = 1
theorem sqrtInvSeries_mul_self : sqrtInvSeries * sqrtInvSeries * (1 + PowerSeries.X) = 1
theorem one_add_X_mul_derivative_sqrtInvSeries :
    (1 + PowerSeries.X) * PowerSeries.derivative ℝ sqrtInvSeries
      = -(1/2 : ℝ) • sqrtInvSeries
end
```
Target file: `Pptc/Hypergeometric/SqrtSeries.lean` (new).
Plan: Route A (coefficients). h_n = (-1)^n * C(2n,n)/4^n. Prove recurrence
(n+1) h_{n+1} = -(n+1/2) h_n from Nat.succ_mul_centralBinom_succ; then
derivative ODE by coefficient ext; then h*h*(1+X)=1 by d(h^2(1+X))=0 + constant.

## Log
- [step 0] created handoff file; about to inspect Quadratic.lean for conventions/lemmas.
- [step 1] wrote SqrtSeries.lean with route A; imports initially lacked ℝ -> many errors.
- [step 2] fixed imports (Real.Basic + tactic modules; Omega module does not exist in 4.33).
- [step 3] changed sqrtInvCoeff to use Nat.choose (2*n) n; added coeff_one_add_X_mul_derivative
  (single lemma covering n=0 via `n*[X^n]f + (n+1)*[X^(n+1)]f`); rewrote derivative theorem.
- [step 4] rewrote sqrtInvSeries_mul_self's hder using PowerSeries.smul_eq_C_mul and an
  explicit ring rearrangement; `norm_num` closed `(2:PS)*(C (-1/2)) = -1`.
- [step 5] lean_diagnostic_messages: success, 0 items. File compiles in warm env.
- [step 6] lake_check Pptc/Hypergeometric/SqrtSeries.lean -> "OK - no errors or warnings."
- [step 7] lean_verify on the three theorems: axioms = propext, Classical.choice, Quot.sound;
  no warnings; grep for sorry/admit/axiom -> none. DONE.
