# HANDOFF: Weak approximation for ℚ → `Pptc/HasseMinkowski/RatApproximation.lean`

Exact goal (Lean syntax), namespace `Rat`:
```lean
theorem approximation' {S : Finset Nat.Primes} {ε : ℝ} (hε : ε > 0)
    (y : ℝ × (Π p : S, ℚ_[p])) :
    ∃ x : ℚ, ‖y.1 - x‖ + Finset.sum (Finset.attach S) (fun n => ‖y.2 n - x‖) < ε

abbrev finiteEmbedding (S : Finset Nat.Primes) (x : ℚ) : ℝ × (Π p : S, ℚ_[p]) :=
  ⟨algebraMap ℚ ℝ x, fun p => (algebraMap ℚ ℚ_[p]) x⟩

theorem approximation (S : Finset Nat.Primes) :
    Dense (Set.range (finiteEmbedding S))
```
Plan: (1) density of ℚ in ℝ and in each ℚ_[p]; (2) CRT to get r ≡ a_p mod p^m;
(3) add N·t with t in ℤ[1/L] (p-integral at each p∈S, dense in ℝ) and N = ∏ p^m;
(4) triangle inequalities. lake_check at end; no sorry.

## Log
- Fetched WiN7 ApproximationTheorem.lean (44 lines, both theorems `sorry`). Created log.
- Helper lemmas all compile (lake_check exit 1 only due to `sorry` in main): `norm_pow_eq`,
  `norm_natCast_eq`, `norm_sub_le`, `exists_int_modEq`, `exists_int_grid`,
  `norm_add_mul_div_le_one`. `finiteEmbedding` needs `noncomputable`.
- Now implementing `approximation'` body.

