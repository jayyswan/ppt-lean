# HANDOFF WP3.1 — disjoint case of Serre existence theorem

## UPDATE (round 2): corrected theorem with `h2`
Caller confirmed the missing hypothesis and re-issued the target WITH
`h2 : ∀ i, (∏ᶠ p : Primes, ep i p) = 1`.  Now proving:
```lean
theorem exists_disjoint {I} [Finite I] (a : I → ℤ) (ha) (hsq) (ep) (hε) (h1) (h2) (h3)
    {ℓ} (hℓ) (hℓA) (hℓgt) :
    ∃ x : ℚ, x ≠ 0 ∧ ∀ i p, hilbertSym (a i : ℚ_[p]) x = ep i p
```
with `x := (A : ℚ) * ℓ`.  Place cases: S (square mod p), T (Legendre char), outside
S∪T∪{ℓ} (units), ℓ (reciprocity + h2).
Log round 2 below.

Target file: `Pptc/HasseMinkowski/HilbertSymbol/Existence.lean` (extend, namespace
`Pptc.HasseMinkowski.Existence`).

Goal (WP3.1):
```lean
theorem exists_disjoint {I : Type*} [Finite I] (a : I → ℤ) (ha : ∀ i, a i ≠ 0)
    (hsq : ∀ i, Squarefree (a i))
    (εp : I → Primes → ℤ) (hε : ∀ i p, εp i p = 1 ∨ εp i p = -1)
    (h1 : ∀ i, ∀ᶠ p : Primes in cofinite, εp i p = 1)
    (hdisj : Disjoint (S a) (T hε h1))
    (h3 : ∀ p : Primes, ∃ x : ℚ_[p], x ≠ 0 ∧ ∀ i, hilbertSym (a i : ℚ_[p]) x = εp i p)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓA : ℓ ≡ A hε h1 [MOD M a])
    (hℓgt : ∀ s ∈ S a ∪ T hε h1, (s : ℕ) < ℓ) :
    ∃ x : ℚ, x ≠ 0 ∧ ∀ i p, hilbertSym (a i : ℚ_[p]) x = εp i p
```

Plan: x = A·ℓ; place-by-place. Sub-lemmas (named), then assembly.

## Log
- start: read Plan-v3 WP3/3.1, Existence.lean (165 lines), Defs.lean, Padic.lean (937 lines).

## IMPORTANT: the target statement is FALSE as written (missing product-formula hyp)
Counterexample: I = Unit, a = 3, ep p = if p = 5 then -1 else 1.
- S a = {2,3}; T = {5}; S ∩ T = ∅ (hdisj OK); hε, h1 OK.
- h3: p=5 choose x=5 (since (3,5)_5 = χ_5(3) = (3/5) = -1); every other p choose x=1.
- prime ℓ = 29: 29 ≡ 5 [MOD 24] (M a = 4·2·3 = 24), 29 > 5, prime (hℓ, hℓA, hℓgt OK).
- Conclusion asks for x ∈ ℚ* with (3,x)_5 = -1 and (3,x)_p = 1 for all p ≠ 5.
  Hilbert reciprocity gives ∏_p (3,x)_p · (3,x)_ℝ = 1. Since 3 > 0, (3,x)_ℝ = 1 for
  every x ≠ 0. So ∏_p (3,x)_p = 1, but under the required values it is -1. Contradiction.
Hence `exists_disjoint` cannot be proven; the statement needs the product-formula
hypothesis `h2 : ∀ i, (∏ᶠ p, ep i p) * εR i = 1` (with `εR` the archimedean prescription),
which the task text calls "h2-like constraint" but which is not implied by h3.
NOTE also: the conclusion is only about finite places (no real place), so εR never
appears; in the disjoint case the construction forces εR ≡ 1 (x = A·ℓ > 0), and then
h2 at i is exactly ∏_p ep i p = 1, which is NOT automatic.

## Round 2 log (corrected theorem with `h2`)
- `dvd_M_of_mem_S`, `prime_not_dvd_of_lt` (helpers): compile.
- `isSquare_ratCast_of_isSquare_intCast`, `isSquare_odd_natCast_of_mod`,
  `isSquare_two_natCast_of_mod8`: compile.
- `isSquare_A_mul_ell_of_mem_S`: **proved** — for `p ∈ S`, `A·ℓ` is a square in `ℚ_[p]`
  (using `8 ∣ M` for the `p=2` branch; `interval_cases` on `A' % 8`).
- `hilbertSym_A_mul_ell_eq_one_of_mem_S`: **proved** — S case of the theorem.
- `coe_padicUnitE`, `valuation_unit_eq_zero`, `padicUnit_unit`,
  `hilbertSym_unit_eq_parity`: **proved** — for odd `p`, unit `u`, nonzero `b`,
  `(u,b)_p = if Even b.valuation then 1 else χ(u)`.
All compile (`lean_diagnostic_messages` clean).

## Round 3 log (finishing `exists_disjoint`)
- `padicValNat_A_of_mem_T` (via `Nat.factorization_prod_apply` + `Finset.sum_ite_eq'`): PROVED.
- `hilbertSym_val_zero_eq_parity`, `hilbertSym_A_mul_ell_eq_of_mem_T` (T-place): PROVED.
- `prime_not_dvd_of_ne`, `hilbertSym_A_mul_ell_eq_one_of_notMem` (unit place): PROVED.
- NOTE: the statement pasted in the round-3 message omits `hdisj : Disjoint (S a) (T hε h1)`,
  but the disjoint-case construction `x = A·ℓ` requires it (if `p ∈ S ∩ T` the symbol is
  forced both to `1` and to `-1`). I keep `hdisj` (it was in the round-1 WP3.1 statement).
- `finprod_eq_one_of_eq_off` (finprod bookkeeping): PROVED.
- **`exists_disjoint`: PROVED** (namespace `Pptc.HasseMinkowski.Existence`), with the EXACT
  statement from the round-3 message (no `hdisj` parameter): `hdisj` is DERIVED internally
  from `hℓA`/`hℓgt` (a common prime of `S` and `T` would divide both `M` and `A`, hence `ℓ`,
  contradicting `hℓgt`).  Proof: `x = A·ℓ`; S/T/unit cases as lemmas; ℓ-place via
  `hilbertReciprocity` + `h2` and `finprod_eq_one_of_eq_off`.
- `lean_diagnostic_messages`: clean.

## FINAL (WP3.1 COMPLETE)
`exists_disjoint` PROVED at line 592; `lean_verify` axioms = propext, Classical.choice,
Quot.sound; `lake_check` → OK (no errors or warnings).  Statement matches the round-3
message exactly (no `hdisj` parameter; derived inside).
Key declaration lines (all proved):
222 `padicValNat_A_of_mem_T`; 249 `dvd_M_of_mem_S`; 257 `prime_not_dvd_of_lt`;
266 `prime_not_dvd_of_ne`; 310 `isSquare_A_mul_ell_of_mem_S`;
363 `hilbertSym_A_mul_ell_eq_one_of_mem_S` (S-place); 418 `hilbertSym_unit_eq_parity`;
431 `hilbertSym_val_zero_eq_parity`; 442 `hilbertSym_A_mul_ell_eq_of_mem_T` (T-place);
495 `hilbertSym_A_mul_ell_eq_one_of_notMem` (unit place); 561 `finprod_eq_one_of_eq_off`;
592 `exists_disjoint`.
Plus round-1/2 helpers (S,T,A,M, `not_realizable_of_single_neg`, etc.).

### Round 2 declaration lines
233 `dvd_M_of_mem_S`, 241 `prime_not_dvd_of_lt`, 250 `isSquare_ratCast_of_isSquare_intCast`,
259 `isSquare_odd_natCast_of_mod`, 265 `isSquare_two_natCast_of_mod8`,
285 `isSquare_A_mul_ell_of_mem_S`, 338 `hilbertSym_A_mul_ell_eq_one_of_mem_S`,
363 `coe_padicUnitE`, 369 `valuation_unit_eq_zero`, 384 `padicUnit_unit`,
393 `hilbertSym_unit_eq_parity`, 422 `not_realizable_of_single_neg`.
`lake_check` → OK (no errors/warnings).  `exists_disjoint` still not delivered
(remaining cases 1–4 below); file compiles with no `sorry`.

### Remaining pieces of `exists_disjoint` (round 2)
1. `p ∈ T` case: need `v_p(x) = 1` for `x = A·ℓ`, i.e. `padicValNat p (A hε h1) = 1`
   (exact valuation of `A` at a prime of `T`; NOT yet proved). Then apply
   `hilbertSym_unit_eq_parity` to `x` and to the `h3 p` witness `x_p`, and use that some
   `εp j p = -1` forces `v_p(x_p)` odd (via `hilbertSym_unit_eq_parity` + `parityPow`).
   Note `padicValNat p A` needs `A` squarefree / product-of-distinct-primes.
2. `p ∉ S ∪ T ∪ {ℓ}`: `a i` unit (`is_unit_ai_of_p_notMem_S`, via `Padic.valuation_intCast`),
   `x` unit (`p ∤ A` and `p ≠ ℓ`), so symbol `1` (`hilbertSym_unit_eq_parity` with even
   valuation `0`, or `hilbertSym_padic_odd_eq`); `ep i p = 1` from `ep_eq_one_of_not_mem_T`.
3. `p = ℓ`: `hilbertReciprocity`, `(a i, x)_ℝ = 1` (`x > 0`), finite factors `= εp i p`
   except possibly `ℓ`; with `h2` conclude `(a i, x)_ℓ = 1`; `ep i ℓ = 1` via
   `ep_eq_one_prime_of_lt` (`ℓ ∉ T`).
4. Assembly.

## Proved sub-lemmas (all compile, `lean_diagnostic_messages` clean)
- `prime_notMem_T_of_lt` : ℓ ∉ T.
- `ep_eq_one_prime_of_lt` : ep i ⟨ℓ,hℓ⟩ = 1.
- `M_dvd_int` : (M a : ℤ) ∣ (ℓ:ℤ) - (A:ℤ).
- `dvd_A_of_mem_T` / `not_dvd_A_of_notMem_T` : (p:ℕ) ∣ A ↔ p ∈ T.
- `two_notMem_T_of_disjoint`, `not_two_dvd_A` (A odd), `eight_dvd_M` (8 ∣ M).
- `not_realizable_of_single_neg` (line 250): a>0 ⇒ no x with symbols -1 at one prime and 1
  elsewhere (uses `hilbertProd`/`hilbertReciprocity` + `finprod_eq_single`).  Axioms:
  propext, Classical.choice, Quot.sound only (`lean_verify` clean).

## Final status
`exists_disjoint`: NOT delivered — the statement is false (missing product-formula hyp, see
above).  No `sorry`/`axiom` introduced; no `exists_disjoint` stub added.
`lake_check Pptc/HasseMinkowski/HilbertSymbol/Existence.lean` → OK (no errors/warnings).
Added import `Pptc.HasseMinkowski.HilbertSymbol.Reciprocity` (needed by the obstruction
lemma; no import cycle — nothing imports Existence).  Existing declarations untouched.
Declaration lines: 172, 180, 186, 195, 202, 213, 219, 225, 250.
Final `lake_check` (after comment fix): OK - no errors or warnings.
Next step for caller: re-issue WP3.1 with the added hypothesis
`h2 : ∀ i, (∏ᶠ p : Primes, ep i p) = 1` (the archimedean factor is forced to 1 by the
construction), then the place-by-place proof can proceed; all the elementary pieces above
are reusable.
