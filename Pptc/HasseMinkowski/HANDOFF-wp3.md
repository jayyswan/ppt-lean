# HANDOFF WP3.1 — disjoint case of Serre existence theorem

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
