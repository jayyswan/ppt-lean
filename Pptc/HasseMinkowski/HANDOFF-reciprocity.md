# HANDOFF: Hilbert reciprocity Phase 2 (generator cases)

Target file: `Pptc/HasseMinkowski/HilbertSymbol/Reciprocity.lean`
Namespace: `Pptc.HasseMinkowski`
Target decl: `theorem hilbertReciprocity : HilbertReciprocity`
APPEND before final `end Pptc.HasseMinkowski`; do not modify existing decls.

Phase 1 done: `hilbertReciprocity_of_generators` reduces to
`hgen : ∀ g h, IsGen g → IsGen h → hilbertProd g h = 1`.

So need 4 cases: (-1,-1), (-1,p), (p,p), (p,q) distinct.

## Log
- [start S3] Read file, Padic.lean, Two.lean, Real.lean. Available:
  hilbertSym_padic_odd_eq (odd ℓ, with Padic.valuation + padicUnit + parityPow/quadraticChar);
  hilbertSym_padic_two_eq (ℓ=2, eps/omg/twoAdicUnit); hilbertSym_real_eq;
  hilbertSym_padic_odd_case00/10/11, hilbertSym_padic_two_units(_eq_one...) etc.
- [start S3] Next: search finprod-to-finset lemma + quadraticChar/legendreSym bridge.
- [S3 batch1] Appended: import QuadraticReciprocity; `twoPrime`, `coe_padicUnit'`,
  `padic_valuation_natCast_cast`, `padic_valuation_neg_one`, `finprod_hilbertSym_eq_finset_prod`,
  `hilbertSym_padic_odd_units`, `quadraticChar_padicUnit_nat`, `quadraticChar_padicUnit_neg_one`.
  Waiting on diagnostics (first LSP call timed out warming).
- [S3 batch2] Added 2-adic unit packaging (`isUnit_two_natCast`, `unitTwo`, `coe_unitTwo`,
  `unitTwo_toZModPow_two/three`, `negOne_toZModPow_two/three`), `chi4_nat_odd`,
  `hilbertSym_padic_two_neg_one_neg_one/neg_one_unit/unit_unit/neg_one_two/two_two`,
  and odd `hilbertSym_padic_odd_neg_one_prime` / `_prime_self`, `padic_valuation_prime_ne/self`.
  Fixed several elaboration errors. LSP just closed connection (possible olean read glitch);
  retrying diagnostics.
- [S3 batch3] Added real helpers, `twoPrime` abbrev, `not_two_dvd_of_ne_two`, `prime_ne_twoPrime`,
  and case theorems `hilbertProd_neg_one_neg_one`, `hilbertProd_neg_one_prime`,
  `hilbertProd_prime_self`. First `lake_check` reported heartbeat timeouts `whnf` at the
  theorem lines (likely `twoPrime` as `def` blocking defeq with `ℚ_[2]`); switched to `abbrev`
  and replaced `simpa only [twoPrime]` by `exact`. Re-running lake_check.
- [S3 MILESTONE] `lake_check` => "OK - no errors or warnings". Three of four generator cases
  PROVED: `hilbertProd_neg_one_neg_one`, `hilbertProd_neg_one_prime` (p odd and p=2),
  `hilbertProd_prime_self` (p odd and p=2). Remaining: `(p,q)` distinct primes.
  Next: 2-adic sign `(p,q)_2 = (-1)^(p/2*q/2)` via `qrSign`, then QR assembly.
- [S3 batch4] Added `parityPow_omg_unitTwo`, `hilbertSym_padic_two_two_unit_nat`,
  `hilbertSym_padic_odd_two_prime`, `hilbertSym_padic_odd_prime_prime`,
  `hilbertSym_padic_two_two_odd`, `hilbertProd_two_prime`, `hilbertProd_prime_prime`, and
  `theorem hilbertReciprocity : HilbertReciprocity` via `hilbertReciprocity_of_generators`.
- [S3 DONE] `lake_check Pptc/HasseMinkowski/HilbertSymbol/Reciprocity.lean` => "OK - no errors
  or warnings". `rg sorry|admit|axiom` => none. Full Hilbert reciprocity PROVED.
  Only step left: confirm `lean_verify hilbertReciprocity` axioms (LSP timed out once).
- [S3 VERIFIED] `lean_verify Pptc.HasseMinkowski.hilbertReciprocity` axioms =
  {propext, Classical.choice, Quot.sound}, warnings []. No `sorry`/`admit`/`axiom` in file.
  `hilbertReciprocity : HilbertReciprocity` is FULLY PROVED. Declarations added (all in
  `Pptc.HasseMinkowski`): finprod reduction, odd/2-adic local evaluations, 2-adic unit
  packaging (`unitTwo`, eps/omg -> χ₄/χ₈), and the four generator cases
  `hilbertProd_neg_one_neg_one`, `hilbertProd_neg_one_prime`, `hilbertProd_prime_self`,
  `hilbertProd_prime_prime` (+ `hilbertProd_two_prime`).
