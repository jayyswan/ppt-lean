# HANDOFF — Pptc.TotallyReal.Newton

Goal: replace all 14 `sorry`s in `pptc/Pptc/TotallyReal/Newton.lean` with real proofs,
signatures unchanged, file order.

Plan: (1) Newton identities k=4,5 on `Multiset ℂ` in the style of
`two_mul_esymm_two` / `three_mul_esymm_three` (Pptc.DegreeSeven:1094/1108);
(2) Lemma N (odd psums -> odd esymms), ℂ and ℝ versions; (3) `psumFinY_Pconstructible`,
`psum_multisetOfY`; (4) `prodSubY` monic / natDegree / eval / coeff / odd-vanishing;
(5) `exists_cubic_seven`, `exists_quartic_eight`.

## Log
- read target file (164 lines) + PLAN sections pending
- four_mul_esymm_four: DONE (Multiset.induction_on + `linear_combination ih + a * h3`)
- five_mul_esymm_five: DONE (same + `linear_combination ih + a * h4` with h4 = four_…)
- esymm_odd_eq_zero_of_psum_odd_zero: DONE (e1 from esymm_one_eq_sum; e3,e5 via 3·e3=0, 5·e5=0)
- NEW general-CommRing section (esymm_zero', esymm_cons', esymm_one_eq_sum', two/three/four/five_…',
  esymm_odd_eq_zero_of_psum_odd_zero' with [CommRing R] [CharZero R] [IsDomain R]): DONE
- esymm_odd_eq_zero_of_psum_odd_zero_real: DONE (instance of the general Lemma N at R := ℝ)
  NB `CharZero.ne_ofNat` does NOT exist; used `Nat.cast_ne_zero.mpr` + `mul_eq_zero` instead.
- psumFinY_Pconstructible: DONE (`Finset.sum_induction` + `pow_Pconstructible`)
- psum_multisetOfY: DONE (`Multiset.map_coe` + `Multiset.map_map`, then `Finset.sum_map_val`)
- prodSubY_monic: DONE (`Finset.prod_induction` + `Polynomial.monic_X_sub_C`)
- prodSubY_natDegree: DONE (`Polynomial.natDegree_prod_of_monic`, then `simp`)
- eval_prodSubY: DONE (`Polynomial.eval_prod` + `Finset.prod_eq_zero (mem_univ i) _`)
- eval_prodSubY_of_mem: DONE (`obtain ⟨i, rfl⟩ := hx`)
- coeff_prodSubY: DONE (Mathlib `Finset.prod_X_add_C_coeff` + `Multiset.esymm_neg` +
  `Even.neg_one_pow`/`Odd.neg_one_pow`; needed `import Mathlib.RingTheory.Polynomial.Vieta`)
- prodSubY_coeff_odd_eq_zero: DONE (Lemma N on `multisetOfY y` + `coeff_prodSubY`)
- remaining: exists_cubic_seven, exists_quartic_eight (still `sorry` at this point)
- exists_cubic_seven: DONE (`prodSubY_coeff_odd_eq_zero` + `prodSubY_natDegree` + `Monic.coeff_natDegree`
  + `eval_eq_sum_range` + `Finset.sum_range_succ` expansion of the range sum + `ring`)
- exists_quartic_eight: DONE (same route, exponents {0,1,2,4,6,8})
- ALL 14 sorries replaced; file has 0 errors and 0 warnings under lean_diagnostic_messages.
  No statement was changed.  One new import added: `Mathlib.RingTheory.Polynomial.Vieta`.
- FINAL: `lake_check Pptc/TotallyReal/Newton.lean` → "OK - no errors or warnings."
  `lean_verify Pconstructible.exists_quartic_eight` → axioms {propext, Classical.choice, Quot.sound}.
  No scratch files left behind; only HANDOFF-totallyreal-newton.md was written.
