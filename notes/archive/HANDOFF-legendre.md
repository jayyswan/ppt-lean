# HANDOFF legendre

Goal: create `Pptc/HasseMinkowski/Legendre.lean` with

```lean
theorem hilbertSym_eq_of_sq_sub_eq_mul {k : Type*} [Field k] [Invertible (2 : k)]
    {a b b' t : k} (hb : b ≠ 0) (hb' : b' ≠ 0) (h : t ^ 2 - a = b * b') :
    hilbertSym a b = hilbertSym a b'
```

Plan: read Plan-v3 WP1.1 and Norm.lean API, then prove by cases on a=0 / IsSquare a / main case
using hilbertSym_eq_one_iff_isNorm + QuadraticAlgebra.norm_mul + star.

- [start] log created.
- Read Norm.lean, Padic.lean, Defs.lean, Plan-v3 WP1.1. API: hilbertSym_eq_one_of_sol,
  hilbertSym_mul_square_eq, hilbertSym_eq_one_iff_isNorm, hilbertSym_comm, hilbertSym_zero_left.
  QuadraticAlgebra k a 0: norm ⟨x,y⟩=x²-a y², star, map_mul, norm_star, norm_algebraMap.
- Drafted Legendre.lean. First diagnostics: 5 errors (ring no-goals, nlinarith failed on witness,
  rw on ≠ goal). Fixed: removed extra ring, rw[hs];ring, intro for ≠. 
- `lean_diagnostic_messages`: success=true, zero items. Proof complete.
- [DONE] `lake_check Pptc/HasseMinkowski/Legendre.lean` => OK no errors/warnings.
  Theorem at line 27. DONE.

## Round 2: WP1 1.4, 1.2, 1.3

- [start] appended log. Need: exists_squarefree_mul_sq_int, exists_squarefree_mul_sq,
  exists_sq_mod_of_hilbertSym, exists_sq_mod_squarefree. Read plan + Padics API first.
- API found: Nat.sq_mul_squarefree (∃a b, b^2*a=n ∧ Squarefree a); Nat.sq_mul_squarefree_of_pos
  (∃a b, 0<a ∧ 0<b ∧ b^2*a=n ∧ Squarefree a); Int.squarefree_natAbs/natCast (simp);
  Rat.abs_def, Rat.divInt_eq_div (Reciprocity technique). Writing 1.4 now.
- 1.4 DONE (exists_squarefree_mul_sq_int, exists_squarefree_mul_sq). 1.3 DONE
  (exists_sq_mod_squarefree) via Nat.chineseRemainderOfFinset + Int.bmod + Finset.prod_dvd_of_coprime.
  All diagnostics clean so far (no lake_check yet). Now 1.2 (hardest).
- 1.2 DONE (exists_sq_mod_of_hilbertSym): p|a -> t=0; p=2 -> t=a via ZMod 2; odd p: padicValInt
  p b = 1 from squarefree+p|b -> ‖b‖=p⁻¹, a a unit via PadicInt.isUnit_iff, then
  hilbertSym_padic_odd_case10 gives χ(a)=1, quadraticChar_one_iff_isSquare + intCast_surjective.
  lean_diagnostic_messages clean for all. Running final lake_check.
- [DONE] `lake_check Pptc/HasseMinkowski/Legendre.lean` => OK - no errors or warnings.
  Declarations: hilbertSym_eq_of_sq_sub_eq_mul (l.27, round 1),
  exists_squarefree_mul_sq_int (1.4), exists_squarefree_mul_sq (1.4),
  exists_sq_mod_squarefree (1.3), exists_sq_mod_of_hilbertSym (1.2). No sorry/axiom, lines ≤100.

## Round 3: WP1.5 legendre_int (critical path)

- [start] plan: strong induction on a.natAbs+b.natAbs with inner `main` taking `hab : sum = n`
  and `hle : a.natAbs ≤ b.natAbs`; swap case via hilbertSym_comm + main b a. Base b.natAbs≤1
  case bash on a,b ∈ {±1}. Step: exists_sq_mod_squarefree -> t, b'=(t²-a)/b, bound |b'|<|b|,
  b'=b''u², transfer hyps with hilbertSym_eq_of_sq_sub_eq_mul/hilbertSym_mul_square_eq, IH.
  Need: Real.lean hilbertSym_real_eq, Int.natAbs_le, invertibleOfNonzero, Int.ediv_mul_cancel.
- WP1.5 written; first diagnostics: case name for Nat.strong_induction_on is `_` not `ind`;
  abs_add -> abs_add_le; mul_lt_mul_left instance issue -> nlinarith; IH needs bound on b'' not
  b'; silent linter.style.haveILetI via set_option. All lean_diagnostic_messages clean now.
- [DONE] running final lake_check for legendre_int.
- [DONE] `lake_check Pptc/HasseMinkowski/Legendre.lean` => OK - no errors or warnings.
  `legendre_int` at line 385. No helpers added (only local `main` inside the induction step).
  Round 3 complete.

## Round 4: WP1.6 hilbertSymLocalGlobal + isotropic_of_rank_three'

- [start] Read RankThree.lean for HilbertSymLocalGlobal / isotropic_of_rank_three signatures.
  Then append two theorems in Legendre.lean, import Pptc.HasseMinkowski.RankThree.
- Added import RankThree (no cycle). hilbertSymLocalGlobal: square-class NF of A,B via 1.4,
  legendre_int on (a,b), transfer local hyps by hilbertSym_mul_square_eq at each place.
  isotropic_of_rank_three' := isotropic_of_rank_three hilbertSymLocalGlobal Q hr hQ hQ'.
  Issues fixed: specialize hlocp p before rewriting; `open Module` for `finrank`.
  lean_diagnostic_messages clean. Running final lake_check.
- [DONE] `lake_check Pptc/HasseMinkowski/Legendre.lean` => OK - no errors or warnings.
  hilbertSymLocalGlobal at line 610, isotropic_of_rank_three' at line 654. WP1.6 complete.
  NOTE for later: RankThree.lean could import Legendre.lean and drop the `hloc` hypothesis
  (isotropic_of_rank_three unconditional / its `HilbertSymLocalGlobal` def could be replaced),
  but RankThree must then no longer be imported by Legendre to avoid a cycle — restructure by
  moving isotropic_of_rank_three' (or Legendre) into the import order. Do not edit now.
