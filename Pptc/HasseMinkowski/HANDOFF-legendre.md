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
