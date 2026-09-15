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
