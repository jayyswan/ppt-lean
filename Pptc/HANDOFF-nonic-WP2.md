# HANDOFF — nonic WP2/WP3 (`Pptc/NonicWitness.lean`)

Goal (exact statements):
- `spread q ψ v` (def) : real quadratic form on `(Fin 7 → ℝ) × (Fin 6 → ℝ)`
- `exists_real_signs {q} (hmon : q.Monic) (h9 : q.natDegree = 9) (hsep : q.Separable)
    (hrel : ∃ z, q_ℂ.eval z = 0 ∧ z.im ≠ 0) : ∃ ψ v₋ v₊, spread q ψ v₋ < 0 ∧ 0 < spread q ψ v₊`
- `continuous_spread q : Continuous (fun p : (Fin 7 → ℝ) × (Fin 6 → ℝ) => spread q p.1 p.2)`
- `exists_rat_signs {q} (h : ∃ ψ v₋ v₊, spread q ψ v₋ < 0 ∧ 0 < spread q ψ v₊) :
    ∃ ψ : Fin 7 → ℚ, ∃ v₋ v₊ : Fin 6 → ℚ, spread q (↑ψ) (↑v₋) < 0 ∧ 0 < spread q (↑ψ) (↑v₊)`

File: `Pptc/NonicWitness.lean` (Mathlib imports only). Log: this file.
Rule: only edit NonicWitness.lean + this log; no sorry; ≤100 char lines; one lake_check at end.

Plan: definition `spread` via `roots.toFinset` finset sums (per plan's risk note). Sub-lemmas
1 `exists_real_divisor`, 2 root bookkeeping, 3 `exists_good_t`, 4 `exists_real_interp`,
5 `spread_add_const`, 6 evaluation (-2, 14/9). Then WP3 continuity/density.

## Log

- [start] read plan + NonicMeyer. Created log.
- [s1] spreadCore + spread def + continuous_spread compile (diagnostics clean). Imports chosen.
- [s2] spreadCore_add_const, exists_rat_signs, continuous_spread compile. Key fix: mark spread/spreadCore @[irreducible] (default reducibility made defeq checks involving spread unfold roots/toFinset and time out).
- [s3] exists_real_interp compiles (Lagrange over C, take coeff.re; used Polynomial.ext + eval_map_apply; hGcoeff needed push_cast+ring not ofReal_mul+ring). Lines ~115-175.
- [s4] exists_real_interp, spreadCore_add_const, root bookkeeping (qmap_star, qmap_star_eval, qmap_ne_zero, oots_nodup, oots_card, oots_conj_mem), spreadCore_pair_neg/pos, one_add_sum_abs_notMem, exists_good_t ALL compile. NOT done: exists_real_divisor and final exists_real_signs assembly.
- [s5] FINAL: lake env lean Pptc/NonicWitness.lean -> OK, no errors or warnings. Scratch deleted. Delivered declarations (line numbers approximate, see file): spreadCore L29, spread L32, continuous_spread L39, spreadCore_add_const L50, exists_rat_signs L73, exists_real_interp L115, qmap_star L181, qmap_star_eval L189, qmap_ne_zero L195, roots_nodup L200, roots_card L205, roots_conj_mem L213, spreadCore_pair_neg L230, spreadCore_pair_pos L263, one_add_sum_abs_notMem L293, exists_good_t L306.
- [stuck] Missing sub-lemma 1 exists_real_divisor and the assembly exists_real_signs. Exact remaining goal for the divisor: given hmon : q.Monic, h9 : q.natDegree = 9, hsep : q.Separable, hzroot : (q.map (algebraMap Q C)).eval z = 0, hzim : z.im != 0, produce D : R[X] with D.Monic, 3 <= D.natDegree, D.natDegree <= 4, D | q.map (algebraMap Q R), (D.map (algebraMap R C)).eval z != 0. Route: P := minpoly R z is the (irreducible) quadratic of z; P | q_R; let R7 := q_R / P (deg 7, monic, coprime to P). Peeling irreducible factors of R7 (each of degree <=2 by Irreducible.natDegree_le_two) via WfDvdMonoid.exists_irreducible_factor gives a divisor of degree 3 or 4 with gcd(D,P)=1, hence D(z) != 0. Assembly then combines exists_good_t + exists_real_interp + spreadCore_pair_neg/pos (spreadCore_add_const handles the dropped constant term).
