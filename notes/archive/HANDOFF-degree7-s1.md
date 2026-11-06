# HANDOFF: degree7-s1 — `Pconstructible.exists_sign_change`

Goal (Lean):
```lean
theorem exists_sign_change {q : ℝ[X]} (hmon : q.Monic) (hnat : q.natDegree = 7)
    (hsep : q.Separable)
    {z : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0) (hzim : z.im ≠ 0)
    (hone : ∀ w : ℂ, (q.map (algebraMap ℝ ℂ)).eval w = 0 → w.im ≠ 0 →
      w = z ∨ w = starRingEnd ℂ z)
    {P₀ : Fin 6 → ℝ} (hQ₀ : qform (Gram q) P₀ = 0) (hP₀ne : P₀ ≠ 0) :
    ∃ d⁺ d⁻ : Fin 6 → ℝ,
      0 < p3vec q (Lcomb q (stereo (Gram q) P₀ d⁺)) ∧
      p3vec q (Lcomb q (stereo (Gram q) P₀ d⁻)) < 0
```

Target file: `pptc/Pptc/S1Sign.lean`, decl `Pconstructible.exists_sign_change`.
Plan: read deps (S1Roots, S1Cert, S1Iso, ScratchS/E/N/H, DegreeSevenOnePair), get statement compiling,
then fill step 1 (omega), step 2 (two roots), step 3 (F0), step 4 (bilin identity),
step 5 (S identity), step 6 (product), step 7 (choose j), step 8 (assemble).

## Log
- [start] created log.
- [step1] built oleans S1Cert/S1Iso; omegaC facts (add_conj, mul_conj, conj) compile. Statement uses dplus/dminus (unicode d-supluss does not parse in Lean).
- [helpers] compiled: vecOf_polyOfVec, eval_map_ofReal, ofReal_multiset_sum, ofReal_trace_mul_eq_sum, mem_R_of_root, root_of_mem_R, eq_zero_of_vanishes_on_roots, bilin_Hmat_vecOf, omegaC_prod_aux, omegaC_prod. Main theorem still sorry.
- [F4 done] Pptc/S1Sign.lean compiles (exit 0); exists_sign_change proved (replaced the unfinished subagent body; added sign_neg_aux, fixed ?/lgebraMap coercions with Complex.ofReal_injective, starRingEnd_apply, Nodup.mem_erase_iff).

## DONE (2026-09-12): plan complete, s = 1 proved unconditionally

lake build Pptc.S1Final succeeds; lake env lean clean; no sorry/dmit anywhere.

File split (adapted from the plan to allow parallel subagents; each imports the previous):
* Pptc/DegreeSevenOnePair.lean � A oot_Pconstructible_of_tschirnhaus, B p3vec_eq_sum/continuous_p3vec, C stereo + S1/S2/S3, D exists_isotropic_Pconstructible, E1 exists_rat_vec_pos.
* Pptc/S1Sextic.lean � E2 exists_sextic_along_line.
* Pptc/S1Roots.lean � F1 oots_eq_pair_add_real.
* Pptc/S1Cert.lean � F3 exists_lagrange_value.
* Pptc/S1Iso.lean � F5 isotropic_plane_trivial.
* Pptc/S1Sign.lean � F4 exists_sign_change (the crux; Lagrange/conjugation sign certificate).
* Pptc/S1Final.lean � G assembly, oot_Pconstructible_of_one_conjugate_pair, and the literal issue statement oot_Pconstructible_of_nonreal_root.

lean_verify on both final theorems reports only propext, Classical.choice, Quot.sound.
