# HANDOFF: exists_chain_roots_local (PLAN-addendum §2.1, local Lemma C)

FILE: pptc/Pptc/TotallyReal/Certificate.lean (namespace Pconstructible)
GOAL: prove `exists_chain_roots_local`, sorry-free, placed right after `exists_chain_roots_at_centre`.

Statement: given centre sign changes hs1..hs4 within eps1..eps4 and denominators hden1/hden2
at I₀, produce open U ∋ I₀ s.t. every I ∈ U has roots lam,x,mu,kappa within the eps-boxes
for chainStep1'..chainStep4'.

PLAN:
1. fix δ₄<ε₄, δ₃<ε₃ with denom-2 nonvanishing on K₃=[c₃-δ₃,c₃+δ₃].
2. W3 open ∋ (c₁,c₂): step3 sign change + denom2 nonvanish on K₃; extract δ₁',δ₂'.
3. W2 open ∋ c₁: step2 sign change + (∀x∈K₂,(lam,x)∈W3) + yNBY nonvanish; extract δ₁''<min δ₁' ε₁.
4. U = common refinement via OpenTube lemmas for (a)..(f).
5. apply exists_chain_roots_at_centre.

## Progress
- [start] created log; about to inspect file.
- [A] continuity helpers compile clean (after `exists_chain_roots_at_centre`):
  nhds_real_ball, exists_box_pair, exists_box_triple, continuous_joint_chainStep1',
  continuous_joint_den1, continuousAt_chainStep2'_fixed, continuousAt_chainStep3'_fixed,
  continuousAt_chainStep4'_fixed, continuousAt_den2. Key: fun_prop needs
  `(disch := assumption)` to close `div` side goals.
- [B] next: add exists_nhds_forall_ne_of_continuousAt + mem_Icc_abs, then main theorem.
- [C] added exists_nhds_forall_ne_of_continuousAt + mem_Icc_abs (compile clean).
- [D] wrote `exists_chain_roots_local` (lines ~888-1220); LSP diagnostics clean
  (region 870-1210, severity error). Structure: r1/r2 denom radii; δ₄; step-4 box;
  δ₃=min(ε₃/2,r2/2,re3/2); K₃; hden2m/p; step-3 box; δ₂; step-2 sign; denom2 tube rt1;
  δ₁=min(...); K₁,K₂; j1..j5; tube apps (a)-(f); U=interior of intersection; apply
  exists_chain_roots_at_centre; convert δ→ε bounds.
- [E] next: lake_check for final confirmation, then axiom_check.
- [F] lake_check exit 0; only the 4 pre-existing sorry warnings (1264, 2620, 2649, 4655)
  plus pre-existing non-sorry warnings. Cleaned new unused-simp warnings.
- [G] axiom_check Pconstructible.exists_chain_roots_local: [propext, Classical.choice,
  Quot.sound] — no sorryAx. DONE.

## Final: PROVED.
`Pconstructible.exists_chain_roots_local` (Pptc/TotallyReal/Certificate.lean, line 879),
sorry-free. lake_check exit 0; axiom_check no sorryAx.

Helper lemmas added (all private, before the theorem):
- nhds_real_ball
- exists_box_pair
- exists_box_triple
- continuous_joint_chainStep1'
- continuous_joint_den1
- continuousAt_chainStep2'_fixed
- continuousAt_chainStep3'_fixed
- continuousAt_chainStep4'_fixed
- continuousAt_den2
- exists_nhds_forall_ne_of_continuousAt
- mem_Icc_abs
Key: prove `ContinuousAt` of the rational step functions via
`simp only [<all defs unfolded>]; fun_prop (disch := assumption)`; the discharger closes
the `div` side goals from the explicit nonvanishing hypotheses.
