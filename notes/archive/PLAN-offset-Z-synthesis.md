# PLAN-offset-Z: synthesis (wave 2; run after A1–A4 and B1–B4 are done)

Read `PLAN-offset-00-overview.md`, every `NOTES-offset-*.md`, and every `HANDOFF-offset-*.md`
(to see which tasks were aborted and at which step).
Log: `HANDOFF-offset-Z.md`. Deliverable: `NOTES-offset-Z.md`. Scripts: prefix `Z-`.

## Questions

1. **Status of each task.** Completed, partial, or aborted. For partial and aborted tasks, what
   is still missing, and does it block a headline?
2. **Independent re-verification of the top claims.** Take the five strongest positive claims, and
   every claim that "degree `n` is covered". For each:
   * re-run the numerical check with your own script, using a different tool where possible
     (Wolfram if the original used Python, and vice versa);
   * re-check the side conditions and the "genuinely new" checklist (overview §4);
   * try hard to break it: a wrong sign branch, a spurious root of the rationalization, a
     crossing that is not isolated, a covering system with no real solution for some root
     pattern, a degenerate Jacobian.

   * wherever a claim rests on an algebraic identity (normal form, rationalization, recovery
     equation), certify it in Lean in your scratch file `pptc/Pptc/Scratch/OffsetZ.lean` (rules
     in overview §5). Reuse the wave-1 scratch files `pptc/Pptc/Scratch/Offset*.lean` where they
     already contain it, re-checking them with `lean_diagnostic_messages`.

   Mark each claim **confirmed**, **confirmed with corrections**, or **refuted**.
3. **Reconciliation.** Where tasks disagree (dimensions, degrees, legality), settle the
   disagreement with a computation.
4. **Combine results.** Look for results that only become powerful together. For example: A3's
   offset×offset family with B1's sign-change trick; A4's rational curves with A2's cofactor
   analysis; B2's sufficiency lemma applied to the best measured family. Do the combining
   computation where it is quick; otherwise write it as a follow-up plan.
5. **Answer the programme question** as precisely as the evidence allows: *exactly how do offsets
   probe higher-degree algebraic numbers?* Give:
   * the list of new number families, with degrees and Galois evidence;
   * the largest degree `n` for which all of degree `n` is (or is conditionally) covered;
   * the status of the totally real septic;
   * the obstruction picture: what is ruled out, and under which assumptions.
6. **Follow-up plans.** Draft them, without starting them:
   * Lean formalization plans for the confirmed results (use B4's statement drafts and lemma
     DAG), each with exactly one deliverable, in the style of `PLAN-jacobi-L*.md`;
   * research plans for the most promising open leads, in the style of this series
     (`PLAN-offset-C*.md`).

   Write them as files at the repo root.

## Deliverable

`NOTES-offset-Z.md`, containing:
1. a plain-language summary of at most 20 lines for the user;
2. the verification table;
3. the reconciled master tables;
4. the programme answer;
5. the list of follow-up PLAN files written.
