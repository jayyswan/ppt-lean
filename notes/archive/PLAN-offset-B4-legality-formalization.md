# PLAN-offset-B4: legality of offset extractions, and the Lean infrastructure they need

Read `PLAN-offset-00-overview.md`, `pptc/Pptc/Defs.lean` (all of it), the whole of
`pptc/Pptc/Offset.lean`, `crossing_Pconstructible` and its helpers in `pptc/Pptc/Basic.lean`
(~l.300-390), and `NOTES-jacobi-X4.md` (the audit of the constructors).
Log: `HANDOFF-offset-B4.md`. Deliverable: `NOTES-offset-B4.md`. Scripts: prefix `B4-`.

You get the scratch file `pptc/Pptc/Scratch/OffsetB4.lean` (overview §5); the other `.lean`
files are read-only. This task leans on Lean more than the others. **Check every statement draft
in the scratch file** with `lean_diagnostic_messages`, and prove the small generic lemmas
outright where you can: the norm lemma (question 4), rational-curve recovery (question 3), and
the parabola offset computation (question 5). Label each draft in NOTES as **proved**,
**stated (sorry)** or **untested**. Never run `lake build`.

## Why

The other tasks will propose constructions: offset × conic, offset × offset, self-crossings,
chains, rational offsets. Each one relies on the formal `offset` constructor actually granting
the step, and a Lean proof will need reusable lemmas for it. Settling legality and designing the
infrastructure now keeps the eventual formalization from stalling.

## Questions

1. **Legality, mechanism by mechanism.** For each of the following, decide whether it follows from
   the constructors as written, with exact reference to the hypotheses (`hsub`, `hinj`, `hdiff`,
   `hreg`, `hC1`, `hd`). List every side condition a construction must establish.
   * the offset of an arc of an ellipse or hyperbola (a trig or rational parametrization; which
     is easier to discharge);
   * the offset of an arc of a polynomial graph, of a power-law arc, of `sin`, of `2^x`;
   * the offset of an offset (needs a tracing of the offset curve that is injective, regular and
     `C¹`; where do these fail?);
   * the offset of an affine image of an offset (chains, A4);
   * the offset of an `arc_of_length` output (its tracing is only given abstractly);
   * a restricted offset curve crossed with another restricted offset curve (A3);
   * two disjoint parameter windows of the same offset (self-crossings, A3);
   * cusps (A3 question 3): is there any legal way to pin a cusp?
2. **The crossing lemma for non-polynomial curves.** `crossing_Pconstructible` needs `F` vanishing
   on the second curve, and **finiteness** of the zeros of `F ∘ Γ`. For offset × offset there is no
   convenient `F` on the offset side except the rationalized implicit polynomial. Design
   alternatives:
   * **Analytic finiteness.** A real-analytic function on a compact interval that is not
     identically zero has finitely many zeros. Check what Mathlib has
     (`AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero`, the isolated-zeros
     results, `AnalyticAt` for `sqrt` of a positive function). Draft the lemma "two analytic
     arcs that are not identical near `β` meet only finitely often in a compact window" in Lean
     syntax, list the Mathlib lemmas it would use (confirm the names with lean-lsp search), and
     estimate the effort.
   * **Isolation without finiteness.** A version of `crossing_Pconstructible` needing only that
     `β` is an **isolated** crossing, which suffices to find a rational box. Draft it the same
     way.
   * Say which of the two makes the A2 / A3 / A4 constructions cheapest to formalize.
3. **Recovery lemmas.** Generalize `offsetParam_normal_eq_zero` and `normalEq_eq_quinticVal`:
   * the normal equation for rational curves (conics, rational offsets);
   * recovering the parameter of a proper rational parametrization from the point (degree 1:
     what Lean statement?);
   * recovery through a chain.
4. **Rationalization lemmas.** The pattern `g·w + d·h = 0 ⇒ g²w² − d²h² = 0` recurs, with more
   terms for conics and cubics (`Σ Fᵢ dⁱ/wⁱ`). Draft one generic lemma, "a polynomial in `w` with
   `w² = S` that vanishes ⇒ its norm vanishes", in a form that makes every A2 family a one-line
   instance, and check it against Mathlib's `Polynomial` API.
5. **The rational-offset curves** (A4). For the parabola `y = x²` offset by `d`, draft the Lean
   statement that its image equals a rational parametrized curve on a window, and the proof
   plan: compute `offsetParam` explicitly, then show the reparametrization is a bijection on a
   window.
6. **Statement shapes.** For three likely headline theorems, draft the final Lean statement and the
   lemma DAG with effort estimates. Suggested headlines: an offset×conic engine, an offset×offset
   engine, and a "degree-`N` family covered" theorem. Follow the repo's conventions: a
   `-- Theorem:` line, `@[pconstructible]` tags where appropriate, no `import Mathlib`.

## Deliverable

1. The summary.
2. A legality table: mechanism × {legal as-is / legal with sub-arc conditions / not legal}, with
   the exact hypotheses involved.
3. The Lean statement drafts (in fenced code, marked *untested* unless checked with
   `lean_run_code`), with the Mathlib lemma names confirmed.
4. Effort estimates and a recommended order of formalization.
5. The Side discoveries and Leads sections. Include any `Defs.lean` modelling issue found for
   `offset` that X4 missed.
