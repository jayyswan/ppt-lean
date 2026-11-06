# HANDOFF hypergeometric R4 (research note, no Lean edits)

Deliverable: `NOTES-hypergeometric-R4.md` — the umbrella over the three inbound-survey
part-notes `NOTES-hypergeometric-R4a-bezier.md`, `R4b-offset.md`, `R4c-sine-exp.md`.
Research only: no `.lean` file edited/created/deleted; no lean-lsp, no lake.
Numeric backend: Wolfram kernel; scripts `archived files/hypergeometric-scripts/R4*-*.wl`.

## Log
- [start] Read AGENTS.md, PLAN §1/§2/§4 H6/§5/§6 R4, NOTES-R1, Defs.lean, ThirdKind.lean,
  Offset.lean. Split R4 into three independent curve-family surveys (Bézier / offset /
  sine+exp+rectangle), added R4a/R4b/R4c rows to the plan task table.
- [R4a] subagent: cubic Bézier arc length is genus 1 and reduces to incomplete F/E/Π (Appell
  F₁/F_D, not ₂F₁); real Q has no simple real root so no completion; only ₂F₁ degenerations
  (y=Cx³ → m=4; h=0 → K) are already landed. Checks to 99 digits. Verdict: no new source.
- [R4b] subagent: arcLength(offset) = arcLength(base) − d·Δφ; the turning-angle excess is
  elementary for every base; ellipse offset is second-kind E + elementary (no Π); monomial-graph
  offset is the old H6 ₂F₁ + d·arctan. Checks to 60 digits. Verdict: no new source.
- [R4c] subagent: sine arc length is incomplete E (Appell F₁), complete sub-arcs are the landed
  E(½); exp_two and rectangle are elementary. Checks to 40 digits. Verdict: no new source.
- [synthesis] wrote `NOTES-hypergeometric-R4.md`; updated PLAN §6 (R4 DONE + verdict table),
  §7 (programme-success wording; useful-negative now points at R4). Inbound map stated closed
  modulo the B6 first-kind differential gap.
- No `.lean` file touched; nothing committed.
