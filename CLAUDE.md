# Pptc — PowerPoint Constructibility

Lean 4 formalization of `PConstructible` / `PConstructibleCurve`: which real numbers are
reachable by the drawing operations of a presentation program. The Lake package is in
`pptc/`; all content lives in `pptc/Pptc/Defs.lean` (the mutual inductives) and
`pptc/Pptc/Basic.lean` (everything proved about them).

## Use lean-lsp first — it is the development loop

**Reach for the `lean-lsp` MCP tools before anything else.** They answer in about a
second; `lake build` takes ~60s for `Pptc.Basic` alone and is the last-mile confirmation,
not the way to find out whether a tactic works.

- `lean_diagnostic_messages` — errors/warnings for a file or line range. This is the
  fast substitute for a build while iterating.
- `lean_goal` — the proof state at a position. Use it constantly.
- `lean_multi_attempt` — try several tactics at a position without editing the file.
- `lean_hover_info`, `lean_local_search`, `lean_loogle`, `lean_leansearch` — confirm a
  lemma's name and exact signature *before* writing it into a proof.
- `lean_verify` / `#print axioms` — confirm nothing leaked in beyond `propext`,
  `Classical.choice`, `Quot.sound`.

Run `lake build` at the end to confirm, and after changing imports (`lean_build`
restarts the LSP). Do not use it as the edit-compile-fix cycle.

## Conventions

- **Targeted imports, never `import Mathlib`.** The latter pulls in all of Mathlib and
  roughly doubles check time. Add the specific module when a new result is needed.
- Every theorem carries a `-- Theorem: ...` line saying what it proves, and section
  `/-! ### ... -/` blocks explain *why* a construction works geometrically. Match that
  density; the prose is load-bearing in this project.
- Prefer generalizing an existing lemma over copying its proof. `pi_Pconstructible` is
  the `x = -1` case of `arccos_Pconstructible_of_mem_Icc` and is written that way.
- No `sorry` on `main`.

## Gotchas

- Source files use **CRLF** line endings. Preserve them when scripting edits.
- Toolchain is **Lean 4.33**. `le_or_lt` is not an identifier here — use `le_total`.
- `speed` deliberately spells out `√(x'² + y'²)` rather than `‖deriv γ t‖`, because
  Mathlib's product norm on `ℝ × ℝ` is the *supremum* norm and would compute the wrong
  quantity. Do not "simplify" it.
- Stale `.olean` files linger for modules removed in an earlier refactor (`Arith`,
  `Circle`, `Coordinate`, `Exp`, `Log`, `Segment`). Harmless; ignore them.
