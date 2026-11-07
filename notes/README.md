# notes

Working notes, plans and subagent handoff logs for `Pptc`. Everything here is prose, not
Lean source; nothing in this directory is imported by the library. It lives inside the git
repository so notes are versioned alongside the code.

## Layout

One folder per topic, named for the construction or investigation it belongs to:

| Folder | Contents |
| --- | --- |
| `3d/` | 3D rotation of curves, the rotation formula and how it is baked |
| `algebraic/` | the `PLAN-algebraic` programme (whole/non-total-real, Theorem H/W) |
| `exponential-motives/` | literature search on exponentiation of coefficient systems |
| `hypergeometric/` | hypergeometric / Gauss, Kummer, Pfaff route |
| `lambert/` | Lambert W: plan for the lower branch `W₋₁` |
| `octic/` | octic resolvent, trace form, root extraction |
| `offset-inversion/` | offset curves, offinverse, Whewell/tangent angle, soundness defects |
| `ppt-curves/` | PowerPoint curve primitives (tan curves, Béziers, `restrict`) |
| `spiral/` | spiral and arc-length constructions |
| `theta/` | AGM (Gauss's theorem) and theta-function values |
| `third-kind/` | third-kind integrals at arbitrary `n` |
| `trendline/` | PowerPoint trendline origin (COM, XML, UI, registry) |
| `warp/` | sheared/warped sine curves; Unicode glyph catalogue (`GLYPH-CATALOGUE.md`) |
| `archive/` | retired material from earlier programmes (septic, nonic, Jacobi, totally real, gamma, …) |

Inside a topic folder:

- `HANDOFF-<step>.md` — the per-subagent progress log (one line per step). Read these before
  re-dispatching a lemma; an aborted subagent may leave its only trace here.
- `PLAN-<topic>.md` — the plan the workers were dispatched from.
- `<step>.md` / `SUMMARY.md` — the results, written up as prose with the statements found and
  the obstructions hit.
- `*.wl`, `*.py` — the Wolfram/Python scripts used to check a claim numerically.

## Conventions

- New handoff logs go in the topic folder, **not** at the repository root:
  `notes/<topic>/HANDOFF-<step>.md`.
- Keep the filename prefix (`HANDOFF-`, `PLAN-`, `NOTES-`) so the kind of file is obvious
  without opening it.
- A topic that outgrows a handful of files gets its own folder; do not add new top-level
  folders here without a good reason.
