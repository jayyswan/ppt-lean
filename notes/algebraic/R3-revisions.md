# R3 revisions: brief for the R3 agent

Written 2026-11-12 after orchestrator review of `R3.md` (commit 27cab1c). You are revising your
own stream. Read `R3.md`, then the "Review corrections" sections at the top of `R1.md` and
`R2.md`, then this note.

## What the review found

Your computations are correct. An independent brute-force check (different code, same boxes)
reproduced them: 4 positive-definite classes for q5 at H = 8, no off-line nondegenerate point
for q6 at H = 5 or q7 at H = 3. The n = 5 control and the Bézier `J = 3` read-out are good work.
Nothing in §2–§7 needs recomputing.

The problem is what the results are said to show. The verdict claims more than a box search
over ℚ can support, and one planned item was replaced by something weaker without saying so.
The revisions below are about scope and labels, plus one piece of missing work.

## Required revisions

### 1. The search field is not the field the theorem needs

Theorem R needs the forms `Q_j` over `L`, where `L ⊂ ℝ ∩ P` is closed under square roots of
positive elements. That is an infinite extension of ℚ containing every real solvable number.
You searched `L = ℚ` in small boxes, and `L = ℚ(√d)` at H = 1 only. Cubic `L` was not reached.

- State this at the top of the findings summary, before the results, in one or two sentences.
- Everywhere the note says "no point" or "no usable `Q`", say "no ℚ-point of height ≤ H".
- The H = 1 quadratic search covers coordinates in `{−1, 0, 1}`. Say plainly that it is close
  to vacuous. Note that it also finds nothing at n = 5, where forms are known to exist, so it
  has no positive control and cannot count as evidence.

### 2. The n = 7 null was predictable and is weak evidence

For n ≥ 7, `V_τ` is a surface of general type. Bombieri–Lang predicts that its points over any
fixed number field are not Zariski dense. So finding only the line `ℓ_τ` over ℚ is the expected
outcome whether or not `V_τ(L)` has the points Theorem R needs. The plan called a failed search
here "informative"; that was the plan's error, not yours, but the note must not repeat it.

- Add a short paragraph to §5 saying this.
- Remove the inference "the control passes, so the null at n = 7 tests the route". The control
  shows the code is right. It does not show that ℚ-points are a proxy for `L`-points: at n = 5
  the surface is rational, so ℚ-points are plentiful for a reason that is absent at n = 7.

### 3. Fix the verdict and its label

- The kill verdict is labelled `[Proof]` modulo G2's catalogue. A box search is not a proof.
  Relabel it `[Heuristic]` and reword.
- Replace "the kill criterion is met in the scoped sense" and "the strict simultaneous-squares
  route is closed for the searched boxes and τ-classes" with a statement of what was observed:
  no off-line ℚ-point of the stated heights at n = 6 and n = 7, and nothing learned about
  `V_τ(L)`.
- The verdict the reviewer supports is: **the kill criterion is not established by R3. The
  route is parked, not closed.** It needs `n − 2` simultaneous `L`-points on a general-type
  surface, with no group-law handle (R1), no way to lower the count (R2), and no computation
  that can see `L`-points (this stream). Record it in those terms.

### 4. The n = 6 warm-up was not done as planned

The plan asked for the K3 case via elliptic fibrations giving points over `F` (solvable
extensions), as a warm-up for how `L`-points arise at all. You ran a ℚ box search instead and
then suggested the fibration "has Mordell–Weil rank 0 over ℚ". No fibration was written down,
so that sentence is a guess. Delete it or mark it `[Open]`.

Then do the planned item. This is the one piece of new work:

- Write down explicitly the genus-1 fibrations on `V_τ` at n = 6 (start from Z5 and A1, which
  catalogue curves on `V_τ`).
- For each, determine its **field of definition**. This is the question that matters. A
  fibration helps only if it is defined over ℚ or over a field inside `L`; then its fibres are
  genus-1 curves over `L`, which have points of degree ≤ 4, hence solvable.
- Reviewer's hint, **unverified, check it before relying on it**: `V_τ` is cut out by diagonal
  quadrics, so over the Galois closure the net is simultaneously diagonal and its discriminant
  sextic splits into 6 lines. The 15 pairwise intersections are the rank-4 quadrics, and each
  gives genus-1 fibrations via its two rulings. If that is right, a single fibration is fixed by
  a subgroup of the shape `S₂ × S₄` in `S₆`, so it is defined over a degree-15 field that is not
  solvable, and these fibrations are **not** available over `L`. That would be a real finding:
  the obvious fibrations do not descend. Either confirm it, with the Galois action written out,
  or find a fibration that does descend.
- If some fibration does descend: produce one explicit real point over a solvable extension
  that gives a positive-definite form off `ℓ_τ`, verified exactly. If none descends: say so,
  scoped to the fibrations you examined.

Label every claim. Scope every negative to the constructions examined; nothing here is a
negative about `algebraic_Pconstructible`.

### 5. Housekeeping

- `scripts/R3_counts.txt` and `scripts/R3_readout.txt` are UTF-16 with CRLF, so git stores them
  as binary and they cannot be diffed or grepped. Re-save both as UTF-8 with LF.
- The reproduction commands use `py -3`, which exists only on Windows. Give them as
  `python3 …` as well.
- The label convention uses `[Heuristic]` for exact, box-exhaustive computation. That is
  stronger than a heuristic. Keep the label if you want consistency with other notes, but then
  do not also use `[Heuristic]` for the verdict without saying which sense is meant; simplest is
  a separate label such as `[Computed, exact]` for the box results.
- `[Wolfram]` labels: keep them only where Wolfram was actually run. Where the check was Python,
  say Python.

### 6. Plan block

Rewrite the "R3 done" block in `PLAN-algebraic.md` to match the revised verdict:

- Lead with the field searched (ℚ; ℚ(√d) at H = 1), then the results.
- Replace the "Kill criterion … Met in the scoped sense" bullet with "not established; route
  parked", and the reason from item 3.
- Add the outcome of item 4.
- Leave R4 and R5 unlaunched. Do not change the status of any other stream.

## What not to change

- §2 (fields), §3 (n = 5 control), §6 (read-outs) and the numerical tables in §4, §5, §7.
- The Y1a form-3 remark and the floating-point trap remark in "Other things noticed": both are
  useful as they stand.
- No `.lean` edits, no `Defs` changes.

## Deliverables

1. Revised `R3.md`, with a short "Revision 2026-11-12" paragraph at the top listing what
   changed.
2. The n = 6 fibration analysis as a new section of `R3.md`.
3. Revised R3 block in `PLAN-algebraic.md`.
4. The two output files re-encoded.
5. A new line in `HANDOFF-alg-R3.md` for each step.
