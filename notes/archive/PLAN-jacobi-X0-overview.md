# PLAN-jacobi-X: exploratory routes to the amplitude (read first, every X task)

The R round (`NOTES-jacobi-R1a/R1b/R1c/R2/R3.md`, `PLAN-jacobi-00-overview.md`) looked mostly
at one route: **laying a string** (`arc_of_length`) along one fixed drawn curve so that the
string's end marks the amplitude. That route is well explored and blocked: every drawable
curve's arc length is a first-kind integral *plus* something the string cannot subtract.

This round asks about **everything else**. It is deliberately exploratory. Wild ideas are
welcome. Every claim still has to be checked, and every positive claim has to come with an
explicit construction.

Target: for P-constructible `c < 1` (take `0 < c < 1` first) and P-constructible `u`, show
`PConstructible (jacobiAm c u)`, or find a precise reason a whole family of routes cannot work.
Recall from `Pptc/JacobiAddition.lean` that it is enough to handle `u` near `0`
(`jacobiAm_Pconstructible_of_near_zero`), and that `sn`, `cn`, `dn` and `am` stand or fall
together.

## The moves a construction may make (from `pptc/Pptc/Defs.lean`)

Numbers: `1`, `+ − × ÷`, a coordinate of the **unique** crossing of two constructible curves,
the **arc length** of a traced piece of a constructible curve between P-constructible endpoints.
Curves: ellipse, rectangle boundary, polynomial graph (degree ≤ 6, rational coefficients),
`y = a x^b` (rational `a, b`), `y = 2^x`, `y = sin x`, cubic Bézier; closed under translate,
scale each axis, rotate, restrict to a window, lay an arc of given length from a constructible
point (`arc_of_length`), offset. **All parameters may be numbers computed earlier in the same
construction, including from `u`.** Constructions are finite trees; branching on cases is fine.

Already known P-constructible (usable as black boxes): roots of degree ≤ 6 polynomials, `√`,
`sin`, `cos`, `arccos`, `π`, `2^x`, `log`; `ellipticF`, `ellipticE`, `ellipticPiInc` (`n > 1`)
forwards; `ellipticEAm` (the inverse of `E`); `jacobiAm c (ellipticF c φ) = φ` for constructible
`φ`; closure of the set of good `u` under addition.

## Rules for every X task

* Research only: **no `.lean` edits.** Deliverable `NOTES-jacobi-X<n>.md` at the repo root;
  progress log `HANDOFF-jacobi-X<n>.md` (create it first and append a line after every step).
* Python 3.12 with `mpmath`, `sympy`, `numpy`, `scipy`:
  `C:\Users\jason\AppData\Local\Programs\Python\Python312\python.exe`. Scripts go in
  `archived files/jacobi-scripts/` with an `X<n>-` prefix. The Wolfram MCP may be available too.
* `mpmath.ellipfun(kind, u, m)` and `mpmath.ellipf(phi, m)` take the **parameter** `m = c`.
* Tag every identity **[symbolic]** or **[numeric, N digits]**. Web sources: give URLs.
* **A positive claim** must include the construction written as an explicit tree of the moves
  above (which curve, which parameters, which crossing or length), plus a numerical check
  that it outputs `am(u, c)` to ≥ 20 digits at 3 moduli and 3 arguments, plus a check of the side
  conditions (the crossing is unique, the tracing is injective).
* **A negative claim** must say exactly which class of constructions it excludes and which
  assumption would have to fail for a construction to slip through.
* Write the notes for a reader who knows what arc length is and not much more. Put a
  plain-language summary of at most 10 lines at the top, and keep the technical detail below it.
* Budget: stop and write up when your budget is two-thirds spent, even if unfinished. A
  well-documented dead end is a good result.

## The X tasks (all independent; run in parallel)

| file | question |
|---|---|
| `PLAN-jacobi-X1-measure.md` | Can `am(u)` be a **measured** length (forward arc length) of a curve built from `u`? |
| `PLAN-jacobi-X2-crossings.md` | Can `am(u)` be read off a **crossing** of curves built from `u`? |
| `PLAN-jacobi-X3-classical-mechanisms.md` | Do classical ellipse theorems (Fagnano, Graves, Poncelet–Jacobi, Landen, MacCullagh) give a mechanism? |
| `PLAN-jacobi-X4-defs-audit.md` | Do the formal constructors in `Defs.lean` allow more than intended? |
| `PLAN-jacobi-X5-obstruction-theory.md` | What theory could *prove* a whole class of routes impossible, and where does it break? |
| `PLAN-jacobi-X6-identity-hunt.md` | A computer search for formulas: is `am(u)` numerically equal to anything cheap? |
