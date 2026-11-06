# PLAN-jacobi-X5: what theory could rule routes out, and where it breaks

Read `PLAN-jacobi-X0-overview.md` first, and `NOTES-jacobi-R3.md` §2 (the derivative test and
its unproved input "(T3)"). Log `HANDOFF-jacobi-X5.md`; deliverable `NOTES-jacobi-X5.md`.

## The idea

Proving that a *specific number* like `am(1, 1/2)` is not P-constructible is hopeless with
current mathematics: it is a transcendence question. Proving that no **uniform** construction
exists is more realistic. A uniform construction is one finite recipe that works for all `u` in an
interval, with every step a function of `u`. That is a statement about *functions*, and there are
theories built for exactly that. Find the best one, say what it would prove, and find the moves it
cannot handle, since those are where a construction could hide.

## Questions

1. **Define the class.** Write a precise definition of "uniformly constructible function of
   `u`": finite trees of the moves in the overview, with each node a real-analytic function of `u`
   on some interval. List the function operations each move contributes: composition with
   elementary functions, parametric definite integrals of `√(x′² + y′²)`, implicit functions
   defined by crossings, and inverses of such integrals.
2. **Candidate theories**, and for each: what it says about `am`, and which operations from
   question 1 it can or cannot absorb.
   * **Differential algebra.** Liouvillian extensions, Rosenlicht's theorem, Kolchin's strongly
     normal extensions. Elliptic functions generate strongly normal, non-Liouvillian extensions.
     Does the class from question 1 stay inside some tower where `sn` provably cannot appear?
     Note that `ellipticEAm`, the inverse of `E`, is already in the class and is also
     non-Liouvillian, so the tower must allow some elliptic inverses but not the first-kind one.
   * **Ax–Schanuel for elliptic curves / functional transcendence** (Ax 1971; Brownawell–
     Kubota; Pila–Tsimerman). These give algebraic independence of `℘`, `ζ` (the second-kind
     analogue), `z` over `ℂ(z)`. Is "inverse of `E` is allowed, inverse of `F` is not" a statement
     about the independence of `ζ` from `℘`?
   * **D-finite / holonomic functions** (see X1): closed under `+ × ∫` and algebraic
     substitution, not under composition. How far into the class do they reach?
   * **o-minimality / Pfaffian closures** (Khovanskii, Wilkie, Speissegger). `am` is Pfaffian, so
     these probably cannot exclude it. Confirm, because it tells us which kinds of argument are
     useless.
3. **Where does it break?** For the best theory, list the specific moves it cannot absorb
   (e.g. `y = sin x` over the whole line, `offset`, crossings with transcendental curves,
   case-splits), and for each sketch what a construction exploiting it would have to look like.
   That list is the most valuable output: it tells the other agents where to dig.
4. **Non-uniform constructions.** Say explicitly what, if anything, can be said when the recipe
   changes with `u`, for example using a different construction for each rational `u`.

## Deliverable

Notes with the plain summary, the definition from question 1, a table of theories with what each
excludes, and the ranked list of "holes" from question 3. Cite sources with URLs. A theorem-level
claim needs either a reference or a proof sketch whose every step is stated.
