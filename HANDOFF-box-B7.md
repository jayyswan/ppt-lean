# B7 — offset-cusp investigation (plan §3.N6)

Research only: no `.lean` edits, no `lake`. Deliverable:
`pptc/Pptc/NOTES-offset-cusps.md`. Backend: Wolfram kernel (`wolfram_WolframLanguageEvaluator`),
exact rational arithmetic for factorisations/resultants, WP 120 for numerics.

## Log
- [start] read plan §3.N6, note §3b/§5.3, `Offset.lean:330-829`, `Defs.lean:55-210`,
  `Basic.lean:849,1204`, `DegreeSeven.lean`, `Nonic/Nonic.lean`.
- [frenet] confirmed `Γ' = (1 − dκ)γ'` symbolically for a general cubic pair (residual `{0,0}`).
  General `W = x'y''−y'x''` is degree ≤ 2, **not** cubic (cubic terms cancel) — CORRECTION to plan N6.
- [degree] `Q` quartic, `W` quadratic → `(★): Q³ = d²W²` degree 12. Genuine cusp is `w³ = dW`;
  the square adds `κ = −1/d` roots.
- [example A] `x=t, y=t³, d=1`: `729t¹²+243t⁸+27t⁴−36t²+1` irreducible deg 12; cusp
  `t*=0.16848298708195529940647787015496915331504638282383` [NC 50], point
  `(0.08363056166992986701199251781422070395614, 1.001176174802846934063925719926321849720)` [NC 40].
  BUT `t*²` is a root of irreducible sextic `729u⁶+243u⁴+27u²−36u+1`, so `t*` is already
  PConstructible (sextic + sqrt) — cautionary example, not new.
- [example B] Bézier `(0,0),(0,2),(2,0),(3,0)`, `d=1`; `x=6t²−3t³`, `y=6t−12t²+6t³`.
  Cusp poly `820125t¹²−6561000t¹¹+…+512` irreducible deg 12. Genuine cusp in [0,1]
  `t*=0.96908567783192265336657130794807810560176` [NC 50], point
  `(3.015151812639309983896917609276868074014, 0.9994137526624290102026815591764698149397)` [NC 40].
  Coordinate minpolys (and their squares' minpolys) all irreducible degree 12 → not √sextic.
- [box] `NMaximize`/`NMinimize`: in both examples the cusp is the global x-extremum of the
  offset stroke over `[0,1]`, so `box_xmax` returns the cusp abscissa with no `restrict`.
- [verdict] Cusp parameters/coordinates escape *direct* crossing reach (deg 12 > 10, different
  shape); symmetric cases already reachable; towers/non-constructibility open. Window
  isolation is the proof burden but §3b's unknown-bound circularity does not transfer (cusps
  are critical points).
- [done] wrote `pptc/Pptc/NOTES-offset-cusps.md`.
