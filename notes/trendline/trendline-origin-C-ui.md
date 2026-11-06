# Trendline to origin, UI-legal data-side loopholes (probe C)

Data y = 2 x^1.5 at x = 1..4, scatter, x axis 0..5, power trendline with `DisplayEquation`. Forward/Backward untouched
(both read 0 throughout). An extra row x = 0 is appended (row 6) and the series range includes it.
Scripts and renders: scratchpad `trend-C\` (c1.py, c2.py, *.png, *.pptx). Backend: PowerPoint COM + PIL pixel analysis.

| Variant (y at x=0) | UI-reachable? | Type kept power | Equation label | Rendered curve | Touches (0,0) |
|---|---|---|---|---|---|
| **blank (cleared cell)**, row in range before trendline | yes (clear cell) | yes (XML `power`, no backward) | `y = 2x^1.5` (coefficients 2, 1.5) | drawn x=0..4, left end at pixel (250,1752) = axis origin | **yes** |
| blank, DisplayBlanksAs = interpolated (3) | yes | yes | same | identical render | yes |
| blank, row hidden (PlotVisibleOnly default) | yes | yes | same | identical render (hidden row still drawn) | yes |
| `=NA()` before trendline | typing needed: not UI-legal | yes | `y = 2x^1.5` | identical to blank | yes |
| `=NA()` trendline added first, row added after | not UI-legal | yes | `y = 2x^1.5` | left end (251,1750) | yes |
| text "a" | not UI-legal | type reported power | label empty | NO trendline drawn (only markers) | no |
| y = 0 | typing/fill (x=0,y=0 plausible) | type reported power | label empty | NO trendline drawn; fit fails (ln 0) | no |
| blank, trendline added first, row added after | yes | yes | -- | INCONCLUSIVE: render showed no data at all (chart cache not refreshed, automation flake) | ? |
| DisplayBlanksAs = zero (2), `DisplayNAasBlank`, hidden + PlotVisibleOnly=False | | | | not completed: PowerPoint crashed (RPC unavailable) and restarted | ? |

Calibration: x=0 gridline at px 250, y=0 at px 1755 in the 3000x2250 export; red trendline min x = 250, y = 1752
(within 3 px = 0.03 data units; thick line), max x 1643 = x=4 marker. Curve visibly bends from the origin, passes
the markers at x=1,2,3,4.

Why: the trendline spans the min..max of the series' x values. A point with x=0 and an empty/#N/A y is excluded from the
power regression (y must be > 0 and x > 0) but its x still extends the drawn range, so the exact fit y = 2x^1.5 is
evaluated down to x = 0 and passes through (0,0). A y of 0 or text invalidates the whole fit.

## Verdict
YES, a UI-legal loophole: include an extra row x = 0 (x from fill-series) whose y cell is cleared (blank), keep it in the
series range, and add the power trendline. Saved XML is `trendlineType power`, no `backward`; equation stays y = 2x^1.5
exactly; the curve is drawn from (0,0) to x = 4 (x axis min 0). Works whether the row is hidden or DisplayBlanksAs is gap or
interpolated. #N/A behaves the same but requires typing. y = 0 or text at x = 0 breaks the trendline.
Caveats: the "trendline added before the blank row" order was inconclusive due to a refresh flake; the right end is still
the largest x in the data (no forward extension). A tiny-positive-x point was not needed.
