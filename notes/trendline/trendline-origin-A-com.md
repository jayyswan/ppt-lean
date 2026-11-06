# Power trendline extended to x = 0 via COM (probe A)

Verdict: YES. The COM property `Trendline.Backward2` (Double) accepts fractional backward
forecast on a power trendline; `Trendline.Backward` (Long-typed) truncates (0.5 -> 0, 1 -> 1).
Setting Backward2 = min x (=1) makes the rendered power curve start exactly at the x = 0 axis
position, i.e. at the origin (0,0), to within render resolution (~1 px of 3000 px).

Setup: scatter chart (`AddChart2(-1,-4169)`), data (1,2),(2,5.657),(3,10.392),(4,16) = y=2x^1.5,
`Series.Trendlines().Add(4)` (xlPower). X axis min 0 max 5, Y axis 0..20, linear.
Scripts/images: scratchpad trend-A\p1.py, p2.py, an.py, an2.py, tA_b*.png/pptx.

Findings
- `Backward`: Long semantics, set 0.5 -> reads 0; 1.0000001 -> 1.
- `Backward2`: reads/sets doubles: 0.5, 1.0, 1.5 all accepted without error and read back exactly.
  `Forward2` likewise (not tested beyond read). `Forward` Long.
- XML stored (chart1.xml): `<c:trendlineType val="power"/><c:backward val="1"/>`;
  also `val="1.5"` and `val="0.5"` stored verbatim; Backward2=0 -> element omitted.
- Clamping: Backward2 = 1.5 (would reach x = -0.5) is stored as 1.5 but rendered curve stops at
  x = 0 (leftmost red pixel col 251 = axis at col 249.5); identical extent to Backward2 = 1.
  Power fit is undefined for x<=0 so it is clamped at 0, not an error.
- Backward2 = 0.5 -> curve begins at x = 0.5 (pixel 422 vs predicted 249.5+0.5*347.2=423). So
  the backward value is in x data units, subtracted from min x of the data.
- Render calibration (3000x2000 PNG): gridlines x=0..5 at cols 249.5,597,944.5,1292,1639,1986;
  y=0 at row 1559, y=20 at row 230.5. Backward2=1: red trendline spans cols 251..1641 (x=0..4),
  bottom at row 1559 = y=0, so it contains (0,0).
- Fit vs 2x^1.5 (centroid of 5px-wide line): x=0.25: 0.218 vs 0.250; x=0.5: 0.685 vs 0.707;
  x=1: 1.980 vs 2.000; x=2: 5.638 vs 5.657; x=3: 10.365 vs 10.392. Max vertical deviation
  over x in [0.04,3.95] = 2.4 px (median 1.5 px) = ~0.036 data units, consistent with a
  constant sub-2px calibration offset (line thickness / grid centre), not a shape error.
  Near 0 (x=0.01, 0.05, 0.1) the curve is within ~1-2 px (<0.03 units) of the true curve;
  finer than that is below pixel resolution, so "exactly a x^b" cannot be confirmed
  beyond render resolution. Did not determine polyline vs. smooth sampling.
- UI claim confirmed in spirit: UI "Backward" box (integer-ish) is the Long property; the
  object model's Backward2 bypasses it.
Cleanup: initial presentations ['Presentation2','Presentation3'] = final list; my presentations
closed; embedded workbooks closed.
