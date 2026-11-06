**OUT OF SCOPE: file editing not allowed (challenge permits PowerPoint UI actions only). Results below are informational and must not count as a valid route.**

# Power trendline to the origin: OOXML route (agent B)

Verdict: YES. Editing chart XML makes a power trendline (y = a*x^b, b>0) reach x = 0.

Scratch dir: C:\Users\<user>\AppData\Local\Temp\claude\C--dev-Powerpoint-lean\c222b849-70f5-4b01-ad09-a19ea61d2b9d\scratchpad\trend-B\  (build.py, var.py, var2.py, meas*.py, tB_*.pptx/png)

## Setup
Scatter chart (xlXYScatter), data x=1..4, y=2*x^1.5 (2, 5.657, 10.392, 16), power trendline added via COM,
saved with SaveCopyAs. Chart XML edited by hand (zip rewritten, deflate, same member order).

## Exact XML
Inside <c:trendline> (schema order respected: ... trendlineType, [forward], backward, dispRSqr, dispEq):

    <c:trendlineType val="power"/><c:backward val="1"/><c:dispRSqr val="0"/><c:dispEq val="0"/>

x-axis scaling: `<c:scaling><c:orientation val="minMax"/><c:max val="5"/><c:min val="0"/></c:scaling>`

## Results (3000x2250 PNG export; x=0 at px 250.5, y=0 at px 1644; 347 px/x-unit, 62.6 px/y-unit)
- control (no backward): leftmost trendline px x=590 (data x = 1, the first point).
- backward=0.5: starts at px 422 (x = 0.5).
- backward=1 / 0.99 / 2: leftmost px 251, y px 1644 = exactly (0,0). backward larger than min-x is
  clamped at x=0 (domain of x^b); not an error.
- Axis min -1 with backward=2: trendline still stops at x=0 (nothing drawn for x<0).
- PowerPoint opens all variants without repair prompt; type stays power (Trendline.Type = 4).
- Round trip (open edited file, SaveCopyAs): `<c:backward val="..."/>` survives verbatim (1, 0.99, 2, 0.5 all kept,
  NOT clamped in XML, even 2 > min-x). Trendline stays `power`. PowerPoint re-adds sysDot dash as it was in base.
- Zoomed render (x in [0,0.5], y in [0,1.5], y = 2x^1.5): sampled px vs ideal
  x=0.01: y 0.0013 vs 0.0020; 0.05: 0.0216 vs 0.0224; 0.1: 0.0617 vs 0.0633; 0.4: 0.5032 vs 0.5060.
  All within ~1 px (about 0.001 in y units) of a*x^b. Leftmost drawn pixel at x~0.0045 on y=0 (dotted line start,
  within dash/cap size of the origin). Curve looks smooth (dense sampling), not visibly polygonal.

## Caveats
- Render only; not an infinite-precision claim. Drawn extent is x in [0, x_max_data]; line touches (0,0) to pixel accuracy.
- COM Trendline.Backward for power is read-only/unsupported through UI per user report, but the file-level value is honoured.
- Forward not tested.
- Cleanup: all presentations I opened were closed. At the end only 'Presentation2' remains open; it was not created by me
  (initial list was ['Presentation1'], which disappeared during the run, presumably the other agent's).
