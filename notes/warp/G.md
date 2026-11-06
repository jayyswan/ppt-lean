# Stream G: exact shape of the sine glyph 〰 (U+3030, Yu Mincho) and a font sweep

Labels: [Measured] = fontTools/Python extraction or sampling; [Wolfram] = fit or check done in the Wolfram
MCP (node lists / sampled points pasted in); [Heuristic]; [Open]. Units are font units, em = 2048.
Scratch (scripts, `glyphs.json`, `screen_out.json`):
`C:\Users\<user>\AppData\Local\Temp\claude\C--dev-Powerpoint-lean\c222b849-70f5-4b01-ad09-a19ea61d2b9d\scratchpad\warp_G\`.

## Findings summary

1. **Edge model of 〰 in Yu Mincho: the two edges are normal offsets of a common spine (a constant-width
   stroke), not vertical shifts.** [Wolfram] The normal distance from the top edge to the bottom edge is
   72.7 to 76.7, mean 74.08 (about +-2 units, 0.5 % of H). The vertical gap swings 73.0 to 104.0 (mean 89.5,
   sd 10.0); a constant-width band predicts `74*sqrt(1+s^2)` = 103.9 at the max slope 0.986, which matches.
   The best vertical shift of the top edge onto the bottom edge leaves a max residual 13.0 (3.3 % of H);
   the best normal offset (w = 75) leaves 2.1 (0.5 %). Normal offset wins by about 6x. **This is the deck's
   assumption, confirmed.**
2. **The spine is a sine to about 1 to 2 % of the amplitude.** [Wolfram] Spine
   `y = c + a cos(2 pi x / 1024)` with `c = 778.8`, `a = 158.8` (period exactly 1024 = em/2, crests at
   x = 0, 1024, 2048). Max vertical deviation with the period fixed: 2.0 % of a (3.2 units) for the deck's
   recovery (top edge pushed down w/2); 1.3 % from the bottom edge pushed up; 1.26 % least squares (0.97 %
   minimax, 1.5 units) for the midpoint-of-normal-chord spine. Residuals are within +-1 unit at the extrema
   and reach 1.9 to 3.2 near x = 1408. Integer font coordinates alone limit accuracy to about 0.3 to 0.6 % of
   a, so part of this is quantization. **This replaces P1b's 12 to 19 % figure, which was for the wrong glyph
   (U+223F).**
3. **Neither edge is itself a sine.** [Wolfram] Top and bottom edges fit `c + a cos(wx+phi)` (period fixed
   at 1024) to 5.3 % and 5.9 % of a least squares (minimax about 5.0 % and 5.1 %, max dev about 8 units),
   because a normal offset of a sine is not a sine. Against the ideal "sine spine +- w/2 along the normal"
   the font edges lie within 2.2 (w = 75) to 2.7 (w = 74) units; against "sine +- vertical shift 45.4" within
   9.4. **So with this glyph the warped band edges are polar images of offset sines, not `r = a + b sin`;
   no vertical-shift route to exact limacons.**
4. **Thickness and ink box.** [Measured/Wolfram] Ink box x in [0, 2048] (zero side bearing, width = em), y in
   [582, 975], H = 393. Normal width `w = 74.1` (`w/H = 0.188`, `w/W = 0.036`). `2a + w = 391.6`, within 1.4
   of H; the ink-box centre y = 778.5 equals the spine centre; box top/bottom are spine crest/trough +- w/2
   (938 + 37 = 975; 619 - 37 = 582). In ink-box fractions the spine is `v = 0.5 + 0.404 cos(4 pi u)` (crest
   0.906, trough 0.094). The end cuts are vertical lines at x = 0 and 2048, 73 units tall, at crest height:
   the deck's "6 pt at the end" equals w to within 1.5 %.
5. **Outline structure.** [Measured] One contour: `L` (left cut), 15 TrueType quadratic Beziers along the top
   edge, `L` (right cut), 16 quadratics back along the bottom edge. 33 segments, no cubics, 2 periods (crest,
   trough, crest, trough, crest). About 8 quadratics per period, hand fitted; the two periods are not
   node-identical. Idealization category: a hand-fitted quadratic-spline approximation of a constant-width band
   about a sine spine, sine accuracy about 1 to 2 % of a.
6. **Weights.** [Measured] Yu Mincho is not in `C:\Windows\Fonts` or the user font folder; it is an Office
   cloud font and only **Regular** is cached
   (`%LOCALAPPDATA%\Microsoft\FontCache\4\CloudFonts\Yu Mincho\31868023978.ttf`, 13 MB, no fvar, weight class
   400). Light and Demibold are not installed here [Open]. Yu Gothic (Light, Regular, Medium, Bold and the UI
   variants, 9 faces) share **one identical 〰 outline**, within about 1 to 2 units of Yu Mincho's (same
   crest/trough nodes; bottom-edge crest 901 vs 902; one trough segment is a single quadratic instead of
   three). So 〰 is weight-independent across the Yu fonts and the result transfers.
7. **Sweep** (U+3030, 301C, FF5E, 223F, 2053, 2240, 2307, 2E1C, 2E3C, 7E, 2DC, 303, 223C, 223E, 2248, 2312):
   [Measured + Wolfram] 1187 distinct outlines over 1602 (font, code point) pairs. **No glyph has exact
   vertical-shift edges and none has exactly sinusoidal edges.** Closest cases in section 5. Yu Mincho/Yu
   Gothic 〰 has the best sine spine of all wave-like glyphs found (1 to 2 % of a; the next best are 2.0 %
   for Roboto Italic ⁓ and 3.7 % for the Constantia tilde, both 1 period or less, and 5 % or worse elsewhere).

## 1. Outline of 〰 in Yu Mincho (G a)

Font: Yu Mincho Regular (single TTF, glyph `uni3030`, advance 2048, upem 2048, bbox 0..2048 x 582..975).
All curves are quadratic Beziers `p0 control p1`, top edge left to right:

```
L (0,902) -> (0,975)                         left cut, vertical
T: (0,975) (76,970) (133,933) | (133,933) (183,900) (287,799) | (287,799) (376,713) (427,683) |
   (427,683) (472,656) (512,656) | (512,656) (557,656) (610,692) | (610,692) (656,723) (735,799) |
   (735,799) (848,908) (910,944) | (910,944) (965,975) (1024,975) | (1024,975) (1092,975) (1156,934) |
   (1156,934) (1211,897) (1313,799) | (1313,799) (1459,656) (1536,656) | (1536,656) (1582,656) (1634,691) |
   (1634,691) (1681,722) (1759,799) | (1759,799) (1875,910) (1931,942) | (1931,942) (1982,971) (2048,975)
L (2048,975) -> (2048,902)                   right cut
B (right to left): (2048,902) (1996,898) (1947,865) | (1947,865) (1904,836) (1823,758) |
   (1823,758) (1714,651) (1650,614) | (1650,614) (1594,582) (1536,582) | (1536,582) (1470,582) (1404,625) |
   (1404,625) (1344,663) (1249,756) | (1249,756) (1159,844) (1110,874) | (1110,874) (1066,901) (1024,901) |
   (1024,901) (977,901) (924,865) | (924,865) (878,834) (799,756) | (799,756) (687,649) (625,614) |
   (625,614) (569,582) (512,582) | (512,582) (447,582) (380,626) | (380,626) (321,664) (225,756) |
   (225,756) (133,846) (87,874) | (87,874) (47,899) (0,902)
```

Top edge: crests at x = 0, 1024, 2048 (y = 975); troughs at x = 512, 1536 (y = 656). Bottom edge: crest
y = 901 (x = 1024) and 902 (ends), troughs y = 582. Each edge has half-range 159.5; the vertical gap at the
extrema is 74.

## 2. Edge model (G b)

All numbers [Wolfram], edges sampled from the exact Beziers (200 samples per segment, nearest-point
distances; interior x in 100..1948 where an offset is compared).

| model | statistic | value |
|---|---|---|
| vertical shift (any constant) | vertical gap top - bottom | 73.0 to 104.0, mean 89.5, sd 10.0 |
| vertical shift, best constant | max distance of shifted top to bottom | 13.0 at shift 87 (3.3 % H); 21.9 at 74; 17.5 at 80 |
| normal offset, constant w | distance top -> bottom curve | 72.65 to 76.74, mean 74.08 |
| normal offset, offset(top, w) vs bottom | max distance | 2.07 (w = 75), 2.76 (w = 74), 3.75 (w = 73) |
| constant-width prediction | `w sqrt(1 + slope^2)` at max slope 0.986 | 103.9 (observed max gap 104.0) |

Conclusion: normal offset, residual about 2 units (partly the quadratic approximation of an offset curve,
partly quantization). Vertical shift is rejected (residual 13; gap range ratio 1.42).

## 3. Spine vs sine (G c)

Spine recovered three ways, sampled from the exact Beziers: deck method (top edge moved down w/2 along its
normal, w = 74); the bottom edge moved up w/2; midpoint of each top sample and its nearest bottom point.
The two normal-offset spines agree to 3.0 max (so w is constant to about +-1.5).

Fit `y = c + A sin(wx + phi)` [Wolfram, 0 <= x <= 2048]:

| curve | period | c | amplitude A | max dev | % of A |
|---|---|---|---|---|---|
| spine, top pushed down w/2, free period (LS) | 1025.2 | 779.09 | 158.85 | 2.73 | 1.72 |
| spine, bottom pushed up w/2, free period (LS) | 1023.4 | 778.59 | 158.88 | 2.00 | 1.26 |
| spine, top-offset, period fixed 1024 (LS) | 1024 | 778.89 | 158.79 | 3.2 | 2.0 |
| spine, chord midpoint, period fixed 1024 | 1024 | 778.83 | 158.83 | 1.53 minimax (LS 2.0) | 0.97 (LS 1.26) |
| top edge, period fixed (LS) | 1024 | 822.6 | 158.5 | 8.4 | 5.3 (minimax 5.0) |
| bottom edge, period fixed (LS) | 1024 | 733.9 | 158.8 | 9.3 | 5.9 (minimax 5.1) |

Where the error sits [Wolfram, chord-midpoint spine, residuals binned at 128-unit steps]: at the extrema
x = 0, 512, 1024, 1536, 2048 the residuals are 0.7, -1.0, 0.35, -1.0, 0.7; between extrema they range -1.1 to
+1.9, peaking near x = 1408. With a = 158.8: extremal error 0.2 to 0.6 % of a, worst in-between error 1.2 %
(chord) to 2 % (top-offset).
Using the deck's end-thickness 73 instead of 74 moves the offset by 0.5 unit: negligible.

## 4. Thickness and ink box (G d)

- Normal width w = 74.08 (range 72.7 to 76.7). Ink box 2048 x 393. `w/H = 0.1885`, `w/W = 0.0362`,
  `w/(2a) = 0.233`.
- `2a + w = 391.6` vs `H = 393`: the box is the spine's range inflated by w/2 each side.
- Box top = top-edge crest = spine crest 938 + 37; box bottom = bottom-edge trough = spine trough 619 - 37.
  Box centre y = 778.5 = spine centre c.
- Horizontally the box is exactly the advance (zero side bearings). The ends are vertical cuts at crest height
  (spine mid-height at x = 0 is 938.5, crest 938): the spine runs over exactly two periods `[0, 2048]`.
- Warp inputs, ink-box fractions `u = x/2048`, `v = (y - 582)/393`: spine `v = 0.5 + 0.404 cos(4 pi u)`;
  edge half-width 0.094 in v (total 0.188); top edge crest at v = 1, bottom edge trough at v = 0.

## 5. Sweep (G e)

Method: every glyph for the 16 code points above in `C:\Windows\Fonts` (TTC members individually), the user
font folder (nothing relevant), Office `offsym*.ttf` and the Office cloud-font cache; deduplicated by
outline hash. Python sliced each outline vertically (top U(x), bottom L(x); ends trimmed 6 to 8 %) to screen;
Wolfram redid the fits on a shortlist. "Vres" = max |gap - mean gap| as % of H; "Nres" = max |gap -
w sqrt(1+s^2)| as % of H with s the midline slope (a first-order test, weaker than the exact distance test of
section 2); sine columns are least-squares max deviation as % of the fitted amplitude, free period. Slices use
integer font units.

| glyph | H | max slope | w/H (normal fit) | Vres %H | Nres %H | spine vs sine %A | top / bot edge vs sine %A | edge model |
|---|---|---|---|---|---|---|---|---|
| 〰 Yu Mincho (exact, sec. 2-3) | 393 | 0.99 | 0.188 | 3.3 (best shift) | 0.5 | 1 to 2 | 5.3 / 5.9 | **normal offset** |
| 〰 Yu Gothic, all weights | 393 | 0.99 | 0.188 | screen rV 0.108 | screen rN 0.013 | screen 1.5 | n/a | normal offset (same as Mincho) |
| ∿ U+223F Lucida Sans Unicode | 1184 | 3.7 | 0.085 | 15.8 | 2.2 | 5.1 | 14.3 / 14.7 | normal offset, steep, about 1 period |
| ∿ U+223F Cambria / Cambria Math | 746 | 2.0 | 0.204 | 24.6 | 11.3 | 5.2 | 21.5 / 21.1 | neither (width varies 150 to 413) |
| 〰 JhengHei Regular | 388 | 0.91 | 0.273 | 5.9 | 2.2 | 5.8 | 13.7 / 9.8 | normal offset |
| 〰 YaHei Regular | 388 | 0.88 | 0.416 | 8.9 | 3.7 | 6.6 | 17.8 / 20.9 | normal offset |
| 〰 Meiryo | 547 | 3.1 | 0.158 | 21.5 | 21.2 | 14.2 | 22 / 23 | neither (not sinusoidal) |
| 〰 MS Mincho | 35 | 1.0 | 0.164 | 4.3 | 3.3 | 10.7 | 11.1 / 11.9 | undecidable (integer grid) |
| 〰 MS Gothic | 47 | 0.93 | 0.423 | 10.0 | 10.5 | 7.1 | 14.0 / 19.7 | neither / undecidable |
| ⁓ U+2053 Roboto Italic | 351 | 0.65 | 0.406 | **2.1** | 3.9 | 2.0 | 3.2 / 3.3 | nearest to vertical shift (1.07 periods) |
| ⁓ U+2053 Roboto | 351 | 0.68 | 0.414 | 2.7 | 3.4 | 4.0 | 5.3 / 6.0 | ambiguous, near vertical shift |
| ⁓ U+2053 Times New Roman | 280 | 1.66 | 0.305 | 10.0 | 16.0 | 21.2 | 20.8 / 28.5 | neither (tapered) |
| ≀ U+2240 Segoe UI Symbol (axes swapped) | 266 | 0.71 | 0.490 | 7.7 | 2.8 | 6.8 | 11.9 / 10.1 | normal offset |
| ~ U+007E Constantia | 242 | 0.42 | 0.491 | 4.0 | 4.5 | 3.7 | 5.1 / 5.4 | cannot tell (slope too small) |

Python-only screening over the 877 analysable outlines (slice based, first order; [Measured]): median `rV`
(gap variation / mean gap) and `rN` (normal-offset residual / mean gap) per code point: U+3030 0.108 / 0.030;
U+301C 0.118 / 0.092; U+FF5E 0.218 / 0.259; U+223F 0.406 / 0.185; U+2053 0.080 / 0.148; U+007E 0.108 / 0.149.
So U+3030 glyphs are the most consistently normal-offset and U+2053 the most inclined to vertical shift.
Tildes (U+007E, U+02DC, U+0303) mostly have `rV` about `rN`: with low slope the two models agree to first
order and the test has no power (Constantia above). Thinnest per ink height among sine-like glyphs with at
least 0.9 periods (screen, vertical-gap mean / H): U+007E Walbaum Display Light 0.166, U+223F Lucida 0.173,
U+3030 MS Mincho 0.185, U+3030 Yu Mincho / Yu Gothic 0.231 (normal width 0.188).

**Flags.**
- **Exact vertical-shift edges: none found.** Closest: Roboto Italic ⁓, residual 2.1 % of H, but its edges
  are 3.2 % of the amplitude from a sine, the band is thick (w/H about 0.4) and the vertical gap still varies
  150 to 161 (7 %); it also has only 1.07 periods and a mild slope (0.65), so the models barely separate.
- **Edges exactly sinusoidal: none.** Lowest edge deviation 3.2 % of the amplitude (Roboto Italic ⁓);
  〰 Yu Mincho 5.3 / 5.9 %.
- U+2307 (WAVY LINE) and U+2E3C fail the slice test (not single bands) and were not analysed further.

## Optional PowerPoint check

Skipped (stream WP covers it). Visual sanity only: slide 59 of the deck shows 〰 starting and ending at crests
with two periods, consistent with the outline above.

## Other things noticed

- Yu Mincho is a Microsoft Office cloud font, present only as the cached `...\FontCache\4\CloudFonts\Yu
  Mincho\31868023978.ttf` (Regular). On a machine without it, the fallback glyph differs: Yu Gothic's 〰 is
  identical within 2 units, MS Mincho's is a coarse hinted outline, Meiryo's is a non-sinusoidal zig-zag.
- Yu Gothic's 〰 is one outline across all 9 faces, so weight does not change the geometry.
- 〰 is not node-symmetric: the left trough (x 287 to 512) uses 3 quadratics, the right trough (1313 to 1536)
  one. [Heuristic] That is plausibly the source of the worst in-between spine error near x = 1408.
- The cached font maps U+301C and U+FF5E to the same glyph `uni301C`; it is about 1.10 periods, normal-offset
  screen residual 20 %, spine 5.5 % of A: not a candidate.
- Caveats of the sweep: Wolfram fits for the shortlist use integer-rounded slices (3 to 4 unit sample steps,
  6 % end trim); for small outlines (MS Mincho H = 35) the integer grid limits the conclusions.
- A scratch script named `inspect.py` shadows the stdlib module and breaks `import fontTools`; keep scratch
  scripts off stdlib names.
