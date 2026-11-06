# 3-D rotation with perspective: is the outline an exact projective image? (probe B)

Backend: all pixel numbers are Python 3 (numpy/scipy/PIL via `py`) on PNGs exported from desktop PowerPoint 16 via COM
(`Slide.Export`). No Wolfram used (no symbolic step was needed). Scripts and images:
`C:\Users\jason\AppData\Local\Temp\claude\C--dev-Powerpoint-lean\c222b849-70f5-4b01-ad09-a19ea61d2b9d\scratchpad\3d-B\`
(make.py, lib.py, an1-an5.py).

## Settings
Own presentation, 960x540 pt slide, blank layout, white background. Shapes centred at (480,270), no fill, black outline.
`ThreeD.Visible=-1; Perspective=-1; FieldOfView=120` (UI/COM max is 120; 130+ raises "out of range"); then RotationX/Y/Z.
* Run a: R=150 pt, 2 pt line, export 7680x4320, RX=30 RY=60 RZ=0.
* Run c (main): R=170 pt, 0.5 pt line, export 11520x6480 (12 px/pt, R=2040 px), RX=15 RY=40 RZ=0.
  (Run b with RX20 RY50 R=200 clipped off the slide and is discarded.)
Shapes per run: control oval (no 3-D); oval 3-D; square (rectangle preset, same bbox) 3-D; freeform made of 4 cubic Beziers
with k = 0.5522847 (corner nodes) 3-D; freeform polygon "grid" (square outline with edge midpoints plus 8 spokes to the centre) 3-D.
Outline pixels: midline of the stroke by darkness-weighted centroid along 3600 rays from the bbox centre (sub-pixel).
Note: PowerPoint scales the stroke width with depth (line is drawn as 3-D geometry), so noise floor is ~0.1-0.3 px.

## Results (px; run c at 12 px/pt)
General-conic fit (Sampson-refined LSQ), RMS residual:
* control circle (no 3-D): 0.315 px; 8th harmonic of residual 0.35 px amplitude (4-fold Bezier signature; see below)
* 3-D oval: 0.316 px (disc b^2-4ac < 0: ellipse-like); 3-D 4-Bezier freeform: 0.316 px, **pixel-identical** to the oval.
Conic fit is therefore as good as the control's own circle fit; the conic fit cannot tell conic from a 4-Bezier-projected curve
(the difference is ~1.3 px, comparable to its noise).
Run a: control 0.162, oval 0.182 px.

Rectangle: 4 edges straight (max inlier deviation 0.1-0.5 px, one edge 1.1 px at tolerance limit). Grid polygon
(corner-to-edge-midpoint-to-corner and spokes): drawn lines lie on the lines predicted by the homography fixed by the 4 rect corners
within rms 1.6 px of 3000 px (mean offset 1.5 px, i.e. 0.05%; corner estimates from mitred stroke intersections limit this).
Spokes through the centre: rms 0.65 px, max 1.5 px. So polygons behave as a true homography (straight edges stay straight, interior
points map by the same H).

Candidate curves, H from the 4 square corners (run c, distance of measured oval midline to candidate; 3600 pts):
| candidate | mean | rms | max |
|---|---|---|---|
| (a) exact H-image of true circle | 0.306 | 0.428 | 1.307 |
| (b) exact H-image of the 4-Bezier (k=0.5523) | 0.147 | 0.187 | 0.551 |
| (c) 4 Beziers with projected control points | 18.4 | 29.7 | 76.9 |
Same with H free (8 dof LSQ fit to the oval): true circle rms 0.325 (max 0.91); 4-Bezier rms 0.115 (max 0.40).
Run a gave the same ordering (0.188 vs 0.103; (c) 12 px mean error). The control (no 3-D) ordering is weak
(0.33 circle vs 0.27 Bezier) because its noise floor dominates.

## Verdict
* The image is NOT an ordinary-Bezier-with-transformed-control-points curve ((c) is off by tens of px).
* It is an exact projective image (to ~0.1-0.2 px of 2000 px, ~1e-4 relative) of the oval's **4-cubic-Bezier representation**,
  not of the true circle (circle misses by up to ~1.3 px = the known 2.7e-4 R radial error of k=0.5523 Beziers, best explained by (b)).
  I.e. PowerPoint maps the curve pointwise by a true homography (rational-quadratic-in-t-of-cubic pieces) and renders it finely
  (no coarse tessellation visible). Because the oval itself is 4 Beziers, its 3-D image is only an approximate conic
  (within ~3e-4 R), exactly a conic only for the idealised circle.
* The oval and the explicit 4-Bezier freeform render identically -> the oval is internally those 4 Beziers (k=0.5523 fits).
* Polygons: true homography, straight edges.

## Uncertainty
* Only perspective sign/orientation pair tested: RX/RY combos (30,60) and (15,40), FOV 120, RZ=0; not other FOV values or off-centre shapes.
* Exactness limited by stroke-midline extraction (~0.1-0.3 px); a perspective effect below ~0.3 px (1.5e-4 R) can't be excluded,
  e.g. fine tessellation or a slightly different k.
* H was inferred from the square's corners (assumes same camera for all shapes with same bbox); free-H fit gives same conclusion.
* The line is rendered with perspective-varying width, so only the centre-line (not the stroke edges) was compared.
