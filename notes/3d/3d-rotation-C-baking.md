# Can a 3-D rotated shape be baked into flat 2-D geometry? (probe C)

Backend for all measurements: desktop PowerPoint 16.0 via COM (pywin32); numerics in Python numpy/scipy
(no Wolfram needed). Scripts: `C:\Users\jason\AppData\Local\Temp\claude\C--dev-Powerpoint-lean\c222b849-70f5-4b01-ad09-a19ea61d2b9d\scratchpad\3d-C\p*.py`.

Test shapes: rectangle 200x120 at (100,100) and oval 200x120 at (400,100), `ThreeD.Visible`, RotationX=20,
RotationY=50, Perspective on, FieldOfView=80, Depth=0 (XML: `legacyPerspectiveFront`, fov 4800000,
`rot lat=3000000 lon=20400000`). Slide 960x540 pt.

## Verdict
No route turns the perspective image into vector geometry.
- Merge Shapes and Edit Points (node touch) give a freeform of the *untransformed* plane outline and keep
  the 3-D scene on it. The effect is not baked, only carried along.
- Every route that does apply the 3-D transform (paste as EMF/SVG, Slide/Shape.Export EMF/SVG/WMF, PDF) outputs a
  *raster*. Ungrouping the EMF gives no freeforms.
- The rendered image is an exact projective map to within render resolution (below), so the exact outline is
  homography(plane outline), but PowerPoint never hands it back as nodes.

## Route 1: Merge Shapes (Union/Combine/Intersect/Subtract/Fragment, with a 60x40 rect at (150,120))
`ShapeRange.MergeShapes(mode, primary)` works. Result is always `Type=5` freeform with `<a:custGeom>` and
**`<a:scene3d>` still present** (3-D visible, same camera), `ThreeD.Visible=-1`. Geometry is in the pre-3D plane.
- Rect union with small rect: 4 nodes (100,100),(300,100),(300,220),(100,220), all line segments; bbox 100,100,200,120.
- Rect intersect small rect: nodes (150,120),(210,120),(210,160),(150,160): the small rect itself, i.e. the
  intersection was computed in the flat plane (the 3-D primary's perspective did not clip it).
- Oval union: XML path = 4 `cubicBezTo`, e.g. moveTo (1270000,0), cubic (1971402,0),(2540000,341159),(2540000,762000):
  exactly the flat oval's 4 Beziers (13 nodes via COM). No projective change.
- Fragment: 2 shapes, each carrying scene3d.
- Flat primary + 3-D secondary (union of A(100,100,200,120) and B(150,150,200,120) with B rotated): result is a flat
  8-node freeform, bbox 100,100,250,170 (plane coordinates), `scene3d` absent. The 3-D of the non-primary is silently
  discarded and also not baked.
=> Not baked. Merge treats a 3-D shape as its flat outline; later turning `ThreeD.Visible` off gives that outline.

## Route 2: copy, Paste Special, ungroup
`PasteSpecial` DataType codes found by trial: 2 = EMF picture, 11 = shape (keeps 3-D, type 1 autoshape), 12 = SVG
graphic (Type 28), 3/13/14 invalid.
- EMF (dt 2): `Picture` 206.6x130.6 pt; the saved `image*.emf` is 2.1 MB (rect) / 4.0 MB (oval) and contains
  only `EMR_STRETCHDIBITS`/`BITBLT` + EMF+ `DrawImagePoints` (0x401B) with an image object (0x4008): **raster**
  (1757x1119 bitmap). `Picture.Ungroup()` succeeds and yields a Group of an `AutoShape` (plain rect at the picture's
  bbox, a background) + 2 `Picture`s (raster layers). No freeforms. Second ungroup: same 3 shapes.
- SVG (dt 12): `ppt/media/image*.svg` (5 KB / 11 KB) = `<image xlink:href="data:image/png;base64,...">` inside a
  clip group. **No `<path>`.** `Ungroup()` raises "can only be accessed for a group", and ExecuteMso
  Ungroup/ConvertToShape fail (and there is nothing vector to convert anyway).
=> Not baked.

## Route 3: Export
- `Slide.Export(path,"SVG")`: error, no installed converter. `"EMF"` and `"WMF"`: ok but raster for 3-D shapes.
- `Shape.Export(path, 6)` writes real SVG. Control (flat oval):
  `M533 480C533 435.817 592.77 400 666.5 400 740.23 400 800 435.817 800 480 800 524.183 740.23 560 666.5 560 592.77 560 533 524.183 533 480Z`
  (4 cubic Beziers). The 3-D rect/oval: same `<image ... base64 PNG>` wrapper, no path (277x175 px for the rect).
- Slide EMF record census: flat control has `EMR_BEGINPATH(59)`, polybezier records, 2.8 KB total, EMF+
  FillPath/DrawPath (0x4014/0x4015). With 3-D shapes: 8.5 MB, 4 `STRETCHDIBITS` (1757x1119 px), only EMF+
  `DrawImagePoints`. No vector path records for the 3-D shapes.
- `SaveCopyAs(...,32)` PDF: flat oval is `m ... c c c c h f*` (4 Beziers); both 3-D shapes are `Image6/Image8 Do`
  with `208.74 0 0 132.78` matrices (raster). XPS: SaveCopyAs fails.
- Also raster: orthographic camera, RotationZ-only camera, extrusion Depth=36 + bevel (all slide EMFs have
  STRETCHDIBITS, no path). Plain 2-D `Shape.Rotation` stays vector (1.9 KB EMF).
=> Not baked; any scene3d means raster.

## Route 4: Edit Points / Nodes
- `Shape.Nodes.Count` works on a 3-D preset (rect 5, oval 13) but `Nodes.Item(i).Points` throws until the shape is
  a freeform. `ExecuteMso("ObjectEditPoints")` fails from COM even for a flat shape.
- `Nodes.SetPosition(1, x, y)` (the `to_freeform` trick) converts the preset to a freeform (`Type 5`) and **leaves
  `ThreeD.Visible=-1`**. Nodes are the plane outline: rect (100,100),(300,100),(300,220),(100,220),(100,100) as
  lines; oval 13 nodes (4 curve segments, SegmentType=1), e.g. (144.77,100),(200,100),(255.23,100),(300,126.86)...
  in unrotated coordinates. `Left/Top/Width/Height` stay 100,100,200,120 (not the projected bbox 92.4..298.2 x
  92.2..221.8).
=> Not baked: Edit Points edits the pre-3D outline.

## Geometry of the actual render (what a baked result would have to equal)
Rendered at 5 px/pt (`Slide.Export` PNG 4800x2700, black fill, no outline), boundary = 0.5-coverage contour via
contourpy (numpy/scipy; resolution about 0.1 pt).
- Rect image corners (intersections of fitted edge lines): TL (92.322,145.822), TR (298.480,92.116),
  BR (283.564,170.987), BL (109.907,222.079). Edges are straight: line-fit max residual 0.043 pt (0.2 px) over
  400-1000 points per edge.
- Homography from the 4 corners (plane to slide pt):
  [[1.47968, 0.41138, -72.349],[-0.28526, 1.26044, 86.898],[5.8989e-4, 2.0568e-3, 1]].
  Predicted images of plane edge midpoints (199.995,117.772),(290.411,134.783),(199.997,195.573),(101.896,187.340)
  lie within 0.04-0.10 pt of the rendered contour; shape centre (200,160) maps to (199.996,159.99), so the
  perspective is centred on the shape centre.
- Oval: rendered boundary (2847 points) fits one conic with max Sampson distance 0.050 pt, rms 0.015 pt,
  B^2-4AC < 0 (ellipse). Mapping the plane ellipse (centre 500,160, semi-axes 100,60) by the homography above,
  shifted by +300 in x, predicts the contour within max 0.085 pt, rms 0.039 pt. So the view of an oval is exactly
  a projective image (an ellipse), consistent with a single homography (numpy SVD DLT).

## Remaining uncertainty
- Only one camera setting was fitted (fov 80, XML lat 50 / lon 340). Other presets and legacy vs true perspective
  were not fitted; render resolution caps checks at about 0.05-0.1 pt.
- No UI driving. Ribbon commands (Edit Points with a real selection, Graphics "Convert to Shape", Save as Picture
  then Convert) were only tried through `ExecuteMso`, which failed even for flat shapes here. They would at most
  reproduce the raster or flat results seen, since no vector projected path exists in any output.
- Not tested: Merge with the 3-D shape inside a group; tracing the raster as ink.
- Practical bake: compute the projected outline yourself (homography above) and build a `BuildFreeform` with
  Beziers. Not tested how closely 4 cubic Beziers reproduce the projected ellipse.
