# 3-D Rotation in desktop PowerPoint: storage and projection formula

Backend: PowerPoint 16 via COM (pywin32); numpy/scipy/PIL for fitting. Wolfram not used.
Scripts and renders: `C:\Users\jason\AppData\Local\Temp\claude\C--dev-Powerpoint-lean\c222b849-70f5-4b01-ad09-a19ea61d2b9d\scratchpad\3d-A\`.
Everything is MEASURED unless labelled (inferred).

## 1. File format

```xml
<a:scene3d>
  <a:camera prst="perspectiveFront" fov="5400000">          <!-- fov omitted = preset default -->
    <a:rot lat="1800000" lon="20370000" rev="21000000"/>    <!-- rot omitted = preset's own -->
  </a:camera>
  <a:lightRig rig="threePt" dir="t"/>
</a:scene3d>
```
- All angles and fov are integers in 1/60000 degree; lat/lon/rev in [0, 21600000).
- COM `Shape.ThreeD`: `RotationX/Y/Z, FieldOfView, Perspective, PresetCamera, SetPresetCamera(1..25), Depth, Z, ...`.
  COM floats (single precision) are rounded to 1/60000 deg in the XML, with
  **lon = -X, lat = Y, rev = -Z (mod 360)**. E.g. X=10 -> lon=21000000; Y=30 -> lat=1800000; Z=10 -> rev=21000000.
  COM reports angles wrapped into (-180,180].
- Angles are arbitrary reals, not whole degrees (12.345678 -> 20859259; 20.5, 33.3, 10.25 stored faithfully). Any value
  is accepted and wrapped mod 360 (even 1e6). Y beyond +-90 accepted (100, -100).
- FieldOfView accepted on [0, 120] degrees inclusive (0.05, 119.99, 120 ok; 120.5, 121, 150 raise "out of range"),
  arbitrary reals. Defaults: 45 (non-legacy/ortho), 65 for legacyPerspective* presets. fov=0 accepted (not rendered-tested).
- `Perspective=True` sets prst `legacyPerspectiveFront` (fov 65); setting rotations keeps the prst and adds `<a:rot>`.
  `SetPresetCamera(k)`: 1-9 legacyOblique*, 10-18 legacyPerspective*, 19 orthographicFront, 20-25 isometric{TopUp,
  TopDown,BottomUp,BottomDown,LeftUp,LeftDown}. COM cannot select other prst (perspectiveFront, perspectiveRelaxed...);
  those were tested by patching the XML of my own saved copy and reopening it.
- Presets carry implicit rotations COM reports as X/Y/Z: isometricLeftUp (X,Y,Z)=(-45,-35,0) (35, not 35.264),
  isometricTopUp (45.281,-35.396,-60.162). Rendering matched the formula with those COM angles (resid <= 0.15 pt).
  legacyOblique*/legacyPerspective* presets 1-18 render the flat outline untransformed (rot=0).
- UI ranges/steps of the Format Shape pane were NOT inspected (only COM limits above). (uncertain)

## 2. Projection formula (fitted)

Slide points, y down. c = centre of the shape's unrotated bounding box, q = (x-cx, y-cy, 0). lat, lon, rev as stored:

    M = Rz(-rev) . Rx(-lat) . Ry(-lon)          (lon applied first, rev last)
    Rx(a) = [[1,0,0],[0,cos a,-sin a],[0,sin a,cos a]]
    Ry(a) = [[cos a,0,sin a],[0,1,0],[-sin a,0,cos a]]
    Rz(a) = [[cos a,-sin a,0],[sin a,cos a,0],[0,0,1]]
    (X,Y,Z) = M q
    perspective: slide point = c + d/(d - Z) * (X, Y)
    orthographic: slide point = c + (X, Y)
    d = k / tan(fov/2),   k = 453 +- 1 pt, independent of shape size, shape position and slide size

In COM terms: lat = Y_com, lon = -X_com, rev = -Z_com. Points with Z>0 (toward viewer) are enlarged.
No rescale or recentring: the bbox centre is the fixed point; all angles 0 leaves the outline unchanged (<=0.15 pt).
The projection centre is the shape's bbox centre, not the slide's (shape at 4 positions, same d).
k: 453.54 pt = 16 cm = 5,760,000 EMU is consistent but unproven (inferred). Individual fits at fov 90-120:
452.3-453.9; low-sensitivity (small fov) fits 453-458. Exactness of d = k/tan(fov/2) cannot be separated from ~0.2 pt noise.

Quirk: cameras with prst `legacyPerspective*` (what COM `Perspective=True` creates) IGNORE `rev`: with lat=-30, lon=25 and
rev = 0, 20, 90 the renders are identical and fit the model with rev=0 (res 0.17 pt; with true rev the residual is 48-86 pt).
Non-legacy `perspectiveFront` and ortho/legacyOblique cameras honour rev. So via COM, perspective + Z rotation is
lost unless the XML is patched (UI behaviour not tested).

## 3. Method and residuals

Black convex freeform pentagon (300x200 pt box, vertices (60,0),(300,40),(260,200),(120,200),(0,120)) on white, exported
with Slide.Export at 4 px/pt; vertices from convex hull + line fits to edge pixels (inward bias about 0.13 pt).
Angle order/signs found by exhaustive search (6 orders x 8 signs) on ortho data; d fitted per run. Max vertex residual, pt:

| setting | camera | fitted d | max resid (pt) |
|---|---|---|---|
| Y=30 | ortho | - | 0.215 |
| X=30 | ortho | - | 0.125 |
| Z=30 | ortho | - | 0.073 |
| X=30,Y=20,Z=10 | ortho | - | 0.138 |
| X=40 | legacyPersp fov 45 | 1090.6 | 0.099 |
| Y=40 | legacyPersp fov 45 | 1082.9 | 0.206 |
| Y=40 | legacyPersp fov 90 | 453.7 | 0.223 |
| X=-50,Y=35 | legacyPersp fov 120 | 261.2 | 0.153 |
| Y=60 | legacyPersp fov 65 | 712.4 | 0.233 |
| lat 40 | perspectiveFront fov 20/45/90/120 | 2589/1081/453.2/261.2 | 0.19-0.25 |
| lat -30,lon 25,rev 20 | perspectiveFront fov 20/45/90/120 | 2574/1105/453.9/261.2 | 0.09-0.21 |
| (lat,lon,rev)=(60,40,20),(50,50,30),(40,-60,170),(70,20,-45),(-65,35,100); shapes 0.5x-1.5x; slides 720x540, 960x540, 1280x720, 1600x900 | perspectiveFront fov 90-120 | k=452.3-455 | 0.09-0.27 (0.64 at lat 70-75) |
| isometric presets 20,22,24,25 | ortho (COM angles) | - | 0.09-0.15 |

## 4. Projective?

Yes. For a flat shape (X,Y,Z)=Mq is linear in (x,y), so (x,y) -> d/(d-Z) (X,Y) with Z affine in (x,y) is a homography
(affine when ortho). Tests with the pentagon: a homography fitted from 4 vertices predicted the held-out vertex to
0.02-0.2 pt in most cases (0.6 pt and 1.7 pt in two ill-conditioned subsets: fov 90 lat 70; fov 120 lat 50/lon 50/rev 30).
Edge pixels deviate from the straight vertex-to-vertex chord by <= 0.17 pt in three settings. Curved outlines not tested.

## 5. Uncertain / not done

- Exact k (about 453) and its origin; fov dependence checked only 20-120 deg.
- UI step/range not inspected; UI-created cameras may be non-legacy (rev honoured then).
- Extrusion/bevel (`sp3d`), text, groups, shapes with `xfrm rot` or flips combined with 3-D: not tested.
- Noise ~0.1-0.25 pt; angle exactness established at storage level and by fits at COM-set arbitrary angles.
- Several unsaved scratch presentations (Presentation N, created by my scripts) may still be open in PowerPoint; I could
  not tell them from other agents' presentations, so did not close any.
