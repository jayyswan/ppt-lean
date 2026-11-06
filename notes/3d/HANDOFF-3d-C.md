start
route1 merge: result freeform, geometry in pre-3D plane coords, scene3d retained (not baked)
route2: paste EMF (dt2)=picture w/ EMF+ DrawImage raster; paste SVG(dt12)=svg wrapping base64 PNG; dt11 keeps shape+3D
route2 ungroup EMF pic -> group of AutoShape rect + 2 raster pictures (no freeform); SVG graphic not ungroupable (raster inside)
route3 slide/shape Export EMF/SVG: 3D shapes raster (StretchDIBits 1757x1119 / base64 PNG), flat control is vector bezier svg
route4 SetPosition on 3D prst -> freeform in PRE-3D plane coords (rect 5 nodes, oval 13 nodes=4 bezier), scene3d retained; ExecuteMso EditPoints fails even flat
route pdf: 3D shapes are Image XObjects, flat is vector. next: fit raster render to homography/conic
fit done: raster render is projective image: H fit; oval conic resid max 0.05pt. remaining: ortho/depth emf check, flat-primary merge, notes
