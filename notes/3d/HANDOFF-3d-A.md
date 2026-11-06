start
a1 probe run
findings: xml units 60000/deg; COM X->lon=-X, Y->lat, Z->rev=-Z; Perspective prop, fov 65 default persp; presets 1-25 only
render.py (freeform pentagon, 4px/pt) works; run1.py collects tests; fitting next
fit: M=Rz(-rev)Rx(-lat)Ry(-lon) (cols; y down), persp x'=x*d/(d-z); d*tan(fov/2)~453 for 300x200 shape; resid<=0.23pt; next: vary size/pos
finding: with legacyPerspective* camera, rev (COM Z) is IGNORED by renderer (ortho legacyOblique honors it). d*tan(fov/2)~453.7 independent of shape size/position. next: patch XML w/ non-legacy prst via Presentations.Open
nonlegacy prst (perspectiveFront) w/ XML patch: model fits all lat/lon/rev + fov, res~0.2pt, k=d tan(fov/2)~453.x. next: precise k, slide-size dependence, write note
legacyPerspective ignores rev confirmed; fov range COM 0..120; angles any real, mod 360, 1/60000 deg. now testing presets then write note
