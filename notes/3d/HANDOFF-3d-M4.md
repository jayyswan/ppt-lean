start M4
step1: lib.py written
step2: t1.py basic shapes: 3D on all; projection centre = geometry bbox not frame for blockarc/chord (to fit)
step3: pictures (transparent, cropped, opaque): 3D works, homography of (cropped) frame, centre=frame centre, confirmed IoU~1. blockarc/chord: centre=geometry bbox not frame
step4: textbox/wordart/group/svg ok (frame homography; group rigid plane about group bbox centre); table & chart frame: ThreeD.Visible stays 0 (ignored)
step5: group XML scene3d in grpSpPr; interactions (rotation/flip) test t5 next
step6: 2D rotation & flip applied to plane BEFORE 3D camera (camera in slide axes): hypothesis B rms<0.01pt, A rejected. Next effects t6
step7: effects t7 rendered grid7.png; analysing shadow/glow/reflection spaces
step8: shadow offset ~in-plane (IoU .84 vs .35 screen); reflection appears to shift projection centre (shape moved) -> testing centre fit w/ boundary cost
step9: glow ~unchanged centre; shadow shifts image ~2pt; reflection ENLARGES/shifts 3D image of shape itself ~10% (mechanism open); soft edge shrinks. next: glow screen-vs-plane, then text/chart-EMF/group/line
step10: glow is in-plane (compressed vertically at lat=70). ThreeD has ProjectText (keep text flat?), Z, IncrementRotation*; TextFrame2.ThreeD exists. testing t13
step11: ProjectText=0 <=> bodyPr flatTx (Keep text flat; COM default -1=project); TextFrame2.ThreeD = text-only scene in bodyPr, but aliases shape scene when shape 3D on; warp+3D ok. next: chart->EMF picture + trendline, 3D chart types, table cell bevel
step12: chart pasted as EMF picture (type 13): 3D ok, frame-centre homography rms 0.18pt, content (incl trendline) rotates as plane. Closed my t4 chart workbook lock.
step13: chart native 3D (Rotation/Elevation/Perspective on 3D chart types; no trendlines in 3D line); table: shape ThreeD ignored, cell bevel COM fails, table-as-EMF-picture accepts 3D. next: GetEnabledMso probes, group/nested, line cases, final write
step14: GetEnabledMso/UI probing skipped (active window belongs to another agent; selection needs it) -> UI pane availability [Open]. next t18 group nesting/ungroup
step15: groups: child 3D kept in flat group; group 3D overrides child 3D (bbox identical); ungroup copies group scene to each child; 2D group rotation precedes 3D. next: centre rule precise (chord/blockarc/moon no stroke)
step16: centre rule confirmed: bbox centre of drawn path (chord/blockarc rms 0.15 at inkC vs 8 at frameC); arc adj quirk. next t21: pic crop-to-shape, connectors, smartart, ink, wave details; then write
step17: freeform bezier: projection centre = control-point hull bbox centre (=frame), NOT curve bbox (rms .19 vs 2.9). SmartArt ThreeD ignored; connectors ok. redo crop-to-shape
step18: deliverable written notes/3d/M4.md; done
