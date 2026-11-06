start: reading com.py, numpy/PIL/scipy ok under py
step1: make.py exports ctrl/oval/rect/bez/grid at 7680x4320, params RX30 RY60 FOV120 tag a
step2: lib.py/an1.py: ctrl 4-Bezier-like 8th harmonic .16px; oval and Bezier freeform give IDENTICAL pts; conic fit RMS oval .18 vs ctrl .16 px (R~1200px). next: homography from rect, compare candidates a/b/c
step3: tag a done (oval best matches 4-Bezier; ctrl-point Bezier off 50px). tag b: RR=200 SC=12 LW=0.5 RX20 RY50 FOV120
done: report written notes/3d-rotation-B-conic.md
