start P3: read plan
step1: harness works: Chart.Export(path,'SVG') gives exact paths (series=cubic C, trendline=L/dash path); Slide.Export EMF lacks series (EMF+ only). lib.py+t*.py in scratchpad P3
step2: findings so far: smooth scatter = uniform Catmull-Rom (mirrored ends) cubic Beziers, resid<0.7px; trendlines lin=1 straight seg, others polyline ~720 pts at ~1px x steps y snapped to px; MA = polyline thru nodes. Chart.Export SVG works only 1st chart per presentation -> new presentation per chart
step3: trendlines lin/exp/log/pow/poly2-6 match standard LS fits (lin in y, exp ln y, log ln x, pow loglog) within 1px (max .8-1.0, rms .4 px, numpy); MA polyline thru k-point avgs. NOTE: reading Trendline.DataLabel.Text via COM crashes PowerPoint; closing last presentation quits PPT -> keep a keeper presentation
step4: log x axis base2/10: trendlines (all types) are fit in linear x then drawn as 720-pt polyline on log axis, resid<=1px; linear tl on log axis is a curve a*2^u+b
step5: gallery g1.py done. Trendline refused (COM) on stacked line/area, radar, pie, doughnut, surface, 3D, waterfall; OK on line,area,col,bar,scatter,bubble,stock HLC/OHLC
step6: pie sectors = 1 cubic Bezier per <=~90deg arc (cat b); radar = straight polygon, polar map; bubble/markers circles = 4 cubics; surface exported as PNG image (raster)
step7: radar: polar map theta=2*pi*i/n clockwise from top, r affine in value (axis min..max), straight chords, vertices snapped to integer px (resid<=1px); radar 360 cats linear data -> one-turn Archimedean spiral POLYGON (cat c)
step8: stacked line + Smooth=True: nodes exactly (A+B), Catmull-Rom Beziers; cosh-type 2^x+2^-x on 61 cats h=.1: spline vs ideal max .0029 (3.5e-4 rel) -> cat c, O(h^4); fill-handle feasibility of small h open. Log y settable via COM on both axes (UI? memory says no). Date axis (CategoryType=3) positions by date.
step9: date axis: trendline fits vs date serial (measured); error bars fixed/pct/stdev(sample sd, centred at mean)/sterr = straight lines+caps
step10: pie arcs <=90deg cubic rel dev<=2.75e-4; MA = trailing k-avg polyline; chartex: box/funnel straight, sunburst arcs C2/C4, treemap/pareto/hist export empty (hist crashed PPT -> autorecovered pres appeared)
step12: wrote notes/ppt-curves/P3.md; done
