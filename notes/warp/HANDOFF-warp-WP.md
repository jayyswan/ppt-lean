step0: read plan+F1, setup scratch
step1: new pres wp.pptx, textbox w/ 〰, Yu Mincho set via Home font dropdown list (typing in box did not commit); size 36, no autofit, no wrap
step2: Warped Circle on 1x〰 at 72pt box 4in: whole-row polar map reproduced corners 0.055pt, between 0.87pt (0.61% R); pickle c1.pkl
step3: Circle rows 1-4 and Arch Up rows 1,2,4 baked (pkl circ_n, up_n). corners<=0.08pt, between<=0.9pt
step4: Arch Down rows baked; Wolfram fits done (flat edges, normal-offset model h=1.304 A=5.588 resid .09pt, rose fits). next: font verify, (d) Text Outline, (e) freeform warp, (f) ends, fragment
step5: (d) Text Outline 6pt on warped circle n=1 (no fill): stroke is constant 6pt in plane, centred on warped outline (inscribed dist median 2.97pt, range 2.78-3.84; PNG export 5px/pt). Merge ignores outline (hausdorff to unstroked bake printed in note)
step6: UI Fragment (Merge Shapes ▸ Fragment, rectangle dummy) on warped+stroked duplicate gave 5 freeforms. now (e) Transform on freeform
step7: (e) Transform gallery is enabled on a freeform from fragment; applying Warped Circle sets WarpFormat=10 but 73 nodes unchanged (text empty). (f) ends: circle ends coincide on theta=180deg ray r 130.63..144; arch up ends at 9 and 3 o'clock same r range; arch down r 32.4..50.45. next: Light/Demibold weights quick test, cleanup, write note
step8: EMF paste-as-picture + convert: stroke stays a 6pt line on 118-node freeform (not a filled outline). weights: Yu Mincho Light selectable but outline identical to Regular. closing wp.pptx w/o saving; writing note
step9: note written to notes/warp/WP.md; wp.pptx closed unsaved; done
