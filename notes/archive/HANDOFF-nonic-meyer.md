# HANDOFF-nonic-meyer

Progress log for PLAN-nonic-meyer.md. One line per step.

- [setup] Read PLAN, septicpaper_revised.tex, Basic.lean l.440-700, seed script. Created log.
- [numerics] Reproduced seed: r2=1 identity fails ~0.24-0.65%, r2>=3 always works. Found a np.polyval ordering bug in my test (fixed).
- [math] Exact rational collisions psi(rho_i)=psi(rho_j) are IMPOSSIBLE for deg psi<=6 (rank arg in Q[a,b]/(q(a),q(b))). Plan's suggested mechanism is flawed as stated.
- [math] KEY FIX: over R collisions are one linear condition each. Real collision psi -> explicit f with Q(f)=-2<0 and a positive vector. Hence {psi: Q|V_psi indefinite} is OPEN and NONEMPTY, so contains rational psi. Meyer then applies.
- [math] r2>=3 handled by dimension count with psi=x: positive index of W={Tr=0} is 8-r2<=5<6=dim V, so Q|V not pos def; not neg def either; indefinite (Meyer) or rational radical (zero).
- [numerics] mpmath high-precision confirms collision interpolation gives phi(w_j)=0 real, phi(z_c)=i, so Q(f)=-2 exactly.
- [examples] Found 3 monic irreducible integer nonics (r2=1,2,4). All have psi=x indefinite. Found rational isotropic vectors; computed phi (deg<=6), resolvent R=Y^9-p(Y) with deg p=6, c8=c7=0 exactly. 120-digit check: |y^9-p(y)|~1e-101, phi(beta)=y.
- [examples] Galois: all irreducible, disc non-square, each has a Frobenius transposition => group S_9. Cycle types include (9,),(8,1),(5,4),(2,2,2,2,1).
- [fix] Corrected an over-strong claim: rational collisions force psi constant only when Q(beta) has no cubic subfield (e.g. S_9); a shared cubic subfield is a loophole. Proof unaffected (uses real collisions).
- [lean] Created pptc/Pptc/Scratch/NonicMeyer.lean; final statement marked `sorry`; `lake_check` passes (only the expected sorry warning). Mathlib 4.33 has no Hasse-Minkowski/Meyer.
- [deliverable] Wrote NOTES-nonic-meyer.md (full proof) and nonicpaper.tex. Conjecture N is PROVED.
- [note] No LaTeX engine (pdflatex/latexmk/tectonic) found on this machine, so nonicpaper.tex was not compiled here.
- [lean] Dispatched subagents; formalization complete with ONE sorry (Meyer gap):
  * Pptc/NonicResolvent.lean (companion9 + charpoly root) -- sorry-free, lake_check OK.
  * Pptc/NonicRecovery.lean (steps 5-6 recovery) -- sorry-free, lake_check OK.
  * Pptc/NonicPowerLaw.lean (resolvent_powerLaw9, resolvent_y_Pconstructible9) -- sorry-free.
  * Pptc/Nonic.lean (`root_Pconstructible_of_rat_nonic_nonreal` general + `_sep`) -- one sorry in `exists_tschirnhaus9`. lake_check Pptc/Nonic.lean exit 0, single sorry warning at 31:8.
