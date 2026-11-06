# HANDOFF — Jacobi amplitude programme, agent R2 (Serret + catalogue + extension)

Brief: PLAN-jacobi-R2-serret-and-extensions.md. Deliverable: NOTES-jacobi-R2.md.
Constraint: research only, no .lean edits.

## Progress log
- [start] Created handoff log. Next: read PLAN-jacobi-00-overview.md and PLAN-jacobi-R2-serret-and-extensions.md in full.
- [read] Read both PLAN files in full. Next: survey repo (Defs.lean constructors, Jacobi.lean, existing scripts).
- [survey] Repo listed. Reading Defs.lean (constructors) and Jacobi.lean for the drawable class and current amplitude results.
- [context] Read Defs.lean constructors, Jacobi.lean results, overview script, R1a brief. Starting literature search on Serret curves.
- [lit1] Found primary Serret sources (JMPA 1845 memoir p.257, Note p.421, 1846 geometric theory p.89; Liouville report p.290; Serret 1843 Cassini p.145). Extracted generating-triangle construction and moduli k^2=n/(n+1). Next: fetch modern secondary sources and derive explicit parametrisation.
- [lit2] Modern secondary: Morgan (1903), Tamiozzo arXiv:1912.00204, Lipkovski-Popelensky 2020. Cassini ovals (Serret 1843) realize every modulus via b/a. Next: derive+verify Serret parametrisation symbolically and numerically.
- [verify] Serret rederivation+30-digit check done (R2-01): arc=sqrt(n)F(alpha,k), k^2=n/(n+1), true for all real n>0. Affine lemniscate scaling destroys single-F (R2-03), so lemniscate gives only c=1/2. Cassini arc differential derived; testing single-F vs two-F. Next: literature on Cassini/Serret explicit forms, then write notes.
- [verify2] R2-05: n=1 curve is exactly the focus-(1,0) lemniscate; F(pi-a)=2K-F(a); gamma injective on [0,pi] for n in {0.5,1,1.7,2,3}; half-length=sqrt(n)2K. R2-04: general Cassini arc is hyperelliptic (-1/4), not elliptic. Writing NOTES-jacobi-R2.md now.
- [done] NOTES-jacobi-R2.md written (A/B/C). R2-06 independent re-check passed (K(1/2), lemniscate quarter, modulus map, arc identity). No .lean file touched. Scripts: R2-01..R2-06 in archived files/jacobi-scripts/.
