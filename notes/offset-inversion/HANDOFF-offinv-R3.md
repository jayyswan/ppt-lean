# R3 separation — progress log

- Read PLAN §0/§1/§R3, sheared-sine §3b, R0, R1, R2, Defs/Offset/BoxOffset. Wrote skeleton of `notes/offset-inversion/R3-separation.md`.
- Ran Wolfram cell 1 (Q1 closure: exp `{0,0}`, `(t,e^t)` `{0,0}`, trig `{0,0}`, affine `{0,0}`, R0 derivative identity `0`).
- Ran Wolfram cell 2 (Q3: `F' = cosh^2 u - d sech u`; `gd` identity `0`; branch points `iπ(m+1/2)`; residue `-i/2`; monodromy `π`; `dF` residues `{1/2,-id,id}`).
- Ran Wolfram cell 3 (Q2 sample `sin x = 2^x`; L2 quartic residual `0`; `F(3)=51.19` vs `e^6/8=50.43`).
- Ran a follow-up Wolfram cell confirming the corrected `w`-form relation has residual `0`.
- Filled `R3-separation.md`: Q1 normal form proved (`offset` warning resolved: `ln u` is a reparametrisation); Q2 difference-of-graph-functions class; Q3 separation proved for `d ≠ 0` via finite log branch points; Q4 depth ≤ 2. Added `d = 0` degeneracy as `[Open]`. Final pass.
