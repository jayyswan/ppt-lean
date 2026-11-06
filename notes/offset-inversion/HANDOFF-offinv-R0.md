# HANDOFF — offset-inversion R0 (foundations)

- read `PLAN-offset-inversion.md` §0, §1, §R0, L1, L2 (deliverable and downstream needs fixed).
- read `notes/offset-inversion-tangent-angle.md` (mechanism, parabola R, cusp-free window, open items).
- read `Pptc/Defs.lean` in full (constructors, `speed`, `unitNormal`, `offsetParam`, `arcLengthOf`).
- read `Pptc/Offset.lean` (module docstring, `offsetParam_zero`, `unitNormal_orthogonal`, `offsetParam_normal_eq_zero`, `offsetParam_dist_sq`, quintic recovery).
- read `Pptc/BoxOffset.lean` in full (`continuousOn_offsetParam`, four box wrappers, `offsetCuspAbscissa`).
- read `Pptc/Box.lean` (box edges, `isCompact_traced_arc`, `arc_*endpoint_Pconstructible`, `arcLength_*endpoint_Pconstructible`).
- read `Pptc/Jacobi.lean` Outlook (offset adds `−d·ψ`; `√Q_n/Q_k^{3/2}` interleaving).
- searched `Pptc/Basic.lean` for `speed`/`deriv`/`arcLengthOf`/`arctan`/`arcsin`/`sqrt`/`root_*`/`pconstructible`.
- Wolfram: symbolic speed identity residual 0; parabola pointwise residuals 0 to 50 digits; arc-length formula residual 0 to 40–50 digits; quartic identity 0; quartic root selection checked; cusp series and d>1 arc length residual 1e-78.
- draft complete, writing `notes/offset-inversion/R0-foundations.md`.
- checked `speed`/`curvature` sign against CCW and CW circles in Wolfram (κ = +1 / −1).
- derived and verified `P_d' = (1 − dκ)γ'` and `speed P_d = |1−dκ|·speed γ` symbolically and numerically.
- verified `arcLengthOf (offsetParam γ d) = R − d·arctan w` for the parabola (residual 0 to 40–50 digits).
- derived quartic `w⁴ − 2e w³ + (1+e²−d²)w² − 2e w + e² = 0`; verified residual 0 and root selection.
- analysed ordinary offset cusps: `κ'(w₀) ≠ 0`, cubic branch separation; verified `d = 2` arc length across cusp to 1e−78.
- wrote the general offset-inversion schema, the L1/L2 lemma list, and the formalized/missing table.
- corrected the parabola cusp coordinate to `(w₀(1−d^{2/3}), w₀²/2 + d^{2/3})` after re-checking `d = 2`.
- final consistency pass on the note (root selection for `d < 0`, cusp sign cases, equation form).

