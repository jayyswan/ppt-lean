# HANDOFF — R3 (Watson/Pólya reduction; check bcc/fcc formulas, B5)

Research only. No `.lean` edits. Deliverable: `NOTES-hypergeometric-R3.md`.
Scripts: `archived files/hypergeometric-scripts/R3-*.py` (mpmath, run with `py`).

- [step 1] Read AGENTS.md, PLAN overview (§2 V11, §4/§5 B5, wave table R3), NOTES-R1
  (do not duplicate). Found a pre-existing `R3-watson-checks.py` (partial, buggy: return
  series tail claim false, direct-integral section crashes). L8 already landed
  (`Pptc/Hypergeometric/Polya.lean`, Gamma + K forms both sorry-free).
- [step 2] Fetched MathWorld "Watson's Triple Integrals" and "Pólya's Random Walk
  Constants". Confirmed Watson I_1 = Γ(1/4)^4/(4π^3), I_2 = 3Γ(1/3)^6/(2^{14/3}π^4),
  I_3 = √6/(96π^3)Γ(1/24)Γ(5/24)Γ(7/24)Γ(11/24), and u(3)=3I_3.
- [step 3] Derived (symbolically) the lattice return numbers as BZ/generating-function
  integrals: u_bcc = I_1, u_fcc = 3 I_2, hence plan's fcc candidate is off by a factor 3.
- [step 4] Confirmed against OEIS: u(3)=A086231, p(3)=A086230, u_bcc=A091670 (escape
  A293238), I_2=A091671, u_fcc=3*A091671 (escape A293237 = 2^(14/3)π⁴/(9Γ(1/3)⁶)).
- [step 5] Wrote/ran `R3-01-sc-polya.py`: sc Gamma/K/theta forms agree ~100 digits;
  p(3) matches A086230 to 60 digits; Bessel integral quadts[0,inf] to ~52 digits.
- [step 6] Wrote/ran `R3-02-bcc-fcc.py`: bcc Γ(1/4)^4/(4π³)=I_1 verified (4 K(1/2)²/π²,
  2F1², direct 2D integral, ~90/60/25 digits); I_2=3Γ(1/3)^6/(2^{14/3}π^4) verified
  (√3 K((2−√3)/4)²/π², direct integral, ~90/63 digits); u_fcc=3I_2 verified incl. K-product.
- [step 7] Checked Lean API: `Gamma_intCast_div_twentyfour_Pconstructible` exists;
  `ellipticF_pi_div_two_Pconstructible {c} (hcP) (hc : c<1)`. Now drafting the note.
- [step 8] `lean_multi_attempt` on `Pptc/Hypergeometric/Polya.lean:73` (warm env):
  `pconstructible` closes Γ(1/4)^4/(4π³), and 9Γ(1/3)^6/(2^(14/3)π^4) (also
  16·2^(2/3) form), and 1-(...)⁻¹; but the K-forms `4/π²·ellipticF(1/2)` and the
  (2∓√3)/4 products FAIL — aesop cannot discharge the `<1` side goal automatically.
- [step 9] Wrote `R3-03-mods-and-k3.py`: two roots of the k6 quartic in (0,1)
  (0.0851642… and 0.8430390…); K(sin π/12)=3^{1/4}Γ(1/3)^3/(2^{7/3}π) exact; K(m+)=√3K(m−).
- [step 10] Wrote deliverable NOTES-hypergeometric-R3.md. Done.
