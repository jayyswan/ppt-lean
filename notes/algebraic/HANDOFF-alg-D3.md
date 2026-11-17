# HANDOFF-alg-D3: offset towers with a spare parameter (PLAN-degree9 D3, with R4/R5)

Backend: Wolfram (wolfram MCP).

- 2026-11-13 start, after H. Read W1 (ranks, backward chain, genus-1 obstruction).
- Forward chain:
  - layer 1 is a conic, so free; normalise h = 4t^2+1;
  - layer 2: D : s^2 = h, sigma^2 = g, genus 1;
  - D is genus 0 only for a conformal layer 2 (proof), so step 3 / R4 is negative (scoped).
- D(R) has 2 components, so j >= 1728. With a = 0: j(D) = Legendre(b^2), and sign J flips at
  b^2 = 1/2.
- R5 on q3 with Q = (beta, 2beta^2+beta^4):
  - Gamma_Q is affine-smooth;
  - j = 318376.96... (rational, 103/97 digits, 600-digit fit), Delta > 0, sign J = -1;
  - matched by b = 0.16730... (sextic in b^2);
  - 11 of 18 small Q have Delta > 0.
- Remaining: 4 conic-support conditions on (Q, T, d1, d2); no sequential order found.
  Fibre-curve degree not computed (homotopy needed).
- Wrote D3.md.
