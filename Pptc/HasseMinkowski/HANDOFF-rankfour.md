# HANDOFF rankfour

Goal: rewrite `Pptc/HasseMinkowski/RankFour.lean`:
- WP4.1 `local_splitting`
- WP4.2 `rankFourDiagonalHM : RankFourDiagonalHM`
- WP4.3 `isotropic_of_rank_four`
No sorry/axiom; targeted imports.

## Log
- started; reading plan + Prod/Local/Legendre/Existence.
- wrote WP4.1 (splitLinearEquiv, splitIsometryEquiv, local_splitting) in RankFour.lean.
- built HighRank olean; retrying RankFour diagnostics.
- WP4.1 local_splitting compiles.
- WP4.2 rankFourDiagonalHM compiles (helpers wss_two_represents_iff_ternary,
  isotropic_three_of_symbol, represents_two_of_local_symbol). Remaining items:
  linter.flexible warnings on two `simp [b, ε]` lines only.
- WP4.3 isotropic_of_rank_four compiles.
- Deleted scratch. File diagnostics clean (only 2 linter.flexible warnings).
- Running final lake_check Pptc/HasseMinkowski/RankFour.lean.
