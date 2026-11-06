# Plan: the incomplete third kind is P-constructible for every real `n`

Target (from `TODO-third-kind-all-n.md`):

```lean
theorem ellipticPiInc_Pconstructible {c n Φ : ℝ}
    (hcP : PConstructible c) (hnP : PConstructible n) (hΦP : PConstructible Φ)
    (hc0 : 0 < c) (hc : c < 1)
    (hne : ∀ θ ∈ Set.uIcc 0 Φ, 1 - n * Real.sin θ ^ 2 ≠ 0) :
    PConstructible (ellipticPiInc c n Φ)
```

All the analytic identities below were re-checked numerically to 40 digits (mpmath) before
being stated; the checks are reproduced at the end.

## File layout

| File | Contents | Depends on |
|---|---|---|
| `Pptc/ThirdKindAll/Circular.lean` | §2 `n < 0`: sheared sine curve | `Pptc.ThirdKind` |
| `Pptc/ThirdKindAll/CircularUpper.lean` | §3 `c < n < 1`: DLMF 19.7.9 | `Circular` |
| `Pptc/ThirdKindAll/Pseudo.lean` | §4.1 `n = 1 ± k′`: closed forms | `Pptc.ThirdKind` |
| `Pptc/ThirdKindAll/HyperbolicLower.lean` | §4.2 `0 < n < c`: DLMF 19.7.8 + duplication | `Pptc.ThirdKind`, `Pseudo` |
| `Pptc/ThirdKindAll/Period.lean` | period/reflection/reduction for `Π` | `Pptc.ThirdKind` |
| `Pptc/ThirdKindAll/Main.lean` | case split and assembly | all of the above |

`Pptc.lean` imports `Pptc/ThirdKindAll/Main.lean`.

## Status

- **A (period/reduction): DONE** — `Pptc/ThirdKindAll/Period.lean`, no `sorry`.
- **B (`n < 0`): DONE** — `Pptc/ThirdKindAll/Circular.lean`, no `sorry`, headline
  `ellipticPiInc_Pconstructible_neg` for every real `Φ`.
- **C (`c < n < 1`): DONE** — `Pptc/ThirdKindAll/CircularUpper.lean`, no `sorry`,
  `ellipticPiInc_Pconstructible_circ_upper` for every real `Φ`.
- **D (`n = 1 ± k′`): DONE** — `Pptc/ThirdKindAll/Pseudo.lean`, no `sorry`, including
  `ellipticPiInc_Pconstructible_gt_one'` with no exceptional locus.
- **E (`0 < n < c`): DONE** — `Pptc/ThirdKindAll/HyperbolicLower.lean`, no `sorry`,
  `ellipticPiInc_Pconstructible_hyp_lower_all` for every real `Φ`.
  * `ellipticPiInc_eq_hyp_recip` and `ellipticPiInc_Pconstructible_hyp_direct` cover
    `(c/n) sin²φ < 1` (DLMF 19.7.8).
  * `ellipticPiInc_eq_exchange` and `ellipticPiInc_Pconstructible_hyp_exchange` cover
    `n < c sin²φ` (Legendre's interchange relation).
  * `ellipticPiInc_eq_diag` and `ellipticPiInc_Pconstructible_hyp_diag` cover the
    `artanh` branch of the diagonal `n = c sin²φ` via DLMF 19.7.10.
  * `ellipticPiInc_Pconstructible_hyp_diag_gt` handles the remaining diagonal
    `n(2-n) > c` by one application of the generalized 19.7.9, and
    `ellipticPiInc_Pconstructible_hyp_diag_all` includes the pseudo fixed point.
- **F (assembly): DONE** — `Pptc/ThirdKindAll/Main.lean` proves
  `ellipticPiInc_Pconstructible` for all real `n`.

### E: revised route, avoiding DLMF 19.11.16

`middlePath_key` in `Pptc/Basic.lean` is already the interchange relation at an *arbitrary*
upper limit. Writing `Q(β) = c sinβ cosβ Δ(β)` and `n = c sin²β`, it gives

```
Q(β) A(n,φ) = F(φ) E(β) - E(φ) F(β) + Q(φ) A(c sin²φ, β).
```

This relates two incomplete third-kind values with **swapped parameters and angles**. Combined
with DLMF 19.7.8 (the draft's `ellipticPiInc_eq_hyp_recip`), it covers the range without the
duplication formula:

* if `φ < β(n) = arcsin √(n/c)`, apply 19.7.8 directly, since `c/n > 1` is then below its pole;
* otherwise apply the interchange and use 19.7.8 at the new parameter `c sin²φ`, whose pole
  threshold is `φ > β(n)`.

The only boundary is the diagonal `n = c sin²φ`.

### The diagonal `n = c sin²φ`

Write `s = sin φ`, `w = cos φ`, `Δ² = 1 - n`, and define

```
ω² = Δ² / w² = c (1-n) / (c-n) > 1,
A  = s² Δ² / w².
```

The diagonal specialization of DLMF 19.7.10 simplifies, because `R_C` collapses to an
`artanh`, to the explicit identity

```
Π(n,φ) = [ s² (1-c)/w² · Π(ω²,φ) + F(φ) - (s Δ / w) · artanh(A) ] / (1-n).
```

This was checked numerically to 40 digits (`c=0.7,n=0.3,φ=arcsin √(n/c)`, residual `-4e-41`;
also `c=0.6,n=0.2` and `c=0.9,n=0.1`).

If `n(2-n) ≤ c`, equivalently `A ≤ 1`, then `ω² sin²φ = A ≤ 1`, so `Π(ω²,φ)` is covered by
the `n > 1` theorem and the displayed formula finishes the diagonal directly. If
`n(2-n) > c`, the parameter `n' = (c-n)/(1-n)` satisfies `n' < n` and `n' < 1 - √(1-c)`;
applying DLMF 19.7.9 once maps the diagonal `(n,φ)` to the diagonal `(n',φ')`, to which the
first case applies. The pseudo fixed point `n = 1 - √(1-c)` is the equality case and is
already a closed form in `Pseudo.lean`.

The displayed identity is formalized as `ellipticPiInc_eq_diag`, with derivative
`hasDerivAt_hypDiagRHS`.  The one-step 19.7.9 reduction is
`ellipticPiInc_Pconstructible_hyp_diag_gt`.

### Current build

`Pptc.lean` imports `Pptc.ThirdKindAll.Main`, and

```
lake build
Build completed successfully (3921 jobs).
```

No `sorry` occurs in `Pptc/ThirdKindAll/`. The old draft
`Pptc/ThirdKindAll/HyperbolicLower.lean.draft` has been removed; its useful content is in
`HyperbolicLower.lean`.

### Completed Lean tasks

1. Generalize `circUpperNu_lt_one`, `hasDerivAt_circUpperRHS`,
   `continuous_circUpperRHS` and `ellipticPiInc_eq_circUpper` in `CircularUpper.lean`
   from `c < n` to `n < c`.
2. Prove the simplified DLMF 19.7.10 identity on its `artanh` branch.
3. Use the generalized 19.7.9 for the diagonal case `n(2-n) > c`; the equality case is
   `ellipticPiInc_pseudo_minus` in `Pseudo.lean`.
4. Assemble `Main.lean` and import it from `Pptc.lean`.

## Subproblems

### A. Shared reductions (`Period.lean`) — independent

A1. `ellipticPiIntegrand c n` is `π`-periodic and even in `θ` whenever it is defined.
A2. `ellipticPiInc c n (φ + mπ) = ellipticPiInc c n φ + 2m · ellipticPi c n`
    (needs no pole on the path).
A3. `ellipticPiInc c n (-φ) = -ellipticPiInc c n φ`.
A4. Reflection about `π/2`: `ellipticPiInc c n (π - φ) = 2·ellipticPi c n - ellipticPiInc c n φ`.
A5. `ellipticPiInc_eq_aux_of_ne` already gives `Π = F + n·A` off the pole.

Deliverable: `ellipticPiInc_reduce` reducing an arbitrary `Φ` to `[0, π)` and, when needed,
to `[0, π/2]`, with `PConstructible Φ`.

### B. §2 circular `n < 0` (`Circular.lean`) — independent

Constants
```
D = c - n,  p = √(1-n),  q = √(-n),  b = pq/D,  a = √(c(1-c))/D
γ(t) = (-b t + sin t, a t)
T(θ) = 2 arctan((p-q) tan(θ/2))
w(θ) = 1 - n sin²θ,  Δ(θ) = √(1-c sin²θ)
```
B1. `γ = linearMap (-b) 1 a 0 '' sine`, hence `PConstructibleCurve`; injective, smooth,
    `speed γ t = √((cos t - b)² + a²)`.
B2. `T 0 = 0`, `T` strictly increasing on `[0, π)`, `T '' [0, π) ⊆ [0, π)`.
B3. Pointwise identity
    `speed γ (T θ) · T'(θ) = Δ(θ)(p - q cos θ)²/(√D w(θ)²)`.
B4. Antiderivative
    ```
    G(θ) = ( E(θ) - F(θ) + (1-n)Π(n,θ)
             - n sinθ cosθ Δ/w
             - p q (sinθ Δ/w + arctan(√D sinθ/Δ)/√D) ) / √D
    ```
    satisfies `HasDerivAt G (Δ(p-q cosθ)²/(√D w²)) θ` and `G 0 = 0`.
B5. Change of variables: `arcLengthOf γ 0 (T θ) = G θ`.
B6. Isolate
    ```
    Π(n,θ) = ( √D · arcLengthOf γ 0 (T θ) - E(θ) + F(θ)
               + n sinθ cosθ Δ/w
               + pq (sinθ Δ/w + arctan(√D sinθ/Δ)/√D) ) / (1-n)
    ```
    valid for `0 ≤ θ < π`.
B7. P-constructibility of every term; hence
    `ellipticPiInc_Pconstructible_neg : n < 0 → PConstructible (ellipticPiInc c n Φ)`
    for all `Φ` (via A).

### C. §3 circular `c < n < 1` (`CircularUpper.lean`) — after B

With `n' = (c-n)/(1-n) < 0` and `φ' = arcsin(cos φ/Δ(φ))`,
```
Π(n,φ) = c/(c-n)·F(φ)
        - n(1-c)/((1-n)(c-n)) · (Π_complete(n') - Π(n',φ')).
```
C1. `φ'` is P-constructible, lies in `[0, π/2]`, and `φ'(0)=π/2`, `φ'(π/2)=0`.
C2. Prove the identity by differentiating in `φ` and matching at `φ = 0` (the boundary
    values are both `0`).
C3. P-constructibility for `[0, π/2]`, then all `Φ` by A.
Deliverable: `ellipticPiInc_Pconstructible_circ_upper`.

### D. §4.1 pseudo-elliptic parameters (`Pseudo.lean`) — independent

`k' = √(1-c)`, and `n = 1 ± k'`:
```
Π(1+k',φ) = ( -(1-k')F(φ) + artanh((1+k') sinφ cosφ/Δ) ) / (2k')
Π(1-k',φ) = (  (1+k')F(φ) - artanh((1-k') sinφ cosφ/Δ) ) / (2k')
```
D1. Derivative of `Real.artanh` (absent from Mathlib): `d/dx artanh x = 1/(1-x²)`.
D2. Prove both by `HasDerivAt` + `G 0 = 0`.
D3. P-constructibility of `artanh` of a P-constructible argument via the `log` definition.
D4. Remove `hgen` from `ellipticPiInc_Pconstructible_gt_one`.
Deliverable: `ellipticPiInc_Pconstructible_gt_one'`.

### E. §4.2 hyperbolic `0 < n < c` (`HyperbolicLower.lean`) — hardest

E1. Arctanh form, for `sin²φ < n/c`:
    ```
    Π(n,φ) = F(φ) + artanh(r tanφ/Δ)/r - Π(c/n,φ),   r = √((c/n-1)(1-n)).
    ```
    Prove by differentiating and matching at `0`; `c/n > 1` so D applies to `Π(c/n,φ)`.
E2. Duplication formula (DLMF 19.11.16) to halve `φ` into range and double back:
    ```
    Π(ψ,n) = 2 Π(θ,n) + n·R_C(γ-δ, γ),
    γ = (csc²θ - n)²(csc²ψ - n),  δ = n(1-n)(n-c),
    sin²θ = (1-cosψ)/(1+Δ(ψ)).
    ```
    `R_C` is elementary (`R_C(x,y) = artanh(√((x-y)/x))/√(x-y)` or `atan`), so this reduces
    to `artanh`/`atan` of P-constructible quantities.
E3. Repeated halving reaches `sin²θ < n/c`; assemble.
Deliverable: `ellipticPiInc_Pconstructible_hyp_lower`.

### F. Assembly (`Main.lean`) — after A–E

F1. Case split on `n`:
    `n < 0` (B), `n = 0` (existing), `0 < n < c` (E), `n = c` (existing),
    `c < n < 1` (C), `n = 1` (existing), `n > 1` (D, no exceptional locus).
F2. For `n > 1` discharge the no-pole hypothesis as stated; reduce `Φ` by A using only
    paths that avoid the pole (the hypothesis is stronger than needed).
F3. Final theorem `ellipticPiInc_Pconstructible`.

## Numerical checks

```
# §2
c=0.37, n=-1.7: quad(speed,[0,T(θ)]) - G(θ) ≈ -1e-41 for θ=0.3,1.4,2.9
# §3
c=0.3, n=0.5, φ=0.7: residual -4.6e-41
# §4.1
c=0.3, n=1±√0.7, φ=0.4: residuals -1.1e-41, 5.7e-42
# §4.2
c=0.7, n=0.3, φ=0.5: residual 0
```
