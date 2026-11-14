# Notation: core

A notation for writing down P-constructible numbers the way a mathematician would, for
reading and communication. It is not Lean syntax and is not meant to be machine-checked.
Libraries built on it: `POLYNOMIALS.md`.

## Kinds of line

Every line of a construction is exactly one of these, and says which.

| line | form | meaning |
|---|---|---|
| **Definition** | `name := expression` | an abbreviation; unfolding it gives back the expression |
| **Fact** | a statement, with its source | a proved result that makes something legal, e.g. `{f = 0} ⊂ 𝒫` for `deg f ≤ 6` |
| **Choice** | `name :∈ S` | let `name` be any element of `S`; legitimate only if `S` is non-empty |
| **Claim** | `x = expression` | a number already in hand equals a legal expression, so it is in `𝒫` |

A definition never makes anything new reachable: unfolding every name gives back a
construction from the constructors of `Pptc/Defs.lean`. New reach only enters through Facts.

## Numbers and shapes

- `𝒫` is the set of P-constructible numbers. Numbers are written as ordinary mathematics.
- A **shape** is the set of points its equation defines: `{y = sin x}`, `{x² + y² = 1}`.
  `Γ_f := {y = f(x)}` is the graph of `f`. Writing a shape claims it can be drawn.
- Moving, stretching, turning and reflecting a shape rewrite its equation, so they have no
  symbol of their own: `{y = 3 sin(2x + 1) − 4}` is legal because `{y = sin x}` is.

| notation | meaning |
|---|---|
| `Aᵀ` | `A` reflected in the line `y = x`; `Γ_{f⁻¹} = (Γ_f)ᵀ` |
| `A\|_W` | `A` cropped to the window `W`, e.g. `Γ_sin\|_{[−π/2, π/2]}`, `S¹\|_{y ≥ 0}` |
| `A_{∥d}` | `A` offset sideways by `d` (positive: to the left of travel) |
| `A⌒(P, s)` | the arc of `A` from `P` of length `s`; the sign of `s` gives the direction |

## Numbers from shapes

| notation | meaning |
|---|---|
| `(A ⋔ B)ₓ`, `(A ⋔ B)ᵧ` | coordinates of the crossing of `A` and `B` |
| `(f ⋔ g)` | the `x` where `Γ_f` and `Γ_g` cross |
| `\|A\|` | length of `A`, when `A` is an arc with endpoints in `𝒫` |
| `⌈A⌉ₓ ⌊A⌋ₓ ⌈A⌉ᵧ ⌊A⌋ᵧ` | right, left, top and bottom edges of `A`'s bounding box |

If `Γ_f` is a shape then `f(u)` is a number for every `u ∈ 𝒫` in its domain.

## Selecting one crossing

A crossing must be singled out before it can be read. Write the selector as a subscript:

- `(A ⋔ B)_{≈v}`: the crossing nearest `v` (by `x`); `(A ⋔ B)_{≈(a, b)}`: nearest the point `(a, b)`.
- `(A ⋔ B)_{[a, b]}` or `_{x ≥ 0}`: the only crossing in that window.

The selector only says *which* crossing is meant, so it may be any description at all,
including a decimal or an expression in numbers not in `𝒫`. What makes it legal is that the
crossing is isolated: a crop window with rational ends then contains it and nothing else.

A shape only needs to be drawable inside that window. For example `Γ_{X⁸}` near a negative
crossing is the mirror image of the drawn power law `y = x⁸, x ≥ 0`.

## Sample glossary

```
S¹        := {x² + y² = 1}
π         := |S¹|_{y ≥ 0}|
√a        := (x² ⋔ a)_{x ≥ 0}                          a ≥ 0
log₂ a    := (2ˣ ⋔ a)                                  a > 0
ln a      := 4 |Γ_{x²}|_{[0, m]}| − (a⁴ − 1)/(4a²),     m := (a² − 1)/(4a),  a > 0
exp u     := 2^{u / ln 2}
cos u     := sin(u + π/2)
Γ_arcsin  := (Γ_sin|_{[−π/2, π/2]})ᵀ
E(b)      := |{x² + y²/b² = 1}|_{x, y ≥ 0}|                b > 0
```
