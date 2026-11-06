# NOTES-hypergeometric-R4

**Inbound survey: does any drawable arc other than the ellipse and the monomial graphs give a
new ₂F₁ family?**

Research note, wave 2, task **R4** of `PLAN-hypergeometric-00-overview.md`. No `.lean` file was
created, edited or deleted; no `lean-lsp` tool and no `lake` command was used. This note is the
umbrella over the three part-notes:

| part | note | curve family |
|---|---|---|
| R4a | `NOTES-hypergeometric-R4a-bezier.md` | general cubic Bézier (`ThirdKind.lean`) |
| R4b | `NOTES-hypergeometric-R4b-offset.md` | `offset` of any base curve |
| R4c | `NOTES-hypergeometric-R4c-sine-exp.md` | `sine`, `exp_two`, `rectangle`, affine images |

All numeric work used the **Wolfram Language kernel** (`wolfram_WolframLanguageEvaluator`); no
Python. Every identity in the part-notes is labelled **[NC n]** (checked to `n` significant
digits), **[SY]** (proved symbolically), **[CL]** (classical, cited) or **[SP]** (speculative).

---

## 0. Answer in brief

**No other drawable arc length contributes a new ₂F₁ family.** The inbound map is exactly:

1. **the ellipse** — the complete elliptic integrals `K`, `E` as `₂F₁(±½,½;1;·)`, and through
   the contiguous relations the whole class `(½+ℤ, ½+ℤ, 1+ℕ)`
   (`hyp_elliptic_class_Pconstructible`);
2. **the monomial graphs** `y = xⁿ`, `n ≤ 6` (with affine images) — the arc-length family
   `₂F₁(−½, 1/m; 1+1/m; ·)`, `m = 2n−2 ∈ {2,4,6,8,10}`, and its class
   `(−½+ℤ, 1/m+ℤ, 1+1/m+ℕ)` (`hyp_graphFamily_class_Pconstructible`);
3. **the `z = 1` Gauss route** — the denominator-24 family `hyp_one_Pconstructible_of_den_24`.

Everything else falls into one of two obstructions:

* **incomplete Appell integrals** — a general cubic Bézier reduces to *incomplete* `F`/`E`/`Π`
  (Appell `F₁`/`F_D`), and a restricted arc of `sine` is an *incomplete* `E`
  (`sinφ·F₁(½;½,−½;3/2;sin²φ,½sin²φ)`); per PLAN §1 these are **not** ₂F₁;
* **elementary** — `exp_two` and `rectangle` edges have elementary arc lengths (Chebyshev), and
  the `offset` of any curve is its base length plus an elementary turning-angle excess.

## 1. Method

Each part derived the arc-length density of the relevant constructor, classified `∫ speed dt`
(elementary / elliptic / hyperelliptic / Appell), reduced it to standard forms, and compared
every closed form to high-precision numerical quadrature with the Wolfram kernel (typically
40–99 digits). A family counts as *new* only if it is a ₂F₁ whose parameter identity is not one
the programme already owns; the yardstick classes are `hyp_elliptic_class_Pconstructible`
(`EllipticClass.lean:521`) and `hyp_graphFamily_class_Pconstructible` (`GraphsClass.lean:765`).

## 2. Verdict per curve family

| constructor | arc length | kind of integral | ₂F₁? | obstruction / note |
|---|---|---|---|---|
| `cubic_bezier`, general | `∫√Q dt`, `Q = x'²+y'²` a quartic | genus 1, **incomplete** `F`/`E`/`Π` | no | Appell `F₁`/`F_D`; `ThirdKind.lean` already lands the incomplete `Π` |
| `cubic_bezier`, graph of `y=Cx³` | `∫√(1+9C²t⁴) dt` | ₂F₁, `m=4` | yes, **old** | `(−½,¼;5/4;·)` ∈ graph class (`n=3`) |
| `cubic_bezier`, `h=0` / ellipse limit | complete `K` | ₂F₁ | yes, **old** | `(½,½;1;·)` ∈ elliptic class |
| `offset` of any γ | `arcLength γ − d·Δφ` | base integral + elementary | no | turning angle `Δφ = ∫κ ds` is elementary (`atan2` of velocity) |
| `offset` of a monomial graph | H6 ₂F₁ `+ d·arctan(nCx^{n−1})` | ₂F₁ + elementary | no | hypergeometric part is exactly the old graph family |
| `sine`, restricted arc | `√2(E(b|½) − E(a|½))` | incomplete `E` | no | incomplete `E` is Appell `F₁` |
| `sine`, complete sub-arcs | `√2·E(½) = (π/√2)₂F₁(−½,½;1;½)` | ₂F₁ | yes, **old** | complete `E` ∈ elliptic class (`i=−1, j=0, k=0`) |
| `sine`, affine image `A sin(Bx+C)+D` | `k² = A²B²/(1+A²B²)` | incomplete `E` / complete `E` | no new | same elliptic class at a P-constructible parameter |
| `exp_two` | `(1/ln2)[√(1+u²) − arsinh(1/u)]`, `u=(ln2)2^x` | elementary | no | Chebyshev; no finite complete period |
| `rectangle` edge | `|q − p|` | elementary | no | straight segment |

Affine images (`translate_x/y`, `scale_x/y`, `rotate`) leave every classification unchanged:
Bézier-to-Bézier, and the turning angle of an image curve is still `atan2` of elementary data.

## 3. Why the negative is tight, and its loophole

* **Bézier.** `speed² = x'² + y'²` is a sum of two real squares of quadratics, so every real
  zero of `Q` has multiplicity ≥ 2: `√Q` has no real branch point, and a real Bézier arc never
  integrates between simple real roots. Hence it never *completes* to a `K`/`E`/`Π` ₂F₁. The
  reduction to incomplete `F`/`E`/`Π` is the classical genus-1 one already formalised in
  `ThirdKind.lean`.
* **offset.** `ds_d = ds − d·dφ`; the curvature term integrates to the total turning angle,
  which is an explicit elementary function for every curve in the constructor language.
* **sine.** The density `√(1+cos²t) = √2·√(1 − ½sin²t)` is the *second-kind* density; its
  incomplete integral is a two-variable Appell `F₁`, and its complete value is the landed
  Legendre `E`.
* **exp / rectangle.** Chebyshev's criterion: `∫ xᵖ(α+βxᵐ)^q dx` is elementary here.
* **Loophole (not excluded).** A *coincidence at a special algebraic endpoint* could make a
  particular incomplete integral collapse to a single ₂F₁, or make a particular Bézier complete.
  R4 establishes that no *family* arises and identifies no such endpoint; it does not rule out
  isolated values. This is the same caveat as PLAN §7: no non-P-constructibility is claimed.

## 4. Consequence for the plan

* §4/§6: **the inbound map is closed.** The only inbound hope left is the B6 *first-kind*
  differential gap (a primitive realising `∫ dx/√(1+x^m)`, or a closed drawable curve of genus
  ≥ 2). That is a pole/differential question, not an arc-length-family question, so R4 does not
  touch it.
* §7: R4 supplies the *useful negative* — a clean statement of which ₂F₁ families cannot come
  from the six base curves by the mechanisms here, with the endpoint caveat listed.

## 5. Label ledger

| claim | label | where |
|---|---|---|
| general Bézier arc length is incomplete `F`/`E`/`Π` | [SY] + [NC 99] | R4a §0–2 |
| real Bézier `Q` has no simple real root | [SY] + [NC 50] | R4a §3 |
| `y=Cx³` Bézier ₂F₁ is the `m=4` graph family | [NC 59] | R4a §4a |
| `h=0` limit is `K=(π/2)₂F₁(½,½;1;c)` | [NC 59] | R4a §4b |
| `arcLength(offset) = arcLength γ − d·Δφ` | [SY] + [NC 60] | R4b §0–2 |
| ellipse offset = second-kind `E` + elementary (no `Π`) | [SY] + [NC 60] | R4b §2.3 |
| monomial-graph offset = H6 ₂F₁ + `d·arctan` | [SY] + [NC 60] | R4b §2.4 |
| `sine` arc length `= √2(E(b|½)−E(a|½))` | [SY] + [NC 40] | R4c §1 |
| `√2·E(½) = (π/√2)₂F₁(−½,½;1;½)` (landed class) | [NC 40] | R4c §0 |
| `exp_two` arc length elementary | [SY] + [NC 40] | R4c §0–2 |
| Chebyshev criterion for exp/rectangle | [CL] | R4c §0 |
| endpoint-coincidence loophole | [SP] | this note §3 |

## 6. Scripts

| script | contents |
|---|---|
| `archived files/hypergeometric-scripts/R4a-bezier-checks.wl` | R4a §1–4 reductions and numeric checks |
| `archived files/hypergeometric-scripts/R4b-offset-checks.wl` | R4b offset identity, per-base densities |
| `archived files/hypergeometric-scripts/R4c-01-sine-exp-rect.wl` | R4c sine/exp/rectangle checks |
