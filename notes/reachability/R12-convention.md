# R12 — the convention: what "solves a family" means

**Stream:** R12 of `notes/reachability/PLAN-routes.md` (wave 1, foundations).
**Deliverable:** this file. Research only: **no `.lean` edit, no `lake` command.**
**Status:** recommendation, awaiting ratification (§2.5). The recommendation is **B + C**; the
alternative A is not wrong, but it is strictly weaker and needs R9 before it can support any
exclusion.

Sources read: `R3-separation.md` §2.1, §3.9, §4; `R2-tower.md` Q3.3–Q3.4; `R8-missing-curve-audit.md`
§1–§3; `R7-dzero.md`; `R5-named.md` §0–§1; `warp/sheared-sine-intersections.md` §3;
`Pptc/Defs.lean` (`PConstructible`), `Pptc/Basic.lean` (`sin_Pconstructible`, `cos_Pconstructible`,
`arctan_Pconstructible`, `log_Pconstructible`).

Labels: **[Proof]**, **[Wolfram]**, **[Heuristic]**, **[Open]**.
**Backend:** every number below was produced by Wolfram Language, 40-digit working precision; the
cells are in §6. No Python.

---

## 0. Verdicts

1. **The uniform convention has exactly one free parameter that matters: the value coordinate.**
   Root-independence — no datum may depend on the unknown root — is non-negotiable and is what makes
   "solving" non-trivial. The choice is how the *value* `x` may enter the construction. The old text
   ("P-constructible data") silently allowed the permissive answer; the separation theorems silently
   assumed the affine one. R12 makes the choice explicit.

2. **A is genuinely stronger, but unevenly.** Under A the target may be composed on the value side
   with any P-constructible `φ`: `D = φ ∘ F`.
   - **Log points are A-robust when the monodromy is real.** The parabola (`2πd`), `gd` (`2π`), the
     involute, the rhumb and the beam interpolation have real monodromy, so their local log
     coefficient is imaginary; a real-analytic `φ` cannot resolve an imaginary log (Lemma 1.2). It
     can only turn it into a pole — the witness is `sin(gd u) = tanh u`, and `tanh` has a pole at
     each branch point. So R3's log separation survives A for these targets, with a corrected
     argument. The tractrix (`−ln sin ψ`, monodromy `−2πi`) and Biot
     (`sinh u (gd u + kπ)`, coefficient `1`) have **complex** monodromy and are **not** A-robust;
     `exp` resolves them. A-robustness is target-specific.
   - **`1/log` and `δlogδ` are not A-robust.** Real `φ` resolve them:
     `exp(1/(1/log ζ)) = ζ` and `(δ log δ)/W(δ log δ) = δ`. So R8's obstructions for `tan` and
     `l = 0` are **B-only**; under A they disappear.
   The programme is therefore B-scoped for `tan`, `l=0`, the tractrix and Biot, and can be A-scoped
   for the protected log rows. B is the uniform recommendation; A is a genuine strengthening in
   those non-log places (and for the elastica, by non-elementarity).

3. **Adopt B + C.** B = affine data: every shape datum (curve affine data, offset `d`, length `X`,
   translation) is affine in the value. Sub-cases **B0** (shape data constant) and **B1** (shape data
   affine, non-constant). C = discrete mode index: fixed construction term, data P-constructible in
   the mode `m`. A = permissive, for **existence** claims only. S = single target, no uniformity.

4. **Under B, R3's Theorem 3.4/3.5 stand unchanged, and Route I is closed for affine value data.**
   The only extra lemma needed is: an affine `φ` preserves the finite-log-branch-point set. This is
   immediate and is written out in §3.1. B is therefore not a weakening of the intersection theorem;
   it is its actual hypothesis, made explicit. [Proof]

5. **Under B0, R2's rigidity is unchanged.** Under **B1**, Route-O necessity becomes a new,
   well-posed finite-dimensional problem, not a constructibility question. For the `tan` family it
   reduces to a **4-function linear span condition** on the Whewell function `R_C` (§3.3). The
   catenary is the solution with `(a,b,c,e) = (1,0,kπ,0)`; the log-cosine is **not** in the span
   [Wolfram]; the circle is only there degenerately. **Uniqueness among drawable curves is open** —
   this is the sharpened form of R2 Q3.4 and the only Route-O gap that survives B.

6. **R12 does not settle `tan x = λx`; it localises the gap.** The obstacle is no longer "a missing
   curve" and not even "`1/log`" alone: it is `B1` + the `1/log` singularity. The catenary route is
   B1-legal (`d = λ`, `x = λkπ` are affine in `λ`), so B does **not** exclude it. What B does is
   replace "does a P-constructible `d(λ)` exist?" by "does `R_C` lie in a 4-dimensional span?".

7. **C is a formulation, not a theorem.** For a discrete spectrum R3 is silent by construction, and
   the `sine` curve shows why no identity-theorem/interval argument can decide it: `u ↦ u + sin u`
   is a drawable graph function (a shear of `sine`) and hits every prescribed value. Only
   arithmetic/transcendence (R11) can separate a discrete spectrum. C's job is to make that question
   precise, not to answer it.

8. **The R5 table under the template** (§4.2): 5 rows are intersection-impossible under B0
   (7, 10, 13, 14, 16), 1 is open on both routes with the B1 + `1/log` gap (6), 2 are mixed
   (8, 9: continuous interpolation B0-excluded, discrete spectrum C-open), 1 is open on both
   routes with `δ log δ` (15), 1 is a legality question (12, S), 1 is a Route-I construction with
   different missing curves (19), and the rest are R/S.

9. **Decision required (§2.5): ratify B + C, or choose A and accept that the non-log exclusions
   (`tan`, `l=0`, tractrix, Biot, elastica) lose their singularity proof — a different, global
   method would be needed for them. The protected log rows survive A.**

---

## 1. Why the convention needs fixing

### 1.1 The text as it stands

R3 Definition 2.1 is the operative one:

> **Definition 2.1 (uniform convention).** Let `F : J → ℝ` be injective, `U = F⁻¹`, and let `s` be a
> construction term. We say `s` **solves `F` on `J`** if for every `x ∈ J` the term, instantiated
> with (i) all fixed curve data and (ii) P-constructible parameters that are functions of `x` only,
> built from `x` by the same constructive vocabulary, produces a P-constructible number `u(x)` with
> `F(u(x)) = x`, and no parameter depends on `u` or on `F`.

The clause "P-constructible parameters that are functions of `x` only" is doing two different jobs at
once, and they need separating:

- **Root-independence** (good, keep): no parameter may depend on `u` or on `F`. Without this, the
  construction could simply be given the answer.
- **Value-dependence** (the choice): *which* functions of `x` are allowed. This is what the
  separation theorems silently restrict, and what the permissive reading silently enlarges.

### 1.2 The three slots

Every construction term has three kinds of ingredient:

| slot | examples | may depend on the unknown? |
|---|---|---|
| **unknown** | the root `u`, the angle `ψ`, the intersection point | — |
| **value** | the family parameter `x` (or `λ`), the length to lay, the RHS | **no** |
| **shape data** | the two curves, their affine data, the offset `d`, the start point, the window | **no** |

The value is the quantity the construction must be a function of; the shape data are everything else.
"Root-independence" says neither slot may depend on the unknown. "Value-dependence" says how the
value may enter. The separation theorems are about the *shape* of the resulting function of the
unknown, so the value-dependence is the only thing that can change their conclusion.

### 1.3 The value-side identity

Consider Route I, one intersection. By R3 Lemma 2.3, the construction forces

```
D(u) = φ(x),        D := g_{C₁} − g_{C₂},                                    (1.3.1)
```

where `φ` is however the value enters (identity for a `translate_y` by `x`, an affine map for a
scaled translation, an arbitrary P-constructible map under A). The target is `F(u) = x`. If the
construction solves the target on an interval, then on that interval the unique solution of (1.3.1)
is `u = F⁻¹(x)`, so

```
D(F⁻¹(x)) = φ(x),        i.e.        D = φ ∘ F        on the range.          (1.3.2)
```

**Equation (1.3.2) is the whole convention question.** The separation theorem has to exclude every
`D` of the form `φ ∘ F` with `D` a difference of two tower graph functions and `φ` in the allowed
class. Under B, `φ` is affine, so (1.3.2) is `D = aF + b`; under A, `φ` is arbitrary P-constructible.

The same identity holds for a single box: the box output is `φ(x)`, and `F⁻¹ = φ⁻¹ ∘ box`, i.e.
`box = φ ∘ F` with `φ` the readout map. R3 §3.9(2) ("box with non-affine `x`-dependence") is exactly
the statement that `φ` is not affine.

### 1.4 A is stronger, but unevenly

Under A, (1.3.2) allows any P-constructible `φ`. Whether that enlarges the reachable class depends on
the singularity type. The first fact is a protection:

> **Lemma 1.2 (real targets have imaginary log coefficients) [Proof].** Let `F` be real-analytic on a
> real interval and have a finite log branch point `u₀` with monodromy `c ∈ ℝ \ {0}`. Then near `u₀`
> ```
> F = (c/2πi) log ζ + analytic = −i(c/2π) log ζ + analytic ,        ζ = u − u₀ ,
> ```
> and for no nonconstant real-analytic `φ` is `φ ∘ F` analytic at `u₀`.

*Proof.* Put `w = F`. The monodromy is `w ↦ w + c`, so a single-valued analytic function of `w` is
`Φ(e^{2πi w/c})`, with `ζ = e^{2πi w/c}`. If `φ ∘ F = Φ(ζ)` is analytic at `ζ = 0`, then `Φ` is
analytic in a disk. It is also analytic on the unit circle, where it is defined by the real function
`φ` on real `w`; and there `Φ` is **real** because `φ(w)` is real and `|e^{2πi w/c}| = 1`. So `Φ` is
analytic on a neighbourhood of the closed unit disk and real on its boundary. Its imaginary part is
harmonic there and vanishes on the boundary, hence vanishes identically; so `Φ` is constant, and
`φ` is constant. ∎

This is why R3's log obstruction **survives A** for the targets with real monodromy: the parabola
(`±2πd`), `gd` (`±2π`), the involute and the rhumb all have imaginary log coefficients, so a real
`φ` cannot resolve them. The point remains singular; the typical outcome is a pole (as `sin` shows).
The A-robustness is target-specific: the tractrix has coefficient `−1` (from `−ln sin ψ`, monodromy
`−2πi`) and Biot has coefficient `1` (from `sinh u (gd u+kπ)`), both real, so `exp` **does** resolve
them; they are B-only. The witness for the protected case is `gd`:

```
gd u = 2 arctan(e^u) − π/2,        sin(gd u) = tanh u,        cos(gd u) = sech u.      (1.4.1)
```

[Proof: `sin(2 arctan z − π/2) = −cos(2 arctan z) = (z²−1)/(z²+1)` with `z = e^u`; Wolfram cell 1
gives residual `0`.] So `φ(z) = sin z` turns the log points into **poles**: `tanh` has
`1/(u−u₀)` at each `u₀ = iπ(m+½)` (`cosh(iπ(m+½)) = 0`). The log *count* fails; the point remains
singular. Lemma 1.2 says this is unavoidable for a real `φ`.

The situation is different for the non-log singularities. Real `φ` **do** resolve them:

```
1/log:  φ(z) = exp(a/z)   with a the 1/log coefficient   gives  ζ (up to a constant)
δlogδ:  φ(z) = z/W(z)     (after absorbing the constant) gives  δ
```

Both are real P-constructible (`1/z`, `exp`, and Lambert `W`; `W` is `lambertW` in
`Pptc/Basic.lean`, reached from the graph of `exp`, and `lambertW_Pconstructible` is proved there).
The constants are target data and are P-constructible, so the resolution is available for the
specific `tan` and `l = 0` targets, not only for the model singularities.
Consequently:

- R3's log separation is **A-robust** for targets with real monodromy (Lemma 1.2). B is the simpler
  proof, not the only one.
- R8's `1/log` and `δlogδ` obstructions are **B-only**. Under A, `tan` and `l = 0` lose their
  singularity obstruction; whether they are reachable is a different, global question.

This is the precise sense in which A is stronger: it does not change the log rows, but it removes the
two open-row obstructions that motivated R9. That is why the convention must be chosen before R9 is
run, and why B is the recommendation for a uniform programme.

### 1.5 The two loopholes are different

The plan's §0.3 lists "non-affine data" and "parameter-dependent data" as two loopholes. They are
different, and the difference is exactly value vs shape:

| loophole | slot | effect | handled by |
|---|---|---|---|
| non-affine value | value | `D = φ ∘ F` with `φ` non-affine; log count may fail | B (affine `φ`); A needs R9 |
| varying shape data | shape | `D` itself changes with the value (`d = d(x)`, curve data vary) | B0 (constant) / B1 (affine); A open |

A construction can be B-legal on one and A-legal on the other. The `tan` catenary route is B1 on the
shape data (`d = λ`) and affine on the value (`x = λkπ`); it is fully B-legal. The parabola family is
B0 on the shape data (`d` is a fixed parameter of the family) and affine on the value. R7's `d = 0`
construction is B0 + affine. No known construction needs A on either slot.

### 1.6 The finite singular set

For the R9 handoff, record the relevant facts (R3 §3.3, extended):

- **Algebraic curves:** Puiseux branch points and poles; the singular set is finite.
- **Exp tower:** at a finite `u`, either analytic/algebraic (`β ≠ 0`, where the essential singularity
  of `exp` sits at `u = ∞`) or algebraic plus at most two log branch points (`β = 0`); finitely many
  singular points. [Proof: R3 Lemma 3.3]
- **Trig tower:** analytic or algebraic on the branch; finitely many singular points (the branch is a
  single interval). [Proof: R3 Lemma 3.3]
- **`offset`, affine, `restrict`:** preserve the class. [Proof: R3 §1.3–1.4]
- **`arc_of_length`:** adds finitely many log branch points (residues of the abelian differential);
  still finitely many singular points. [Proof: R3 §4.2]

So: **every tower graph function has only finitely many finite singular points**, of the types
{algebraic branch, pole, log}. This is a **tower** invariant. Its behaviour under value-side
composition is now known unevenly:

- **Log points:** protected by Lemma 1.2 when the monodromy is real — the parabola, `gd`, the
  involute, the rhumb and the beam interpolation. The local coefficient is then imaginary; a real
  `φ` cannot resolve it, only turn it into a pole. Those log rows are **A-robust**. The tractrix and
  Biot have complex monodromy and are **not** protected; `exp` resolves them.
- **`1/log`, `δlogδ`:** not protected. Real `φ` resolve them explicitly (§1.4). These rows are
  **B-only**.
- **Algebraic branch points and poles:** `z²` resolves a square-root branch point and `1/z` resolves
  a pole. The named targets do not have these as their infinite singularity set, but R9's taxonomy
  must record the caveat: a crude singular-set count is not enough on its own.

**Handoff.** R9 should classify singularities **under B**. The A-closure question is settled for log
with real monodromy (yes, Lemma 1.2) and settled negatively for `1/log`/`δlogδ` (no, by the explicit
resolving `φ`). If
the user chooses A, `tan` and `l = 0` need a *global* argument; the log rows do not. A global
argument would have to use more than the local singularity type — e.g. growth or a counting
condition on `φ ∘ F` — and is a separate programme.

---

## 2. The convention

### 2.1 Family kinds

A family is one of:

- **continuous:** a one-parameter interval `J ⊆ ℝ` of values `x`; the target is `F : J → ℝ`
  injective, `U = F⁻¹`. (The physical name of the parameter may be `λ`; the value is whatever the
  construction must output a function of. For `tan x = λx` with `k` fixed, the value is `λ` and the
  unknown is the root `x = kπ + ψ`.)
- **discrete:** a set `{x_m : m ∈ M}`, `M ⊆ ℤ`; the target is the sequence `u_m = F⁻¹(x_m)`. The mode
  `m` is a label, not the unknown.
- **hybrid:** a product, e.g. `ℝ × ℤ` for `tan` (continuous in `λ`, discrete in the branch `k`).
- **single:** one equation, one number; no uniformity.

### 2.2 Data classes

| tag | shape data | value map `φ` | use |
|---|---|---|---|
| **S** | fixed | fixed | single targets |
| **B0** | fixed (curve and `d`) | affine | rigidity, Route O necessity |
| **B1** | affine in the value | affine | general affine-data claims; `tan` Route O |
| **C** | P-constructible in `m` | P-constructible in `m` | discrete spectra |
| **A** | P-constructible in the value | P-constructible | existence; exclusion only for protected-log targets (Lemma 1.2) |

"Affine" means `α + βx` with `α, β` P-constructible and **not** depending on the unknown. B0 ⊂ B1 ⊂ A.
C is the discrete analogue of B1 (and A, depending on what is allowed in `m`); a hybrid uses B on the
continuous factor and C on the discrete one, written **B1×C**.

### 2.3 What "solves" means

A term **solves** the family if:

1. the same construction term (same curves, same combinatorics) is used for every value/mode;
2. every datum is in the declared class and is root-independent;
3. for each value the term is **legal**: the curve is regular on the window, the offset is cusp-free
   (`1 − dκ > 0`) where a cusp would break the readout, and the intersection/box output is **unique**
   on the window;
4. the output is the required `u(x)` (or `u_m`), up to a P-constructible algebraic readout.

Condition 3 is not cosmetic: a degenerate equation (e.g. an identically true one) is not a solution
even though every `u` satisfies it. This is what excludes the circle from the B1 discussion in §3.3.

### 2.4 Recommendation

> **B + C is the programme's convention.** B0 for rigidity-style necessity; B1 for affine-data
> necessity; C for discrete spectra; S for single targets. A is allowed for *existence* claims and
> for *conditional* claims explicitly labelled "under A, modulo R9".

Reasons:

1. **All known constructions are B-legal.** Catenary/`tan` (B1), involute (B0), beams (B0 + C),
   rhumb (B0), tractrix (B0), parabola (B0), `d = 0` (B0). No known route needs A.
2. **B is the hypothesis under which the *type-specific* invariants are preserved.** Log with real
   monodromy is A-robust (Lemma 1.2), but the `1/log`, `δlogδ`, complex-monodromy log and
   non-elementarity arguments are B-only. B gives a uniform proof; A would require a case split and a
   global argument for the non-log rows.
3. **B makes the open questions finite-dimensional.** B1 replaces "is `d(λ)` P-constructible?" by a
   4-function span condition on `R_C` (§3.3), which is a question about a curve, not about
   transcendence.
4. **A is not lost.** It is the right class for existence and for any future construction that is
   genuinely non-affine. A claim made under A is strictly stronger. The log rows can be upgraded to A
   via Lemma 1.2; the non-log rows need a separate global argument.

### 2.5 Ratification

```
[ ] B + C  (recommended)
[ ] A      (permissive; the 1/log, δlogδ and non-elementarity exclusions become
             conditional on a global argument; the log rows survive via Lemma 1.2)
[ ] other: ______________________________________________
```

The decision is prose, not a `Defs.lean` change. Until it is ratified, every R12 restatement below is
written under B + C and tagged.

---

## 3. Restatements under the convention

### 3.1 Route I under B

> **Lemma 3.1 (affine value maps preserve the log set) [Proof].** Let `F` be analytic on a domain,
> and let `φ(z) = az + b` with `a ≠ 0`. Then `φ ∘ F` has a finite log branch point at `u₀` iff `F`
> does, with the same monodromy multiplied by `a`.

**Proof.** Analytic continuation around `u₀` sends `F ↦ F + c` iff the monodromy is `c`; then
`φ ∘ F ↦ a(F+c)+b = (φ∘F) + ac`, and `ac ≠ 0` iff `c ≠ 0`. Local log terms are multiplied by `a`. ∎

> **Theorem 3.2 (Route I, B) [Proof].** Let `F` have infinitely many finite log branch points, and
> let `s` be a construction of output depth ≤ 2 whose only active step is one `inter_x`/`inter_y` or
> one `box`, with all data **B-affine** in the value. Then `s` does not solve `F` on any interval.

**Proof.** By (1.3.2), `D = φ ∘ F` with `φ` affine. By Lemma 3.1, `D` has infinitely many finite log
branch points. By R3 Lemma 3.3, a difference of tower graph functions (or a box readout) has only
finitely many. Contradiction. For the box, R3 Lemma 2.4 gives a piecewise-affine output, which is not
`φ ∘ F` for non-affine `F`; the same contradiction, or the direct `U` non-affinity argument of R3
Theorem 3.5. ∎

This is R3 Theorem 3.4/3.5 with the convention made explicit. **No new mathematics** beyond Lemma
3.1; the point is that the hypothesis is now stated in the same language as Definition 2.1.

**What changes under A.** Lemma 3.1 fails in general, but Lemma 1.2 gives a substitute for log
targets with real monodromy: any real `φ` preserves the singularity (as a pole), so `φ ∘ F` still
has infinitely many finite singular points and is not a graph difference. Thus Theorem 3.2's
*conclusion* survives A for those targets, with a pole-count argument instead of a log count. For
`1/log`/`δlogδ` targets, A is genuinely stronger and Theorem 3.2 has no A-version; that is the R9
scope split.

### 3.2 Route O under B0 (rigidity)

> **Theorem 3.3 (R2 rigidity, B0) [Proof].** Fix a drawable curve `C` and a constant `d`. If
> `R_C(ψ) − dψ = x` has the same solution `ψ(x)` as the target for every `x` in an interval, then
> `ρ_C − ρ_target ≡ 0`: `C` is a parallel of the target curve.

This is R2 Q3.3, unchanged. It is the B0 case: shape data constant, value `x` continuous. The
consequence table (R2 §Q3.3) is unchanged: the beam's **continuous interpolation** forces the
log-cosine, and the involute (`d = 1`) and rhumb (`d = k`) force the catenary/log-cosine; no base
curve qualifies. [Proof + Wolfram, R2] For `tan`, R2's fixed-`λ` computation is a B0 statement about
the continuous interpolation `tanψ − λψ`, not the discrete branch family; the `tan` family itself has
`d = λ` and is B1 (§3.3). This is exactly R8's "Q3.4 open" caveat, now given a convention tag.

### 3.3 Route O under B1 (the reduction)

Now let the shape data be affine in the value. Take a continuous family with target equation
`T(ψ, λ) = 0` (the value is `λ`; `ψ` is the unknown angle), a fixed or affinely varying curve `C`, and

```
R_C(ψ) − (aλ + b)ψ = cλ + e,        d = aλ + b,   X = cλ + e.                (3.3.1)
```

Differentiate (3.3.1) along the target branch `ψ(λ)` and use `T_ψ ψ' + T_λ = 0`:

```
ρ_C(ψ) = aλ + b − (c + aψ) T_ψ / T_λ .                                       (3.3.2)
```

Equation (3.3.2) is the **B1 differential condition**. It is a formula for the radius of curvature of
the candidate curve, hence (by the Whewell function) for the curve itself, up to congruence. If `T`
can be solved for `λ` as a function of `ψ`, (3.3.2) becomes a condition in `ψ` alone.

**The `tan` case.** `T(ψ,λ) = tanψ − λ(ψ + kπ)`, so `T_ψ = sec²ψ − λ`, `T_λ = −(ψ+kπ)`, and
`λ = tanψ/(ψ+kπ)`. Substituting:

```
ρ_C(ψ) = a tanψ/(ψ+kπ) + b + (c+aψ) sec²ψ/(ψ+kπ) − (c+aψ) tanψ/(ψ+kπ)² .    (3.3.3)
```

Integrating (3.3.1) at fixed `λ` gives the **zeroth-order B1 condition**:

```
R_C(ψ) = bψ + e + (aψ + c) · tanψ/(ψ + kπ) .                                 (3.3.4)
```

So, with `T₀(ψ) := tanψ/(ψ+kπ)`, the B1 question for `tan` is:

> **Does `R_C` lie in the linear span of `{ψ, 1, ψT₀, T₀}`?** If not, no B1 configuration with that
> curve solves `tan x = λx`. If yes, the coefficients are `(a,b,c,e)`; the construction is
> non-degenerate iff the resulting equation is not identically true.

**Checks [Wolfram, §6 cells 4–6].**

- Catenary `R = tanψ = ψT₀ + kπT₀`: in the span with `(a,b,c,e) = (1,0,kπ,0)`. The equation is
  `tanψ − λψ = λkπ`, the target itself. ✓
- Log-cosine `R = gd⁻¹ψ = log(secψ+tanψ)`: the 5×5 Wronskian of
  `{ψ, 1, ψT₀, T₀, R}` is nonzero. **Not in the span** — the log-cosine is not a B1 solution for
  `tan`. This is the expected asymmetry: the log-cosine solves the beam/rhumb, not `tan`.
- The same Wronskian is nonzero for the parabola (`R = ½(tanψ secψ + gd⁻¹ψ)`), Neile
  (`R = ⅓sec³ψ`) and exp (`R = secψ − arctanh(cosψ)`) [Wolfram, with symbolic `K`; hence for all but
  possibly finitely many exceptional `k`, which are checked by evaluation]. So none of the base
  catalogue is a B1 solution for `tan` with constant coefficients.
- Circle `R = ψ`: in the span with `(a,b,c,e) = (0,1,0,0)`, but the equation is `ψ − ψ = 0`,
  identically true — **degenerate**, excluded by condition 3 of §2.3.
- The differential form (3.3.3) reproduces `ρ = sec²` exactly for the catenary (residual `0`), and the
  derivative identity (3.3.2) is an identity (residual `0`). ✓

**What is proved and what is open.**

- **Proved:** the B1 condition is (3.3.4); the catenary is a solution; the log-cosine is not; the
  circle is only a degenerate solution. [Proof + Wolfram]
- **Open:** whether a **tower curve beyond the base catalogue** has `R_C` in the span, or `ρ_C`
  satisfying (3.3.3), for some `k`-dependent `(a,b,c,e)`. The base catalogue is excluded by the
  Wronskian checks above; the remaining class is the offset/affine/`exp` tower. The span is
  4-dimensional, so this is a finite linear-algebra question for each candidate curve. Handed to R10
  (catalogue) and R9 (if the answer needs the singularity spectrum).
- **Consequence for `tan`:** R5's "M catenary" is B1-sufficient; B1-necessity is **open**, but now a
  concrete functional-equation question, not R2 Q3.4's constructibility question.

**Other named rows under B1.** The involute (`d = 1` constant, value `k`), rhumb (`d = k` constant,
value `c`), tractrix (`d` constant), beams (`d = ∓1` constant, value `c` or `m`) are all **B0**: the
shape data do not depend on the value. So Theorem 3.3 applies and the R2 table stands. Only `tan`
(and any other family where the offset is tied to the value) is genuinely B1.

### 3.4 What B does not close

1. **B1 Route-O necessity.** The functional equation (3.3.2)/(3.3.4) is not solved for a general
   target. `tan` is the open case (§3.3). B1⁺ (curve affine data also affine in the value) is larger
   and also open; no known construction needs it.
2. **A on either slot.** Existence claims are fine. The log rows with real monodromy (7, 10, and the
   beam interpolation) are A-robust (Lemma 1.2); the `1/log`, `δlogδ`, tractrix/Biot and
   non-elementarity rows need a global argument, not a local singularity classification.
3. **C.** Discrete spectra are untouched by the interval argument.
4. **The full-tower catenary/log-cosine question** (issue 18 item 2). B does not decide whether a
   catenary or log-cosine parallel is in the tower; that is a constructor-reachability question,
   unchanged.

### 3.5 The `d = 0` case under B

R7's construction is B0 + affine: `d = 0` is constant, the value enters as `translate_y` by `x`
(affine). It is a single `inter_x`, depth 1. The target `F₀` is entire, so Theorem 3.2's hypothesis
(infinitely many finite log branch points) fails, and there is no contradiction: the theorem is
correctly silent, and the construction exists. B changes nothing here. [Proof, R7]

---

## 4. The template, filled in

### 4.1 Revised template

```
Target:            <equation / named problem>
Family:            continuous | discrete | hybrid | single
Value:             <x / λ / m; what the construction outputs a function of>
Unknown:           <the root>
Convention:        S | B0 | B1 | C | B1×C | A

Route O:
  construction:    <curve C, offset d, length X; legality: cusp-free window?>
  necessity:       <B0 -> parallel (R2 Q3.3) | B1 -> (3.3.2)/(3.3.4) | open>
Route I:
  decomposition:   <F = g1 - g2, both drawable>
  or exclusion:    <invariant: log | full spectrum | non-elementarity>
  hypotheses:      <B-affine value? continuous? tower class?>

Verdict:           R | I-excluded | O-suff (B0/B1) | open (which slot) | S-legality
```

The additions to the plan's template are **Family**, **Value**, **Convention**, and the explicit
sub-case labels. The rest is unchanged.

### 4.2 R5's table under the template

`Fam`: `cont` = continuous, `disc` = discrete, `hyb` = hybrid, `sing` = single.
`O-nec`: `B0` = rigidity, `B1` = open.
`I`: `ex` = excluded, `op` = open, `R` = reachable, `n/a`.

| # | target | Fam | Conv | Route O (construction / necessity) | Route I | verdict |
|---|---|---|---|---|---|---|
| 1 | optimal projectile | sing | S | — | — | **R** |
| 2 | rainbow angle | sing | S | — | — | **R** |
| 3 | catenary of given length | sing | S | — | — | **R** |
| 4 | Neile, `d = 0` | cont | B0 | Neile, `d = 0` (collapses) | R | **R** |
| 5 | clothoid | cont | B0 | clothoid (collapses) | R | **R** |
| 6 | `tan x = λx` | hyb | **B1×C** | catenary, `d = λ`, `X = λkπ` / **B1 open** | **op** (`1/log`) | **open both** |
| 7 | gear involute | cont | B0 | catenary, `d = 1`, `X = k` / B0 | **ex** (log) | **I-excluded** |
| 8 | cantilever beam | disc (+ cont interpolation) | **B0 + C** | log-cosine, `d = −1`, `X = (2m+1)π` / B0 for interpolation, C open | interpolation **ex**; spectrum **op** | **mixed** |
| 9 | clamped–clamped | disc (+ cont interpolation) | **B0 + C** | log-cosine, `d = 1`, `X = 2mπ` / as row 8 | as row 8 | **mixed** |
| 10 | rhumb (fixed `k`) | cont | B0 | log-cosine, `d = k`, `X = c` / B0 | **ex** (log) | **I-excluded** |
| 11 | pendulum separatrix | sing | S | — | **R** (pointwise `gd`) | **R** |
| 12 | goat | sing | S | formal, `d = 1`, `X = π/2` / **legality open** | `n/a` | **S-legality** |
| 13 | tractrix | cont | B0 | tractrix, `d` fixed / B0 | **ex** (log) | **I-excluded** |
| 14 | Euler elastica | cont | B0 | elastica, `d` fixed / B0 | **ex** (non-elementarity) | **I-excluded** [standard] |
| 15 | spherical well `l=0` | cont | B0 | no curve | **op** (`δ log δ`) | **open both** |
| 16 | Biot | cont | B0 | not (OI) | **ex** (log) | **I-excluded** (no O) |
| 17 | aberration | sing | S | — | — | **R** |
| 18 | caustics | sing | S | — | — | **R** |
| 19 | `tan x = x` quartic | sing | S | — | Route-I with missing curves; not excluded | **I with missing curves** |
| 20 | Laplace limit | sing | S | — | — | **R** |

### 4.3 Convention sensitivity

- **Settled under B0** (no change): 7, 10, 13, 14, 16. These are the rows where
  "intersection-impossible" is safe under B0; 13/14/16 weaken under A (§ below).
- **Convention-critical:** 6 (`B1` + `1/log`), 8/9 (`B0` continuous vs `C` discrete), 15 (`δ log δ`),
  19 (Route-I with other missing curves). These are the rows where a claim must name its convention
  or it is meaningless.
- **Would weaken under A:** rows 6, 13, 14, 15, 16. Rows 6/15 are `1/log`/`δlogδ`; row 13 (tractrix)
  and row 16 (Biot) have complex log monodromy, so `exp` resolves their log points; row 14
  (non-elementarity) can be composed by a non-elementary P-constructible `φ`. Under A these become
  "conditional on a global argument".
- **A-robust:** rows 7 and 10 (log with real monodromy, Lemma 1.2), and the beam continuous
  interpolation in 8/9.
- **Unaffected:** S rows (1, 2, 3, 11, 12, 17, 18, 20) and R rows.

---

## 5. Consequences for the other streams

- **R9 (singularity spectrum).** Classify the finite singularities of tower graph functions —
  including `1/log` and `δ log δ` — **under B**. The A-status is uneven: log points with real
  monodromy are A-robust (Lemma 1.2), while `1/log`, `δlogδ`, and log points with complex monodromy
  (tractrix, Biot) are B-only, because real `φ` resolve them (§1.4). So R9's non-log results are
  B-theorems; its protected-log results may be upgraded to A. If the user chooses A, `tan`, `l = 0`,
  the tractrix and Biot need a global argument, not a local one.
- **R10 (decomposition dictionary).** Constructions may be stated under A (they are existence
  results), but any claim that a curve *fails* to be a B1 solution must use (3.3.2)/(3.3.4) and say
  so. The base-catalogue B1 test (does `R_C` lie in `span{ψ,1,ψT₀,T₀}`?) is a concrete R10 task.
- **R11 (discrete spectra).** C is now defined: fixed term, data P-constructible in `m`, unique
  readout per mode. The `sine` example (`u ↦ u + sin u` is a drawable graph function) shows no
  analytic invariant can exclude a discrete spectrum; only arithmetic can.
- **IDX (standing index).** Use the §4.1 template; the four new fields are mandatory.
- **R13 (goat).** S: no uniformity, only legality. The convention does not apply; the pole/fold
  question is a `Defs`-hypothesis question.
- **R5/SUMMARY.** The `M` legend should point to this file for the convention and to R8 for the
  route audit. No label changes are forced by R12; the table in §4.2 is the reference.

---

## 6. Wolfram cells

All values are Wolfram Language, 40-digit working precision. One computation per call; session state
does not persist.

| cell | check | result |
|---|---|---|
| 1 | `Sin[2 ArcTan[E^u] − π/2] − Tanh[u]` | `0` |
| 1 | `Cos[2 ArcTan[E^u] − π/2] − Sech[u]` | `0` |
| 1 | `Series[Tanh[iπ/2 + z], {z,0,1}]` | `1/z + z/3 + …` (a pole at the branch point) |
| 1 | `Sin[−i log z] − i/(2z) + i z/2` | `0` (a pole, not an essential singularity) |
| 2 | `∮ F'(u) du` around `u₀ = iπ/2`, `d = 1/2`, radius `1/10` | `−3.14159265358979323846…` = `−π` = `−2πd` (imag residual `10⁻⁵⁶`) |
| 3 | `Sin[(F − 2πd)/d] − Sin[F/d]` | `0` (the period that kills the monodromy) |
| 4 | `(ρ − aλ − b)ψ' − aψ − c` with `ψ' = (ψ+kπ)/(sec²ψ − λ)` and `ρ` from (3.3.2) | `0` |
| 5 | (3.3.3) at `(a,b,c) = (1,0,kπ)` minus `sec²ψ` | `0` |
| 5 | (3.3.3) with `b = 1−a`, `c = akπ` minus `sec²ψ` | `(a−1) tan²ψ`; zero iff `a = 1` |
| 6 | 5×5 Wronskian of `{ψ, 1, ψT₀, T₀, R}` for `R = tanψ` | `0` (catenary in the span) |
| 6 | the same for `R = ψ` | `0` (circle in the span, degenerate) |
| 6 | the same for `R = log(secψ+tanψ)` | nonzero (log-cosine not in the span) |
| 6 | the same for `R = ½(tanψ secψ + log(secψ+tanψ))`, `R = ⅓sec³ψ`, `R = secψ − arctanh(cosψ)` | nonzero (parabola, Neile, exp not in the span) |

The Wronskian computations are the standard linear-independence test; a nonzero value on an interval
is a proof of non-membership in the span. The `a = 1` factor in cell 5 is the uniqueness of the
catenary's B1 representation among curves with `ρ = sec²`.

---

## 7. Open items and handoff

1. **Ratify B + C** (§2.5). Until then, R9 may still close A; B is the safe default.
2. **R9:** the singularity classification under B: `1/log`, `δ log δ`, log, poles, algebraic
   branches. Log with real monodromy is A-robust (Lemma 1.2); `1/log`, `δlogδ` and complex-monodromy
   log points are B-only, so a choice of A leaves `tan`, `l=0`, the tractrix and Biot needing a global
   method.
3. **R10:** the base-catalogue B1 test for `tan`: for each base curve, is `R_C` in
   `span{ψ, 1, ψT₀, T₀}`? A nonzero 5×5 Wronskian excludes it.
4. **R11:** the discrete formulation C is ready; the arithmetic question is unchanged.
5. **R2 Q3.4** can now be restated: "B1 necessity for `tan`" instead of "is `(R_C(ψ_λ) − x(λ))/ψ_λ`
   P-constructible?". The former is a functional equation; the latter was a constructibility
   question. They are equivalent under B1, and the former is the useful form.
6. **No Lean change.** The convention is prose. The only formalizable fragment is the algebraic part
   of R3's Q1 (closure of the normal form), already noted in R3 §5.4.
