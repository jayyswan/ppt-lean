# NOTES — Jacobi R1c: arc lengths of `sine` and `exp_two` chains

Task: `PLAN-jacobi-R1c-transcendental-chains.md`. Scope: only the `sine` base
(`y = sin x`) and the `exp_two` base (`y = 2^x`), closed under constructible linear
maps, translations and `offset`. Question: is there a drawable curve in this class whose
arc length is exactly `α F(φ(T), c) + β`?

**Verdict (short).** No curve in this class has arc length `α F(φ, c) + β` with an
*algebraic* reparametrisation `φ`. Every arc-length 1-form in the class has a genuine
double pole at the "end" of the base parameter, with a coefficient that is the leading
`√Q_n` coefficient and that **no** translation, linear map or offset can change. The
`offset` corrections are *regular* there, so they cannot cancel it, regardless of the
genus or isogeny class of the auxiliary curves they introduce. This is a clean
useful-negative; it is the transcendental analogue of the `s − B` obstruction (F2) and of
the ellipse/polynomial conclusions.

All scripts are in `archived files/jacobi-scripts/` and are cited inline. "symbolic" means
`simpy` returned exactly `0` / an exact antiderivative; "numeric" gives the number of
digits to which two independently computed quantities agreed.

---

## Step 1 — `sine` under a constructible linear map

Parametrise `γ(x) = A·(x, sin x) + b`, `A = [[a,b],[c,d]] ∈ GL₂(ℝ)`. Then

    v(x) = γ'(x) = A·(1, cos x),    |v|² = Q_A(w) = q₀ + q₁ w + q₂ w²,   w = cos x,
    q₀ = a²+c²,   q₁ = 2(ab+cd),   q₂ = b²+d².                                    (1.1)

(1.1) is **symbolic** (`r1c_01_sine_linear.py`: `simplify(speed²−Q_A)=0`).

With `dw = −sin x dx` the arc-length 1-form is

    Ω = √(Q_A(w)) dx = √(Q_A(w)) · dw/√(1−w²) = Q_A(w)/y · dw,
    y² = (1−w²) Q_A(w).                                                            (1.2)

`y² = (1−w²) Q_A(w)` is a smooth genus-1 curve `E_A`: the roots `±1` are real and the two
roots of `Q_A` are complex conjugate, because

    disc(Q_A) = q₁² − 4 q₀ q₂ = −4 det(A)² < 0        for nonsingular A.          (1.3)

(1.3) is **symbolic** (`r1c_04_step4.py`). For singular `A` the image of the graph is a
straight line and the arc length is elementary — nothing elliptic is available there.

**Pole at `w = ∞`.** Put `u = 1/w` and `y = s·i√q₂ · u⁻² h(u)`, `s = ±1`, `h(0)=1`. Expanding
`h(u) = 1 + (q₁/2q₂)u + O(u²)` gives

    Ω = −(1/(s i √q₂)) · [ q₂ u⁻² + (q₁/2) u⁻¹ + O(1) ] du.                       (1.4)

Hence at each of the two points over `w = ∞`:

* the **residue** is `−q₁/(2 s i √q₂)`, nonzero iff `q₁ = 2(ab+cd) ≠ 0`: a third-kind
  (logarithmic) part;
* the **double pole** coefficient is `√q₂/(s i) ≠ 0` for every nonsingular `A`
  (`q₂ = b²+d² > 0`): a genuine second-kind / boundary term.

(1.4) was obtained symbolically and the residue formula checked against an independent
numeric expansion to 20 digits (`r1c_01_sine_linear.py`, e.g. `A=(0.9,0.44,−0.31,1.27)`:
`q₁=0.0046`, `res=0.00171123184289841978i`).

**Answer to the step-1 question ("are there maps making the second-kind part vanish?").**
No. Choosing `A` with orthogonal rows (`ab+cd = 0`, e.g. every rotation or scaled rotation,
`A = ρR`) forces `q₁ = 0` and kills the log part, but the double pole `q₂ u⁻²` is present
for **every** nonsingular `A`. The form is therefore
`(first-kind class) + (exact boundary term) + (log, if q₁≠0)`, never a pure first-kind
form. For `A = I`, `Ω = (1+w²)/y dw` on `y² = 1−w⁴`, matching the overview's "E-type for
`y = A sin x`"; the boundary term is the `√(1−w²)`-free piece.

---

## Step 2 — adding offsets

Write `v = (v_x, v_y)` and `v × v' = v_x v'_y − v_y v'_x`. For the sine base
`v = (1, cos x)`, `v' = (0, −sin x)`, so

    (v × v') dx = −sin x dx = dw.                                                   (2.1)

**One offset after a map `A`.** The exact speed of `A·(x,sin x)` pushed `d` along its unit
normal is

    |η'| = √(Q_A(w)) · | 1 − d · det(A) · (v×v') / Q_A(w)^{3/2} |.                  (2.2)

This was verified **symbolically** with a concrete rational `A` (`speed² − form²` simplifies
to `0`) and **numerically to 25 digits** (`r1c_02_offsets.py`). The correction 1-form is,
by (2.1),

    −d det(A) · √Q_A / Q_A^{3/2} · (v×v') dx = −d det(A) · dw / Q_A(w),             (2.3)

which is rational in `w`, hence **elementary** (e.g. `∫ −d detA dw/(1+w²) = −d detA·arctan w`,
verified symbolically). It contains no `√(1−w²)` and no elliptic content.

**Chains of offsets.** The iterated formula (F3),
`ds_n = √Q_n(v)[1 − Σ_k d_k det A_(k)(v×v')/Q_k(v)^{3/2}]dx`, with cumulative linear parts
`A_(k)` and `Q_k(v)=|A_(k)v|²`, was checked against **complex-step finite differences to 25
digits** for a two-offset chain `A_2 ∘ off_{d₁} ∘ A_1 ∘ off_{d₀}` (`r1c_02_offsets.py`).

**Why offsets cannot cancel the step-1 pole.** Using (2.1), the `k`-th correction 1-form is

    −d_k det A_(k) · √(Q_n(w)) / Q_k(w)^{3/2} · dw.                                 (2.4)

At `w = ∞`, `√Q_n/Q_k^{3/2} = O(w⁻²)`, so (2.4) is `O(w⁻² dw)`, i.e. **regular** at
`w = ∞` (`w⁻²dw = −du` in `u = 1/w`). Meanwhile the bracket in (F3) tends to `1` there, so
the leading term is exactly `√Q_n dx ~ const·dw`, whose double pole has coefficient
`√(q₂^n)/(s i) ≠ 0`. A regular form cannot cancel a pole at a point, so

> offsets add only corrections that are regular at the sine pole; they can never remove it.

This holds before any question of the auxiliary curve's genus or isogeny class arises.
(There *is* genus in (2.4): after rationally parametrising the conic `Y²=Q_n(w)`, the
integral becomes `∫ W(m)/V(m)^{3/2} dm` with `V` a quartic; for generic `Q_n ≠ const·Q_k`,
`V` is squarefree — checked in `r1c_03_exp_two.py` in the analogous `2^x` setting — so the
correction is generically an elliptic integral. It is still regular at the pole, so it
cannot help.)

---

## Step 3 — the `2^x` base

Put `z = 2^x`. Then `v = (1, (ln 2) z)` and

    |v|² = Q_A(z) = q₀ + q₁ z + q₂ z²  (quadratic),     dx = dz/(z ln 2),
    ds = √(Q_A(z)) · dz/(z ln 2).                                                   (3.1)

`Y² = Q_A(z)` is a **conic**, hence genus 0, so (3.1) is **elementary**. Explicitly, the
conic parametrisation `Y = z + m` (rational point at infinity) turns the integrand into a
rational function; `sympy` returns an exact elementary antiderivative (rational + logs) —
`r1c_03_exp_two.py`, `r1c_04_step4.py`. This confirms the plan's "genus 0 plus logs".

**One offset** after `A`. Here `v' = (0,(ln2)²z)` and `(v×v')dx = (ln2)² z · dz/(z ln 2) =
ln 2 · dz`, so the correction is

    −d det(A) · ln 2 · dz / Q_A(z),                                                  (3.2)

again elementary (`r1c_03_exp_two.py`: `∫ dz/(1+3z+2z²) = log(z+½) − log(z+1)`).

**Two offsets reach genus 1.** The `k`-th correction now is
`−d_k det A_(k) ln 2 · √Q_n/Q_k^{3/2} dz` with `√Q_n = Y` on `Y²=Q_n(z)` and `W²=Q_k(z)`.
Parametrising the conic `Y²=Q_n(z)` rationally (`Q_n = 1+z+z²`, `Q_k = 2+3z+z²`, chosen with
nonzero linear terms) gives `∫ W(m)/V(m)^{3/2} dm` with

    V(m) = m(m−2)(m²−4m+1),     disc(V) = 432 ≠ 0,

so `V` is squarefree and the correction is a genuinely **genus-1** (elliptic) integral
(`r1c_03_exp_two.py`, verified symbolically including the factorisation and discriminant).
Equivalently, the curve `Y²=Q_n(z), W²=Q_k(z)` is a smooth intersection of quadrics in `P³`.

**Kinds and obstruction.** The base and every single-offset term are genus 0; only from the
*second* offset onward does an elliptic piece appear, and it is generically a second/third
kind differential. But the leading term `√Q_n dz/(z ln 2)` still has:
a double pole at `z = ∞` with coefficient `√q₂^n/(ln 2) ≠ 0`, and a log at `z = 0`. The
corrections (3.2) are `O(dz/z²) = O(du)`, **regular at `z = ∞`**, and finite at `0`. So the
double pole survives, exactly as for the sine base.

---

## Step 4 — can an algebraic reparametrisation absorb `√(1−w²)`?

No. `Q_A` is **positive definite**: `disc(Q_A) = −4 det(A)² < 0`, so `Q_A(±1) > 0` and `Q_A`
is never divisible by `1−w²` (`r1c_04_step4.py`, symbolic; also
`Q_A(±1) = (a±b)² + (c±d)²`). Hence `√(Q_A/(1−w²))` always has the `w = ∞` pole; it cannot
be rewritten as a rational (or holomorphic) function of `w`. The same argument gives
`Q_A(z) ≠ const·z²`, so the `2^x` leading term keeps its `z = ∞` double pole.

**General obstruction for any algebraic `φ`.** Suppose a constructible curve `C` in the
class satisfies `s_C(T) = α F(φ(T), c) + β` with `α, β` real and `φ` algebraic. Differentiate
along the parameter `t` (with `w = cos x` or `z = 2^x` as local coordinate on the
compactified parameter sphere):

    ds_C = α · dφ / Δ_c(φ),      Δ_c(φ) = √((1−φ²)(1−c²φ²)).                       (4.1)

At a point where `φ` is finite and `Δ_c(φ) ≠ 0`, the right side is regular. Where
`Δ_c(φ)=0`, `φ` equals `±1` or `±1/c`; writing `φ−φ₀ ~ u^k` in the local parameter `u`,
`dF(φ) ~ u^{k/2−1} du`, which is regular for `k ≥ 2` and a branch-type (half-integer)
singularity for `k = 1` — never a pole. At a pole of `φ`, `φ ~ u^{−m}` (`m ≥ 1`),
`dF(φ) ~ dφ/φ² ~ u^{m−1} du`, which is **holomorphic or zero**, never a pole. Therefore
`α dF(φ)` never has a double pole at the base end. Since every `ds_C` in the sine and
`2^x` classes does (Step 1, (1.4), and Step 3), no algebraic `φ` can satisfy (4.1).

This is the decisive statement, and it is why the construction cannot be completed by the
single-curve route even when `q₁ = 0` removes the logarithmic part: the boundary/double-pole
term is irreducible.

---

## Step 5 — Verdict, assumptions, loopholes

**Verdict.** Drawable curves built from `sine` or `exp_two` by constructible linear maps,
translations and offsets do **not** have arc length `α F(φ, c) + β` with algebraic `φ`.
The arc-length 1-form has a non-holomorphic double pole at the end of the parameter
(`w = ∞` for `sine`, `z = ∞` for `exp_two`); its coefficient is the leading `√Q_n`
coefficient, invariant under translations and offsets (whose corrections are regular
there) and nonzero for every nonsingular linear map. Choosing orthogonal-row maps
(`q₁ = 0`, e.g. rotations / scaled rotations) removes the third-kind (log) part only.

**Assumptions.**
1. `φ` is algebraic (a rational/algebraic constructible function of `w` or `z`).
2. Single-curve route: one drawable curve, one reparametrisation. Composition routes (R3)
   and the ellipse/polynomial classes (R1a/R1b) are outside scope.
3. Nonsingular linear maps (singular maps give a straight-line image, elementary arc
   length, no elliptic content).
4. Offsets of finite order (an infinite chain is not a constructor).

**Loopholes not covered.**
* A **non-algebraic constructible `φ`**. The pole argument only rules out algebraic `φ`.
  If `φ` were allowed to be an arbitrary constructible function, (4.1) becomes essentially
  the definition of the amplitude, so any solution would be circular unless it built `am`
  from the other primitives. The allowed primitives in `Defs.lean` give no candidate.
* **`restrict`** does not help: it only changes the definite limits of the integral; the
  indefinite integral still carries the boundary/double-pole term.
* **Nonlinear constructible reparametrisations** of the base before offsetting (not in the
  stated closure of this task) are not analysed here.
* The **finite/regular part** of the forms: we have not shown the elliptic pieces are
  incapable of contributing an independent `F`; we have only shown they cannot remove the
  double pole, which suffices to exclude the exact `αF(φ,c)+β` shape.

**Verification summary** (`archived files/jacobi-scripts/`):

| identity | status | script |
|---|---|---|
| `speed²(A·(x,sin x)) = q₀+q₁w+q₂w²` | symbolic (0) | `r1c_01_sine_linear.py` |
| expansion (1.4), residue `−q₁/(2si√q₂)` | symbolic + numeric 20 digits | `r1c_01_sine_linear.py` |
| one-offset speed identity (2.2) | symbolic + numeric 25 digits | `r1c_02_offsets.py` |
| two-offset (F3) chain formula | numeric 25 digits | `r1c_02_offsets.py` |
| `∫√Q_A(z)/z dz` elementary (genus 0) | symbolic exact | `r1c_03_exp_two.py`, `r1c_04_step4.py` |
| two-offset quartic `V`, `disc=432≠0` (genus 1) | symbolic exact | `r1c_03_exp_two.py` |
| `disc(Q_A) = −4 det(A)²` | symbolic exact | `r1c_04_step4.py` |

**Bottom line.** A useful negative: this class is excluded from the single-curve route for
the same reason as the cubic-graph (`s−B`) and ellipse/polynomial classes — an
irreducible boundary (double-pole) term. The only way `sine`/`exp_two` could still
contribute is through a non-algebraic constructible reparametrisation that already encodes
`am` (composition route), which is exactly what R2/R3 address.
