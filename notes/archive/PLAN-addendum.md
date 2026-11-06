# Addendum to PLAN.md: triage of the remaining `sorry`s

**Status (2026‑09‑26).** `Certificate.lean` has no errors, but it still has 4 `sorry`s, and
`Main.lean` has 1. The implementation agents flagged several statements as false. This note
says which of those findings are real and what to do next.

**RESOLVED (2026‑09‑26).** All five `sorry`s are gone and `Pptc.TotallyReal` builds. The work
split A–G was carried out as follows.

| # | Deliverable | Where it landed |
|---|---|---|
| A | `signChange_of_simpleRoot` (derivative) and `signChange_of_factorization` / `_eventually` | new file `Pptc/TotallyReal/SignChange.lean` |
| — | compact-uniform tube lemmas (`exists_nhds_forall_lt`/`_ne`, `_of_continuousAt`, finite forms) | new file `Pptc/TotallyReal/OpenTube.lean` |
| B | `centre7_chain_signs`, `centre8_chain_signs` (strict sign change at every small radius, from explicit centre factorizations) | `Certificate.lean` |
| C | `exists_chain_roots_local` (local Lemma C: centre data → a neighbourhood of good inputs); its conclusion also exposes the two denominators | `Certificate.lean` |
| D | restated `exists_open_good7`/`exists_open_good8` (`ChainGood` + four nonvanishing witnesses, no `PConstructible`, no `S₁`); old `exists_chain_roots` deleted | `Certificate.lean` |
| E | `exists_PC_inputs_s1` (trace-corrected lift keeping all six slots in `V = {S₁ = 0}`) | `Certificate.lean` |
| F | `exists_oddTschirnhaus` re-assembled from D + E + `stepRoots_Pconstructible` + `chainBLift_Pconstructible_of_roots` | `Certificate.lean` |
| G | `root_Pconstructible_deg8_coeffs` removed; the degree-8 headline is `root_Pconstructible_totallyReal_eight`; nonreal-octic case recorded as future work in PLAN §5 | `Main.lean`, `Pptc/TotallyReal.lean`, PLAN §5 |
| §2.6 | dead-end refutation lemmas and stale section notes removed | `Certificate.lean` |

`axiom_check` on `exists_oddTschirnhaus`, `exists_open_good7/8`, `exists_chain_roots_local`,
`centre7/8_chain_signs` and on `root_Pconstructible_totallyReal_seven`,
`root_Pconstructible_deg7_coeffs`, `root_Pconstructible_totallyReal_eight` reports only
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`. The one remaining gap is the
nonreal-root octic (PLAN §5); it is off the critical path.

**Verdict.** None of them block Theorem 7 or the totally‑real Theorem 8. The false statements
come from how the Lean statements were phrased (fixed radius‑1/3 boxes, and `PConstructible`
demanded on an open set), not from the mathematics of PLAN §2. The one real gap, octics with
nonreal roots, is already listed as out of scope in PLAN §5.

---

## 1. The five `sorry`s

### 1.1 `exists_chain_roots` (Lemma C), `Certificate.lean` ~804

- **As currently stated, with `hpole1`/`hpole2`, it is probably true.** It follows from a
  standard compactness argument:
  - At `I₀`, the step‑1 roots in the closed interval form a compact set inside the open
    interval.
  - For `I` near `I₀`, the roots stay near that set.
  - Tube lemmas then carry the sign data and pole‑freeness over to `I`.
- The WARNING docstring above it is **out of date**. It asks for `hden1'`/`hden2'`, which are
  now present as `hpole1`/`hpole2`.
- **It is still the wrong lemma, because its hypotheses can never be supplied:**
  - `h2`–`h4` require sign changes for *every* earlier parameter in a radius‑`eps` box.
    `centre7_signs`/`centre8_signs` prove them only at the single centre point.
  - `hpole2` at radius 1/3 is *refuted* (`centre7_hpole2_false`, `centre8_hpole2_false`).
    The step‑3 pole is about 0.0825 from μ₀ for n = 7, and about 0.278 for n = 8.
- **Action:** replace it with the local Lemma C of §2.1 below. Do not try to prove the
  current statement.

### 1.2–1.3 `exists_open_good7` / `exists_open_good8`, ~2140 / ~2169

All three obstructions listed in the docstring are correct, and each one comes from the
formulation:

| Obstruction | Correct? | Resolution |
|---|---|---|
| `PConstructible lam ∧ …` for every `I` in an open `U` is impossible, since P‑constructible reals are countable | Yes | Remove these conjuncts. P‑constructibility is needed only at the P‑constructible lifted input, where `stepRoots_Pconstructible` (proved) supplies it. |
| Lemma C cannot be applied because of the step‑3 pole at radius 1/3 | Yes | This comes only from fixing the radius at 1/3. The denominators are nonzero *at the centre*, so they are nonzero on a small neighbourhood, and the local Lemma C needs nothing more. |
| `Injective (chainY …)` does not follow from radius‑1/3 witnesses | Yes | The local Lemma C gives witnesses within any ε of the centre roots. The output is continuous there and equals β\* at the centre, and "entries distinct" is an open condition. |

### 1.4 `exists_oddTschirnhaus`, ~3940

- This depends only on 1.2–1.3.
- There is one extra ingredient, S₁ = 0 on the inputs. `no_open_s1` shows correctly that this
  cannot be an open condition. It has to be enforced during the density step (§2.3).
- The docstring cites `exists_PC_inputs_s1`, which **does not exist yet**.

### 1.5 `root_Pconstructible_deg8_coeffs`, `Main.lean` ~623

- This is a **genuine gap**: separable octics that do not split over ℝ.
- It needs a degree‑8 analogue of `root_Pconstructible_of_nonreal_root`, which means rebuilding
  the Bring–Jerrard machinery in dimension 7. That is a new result.
- **It is off the critical path.** PLAN §5 already excludes it, and the Γ targets
  (N = 15, 17) are totally real.
- `root_Pconstructible_totallyReal_eight` has no `sorry` of its own. It depends only on
  `exists_oddTschirnhaus`.

---

## 2. Next steps

### 2.1 Local Lemma C (the only substantial new analysis)

Restate Lemma C the way PLAN §2.5 intends: data **at the centre only**, and a conclusion for
**every** ε. Sketch:

```lean
/-- sign change at every small radius from a simple root -/
theorem signChange_of_simpleRoot {f : ℝ → ℝ} {x₀ d : ℝ}
    (hf : HasDerivAt f d x₀) (h0 : f x₀ = 0) (hd : d ≠ 0) :
    ∀ ε > 0, ∃ δ, 0 < δ ∧ δ < ε ∧ f (x₀ - δ) * f (x₀ + δ) < 0

theorem exists_chain_roots_local (I₀ : ChainYInputs n) (c₁ c₂ c₃ c₄ : ℝ)
    -- the four steps vanish at the centre roots
    (h1 : chainStep1' I₀ c₁ = 0) (h2 : chainStep2' I₀ c₁ c₂ = 0) (h3 : …) (h4 : …)
    -- simple roots in the last variable, at centre values of the earlier ones
    (hd1 : ∃ d ≠ 0, HasDerivAt (chainStep1' I₀) d c₁) (hd2 : …) (hd3 : …) (hd4 : …)
    -- denominators nonzero at the centre only
    (hden1 : yNBY (chainP I₀ c₁) I₀.g ≠ 0)
    (hden2 : yBdotY (chainP I₀ c₁) (chainD I₀ c₁ c₃) (chainD I₀ c₁ c₃) ≠ 0) :
    ∀ ε > 0, ∃ U, IsOpen U ∧ I₀ ∈ U ∧ ∀ I ∈ U, ∃ lam x mu kappa,
      |lam - c₁| < ε ∧ |x - c₂| < ε ∧ |mu - c₃| < ε ∧ |kappa - c₄| < ε ∧
      ChainGood-equations-and-denominators I lam x mu kappa ∧
      -- sign-change witnesses at the found roots, for `hne1`–`hne4`
      (∃ t, chainStep1' I t ≠ 0) ∧ …
```

**Proof outline.**

1. Work backwards through the steps. For each step k, use the helper to pick δₖ < (the
   neighbourhood size required by step k+1) with a strict sign change at `cₖ ± δₖ` at the
   centre.
2. Joint continuity at the two points `(I₀, c_{<k}, cₖ ± δₖ)` gives a neighbourhood on which
   those signs persist. Continuity comes from `ContinuousAt` of the rational step functions,
   since the denominators are nonzero at the centre and hence nearby. Only `ContinuousAt` at
   finitely many points is needed; no uniformity over boxes.
3. Work forwards with the IVT (`exists_zero_of_sign_change_on`, already in the file) on
   `[cₖ − δₖ, cₖ + δₖ]`.

**Discharging `hd1`–`hd4` at the centres.** At the centre each step is an explicit
rational‑coefficient polynomial in its own variable (with a nonzero denominator for step 3).
Deriving `HasDerivAt` term by term is heavy, so write it instead as a factorization
`F(t) = (t − cₖ) · G(t)` with `G(cₖ) ≠ 0`, checked by `ring_nf`/`norm_num`. PLAN §2.4 gives
the exact nonzero derivative values to check against.

- The factorization gives the sign change at all small radii directly: `G` is continuous and
  nonzero at `cₖ`.
- So the helper can take `(hfac : ∀ t near cₖ, F t = (t − cₖ) * G t) (hG : ContinuousAt G cₖ)
  (hG0 : G cₖ ≠ 0)` in place of `HasDerivAt`. Pick whichever turns out easier in practice.

Delete the old `exists_chain_roots` and its WARNING once this lands. Keep the IVT helper
`exists_chain_roots_at_centre` if it is reused.

### 2.2 Restate `exists_open_good7/8`

- **New conclusion:** `∃ U, IsOpen U ∧ centre ∈ U ∧ ∀ I ∈ U, ∃ lam x mu kappa,
  ChainGood I lam x mu kappa ∧ (hne1 … hne4 data)`. There are **no** `PConstructible`
  conjuncts and no S₁ conjunct.
- **`Injective`:** choose ε in Lemma C so that the output stays in a neighbourhood of β\*
  where the entries are distinct. This uses continuity of `chainY` in
  `(I, lam, x, mu, kappa)` near the centre, and that `chainY centre roots = β*` (injective).
- **`hne3`:** it is stated on `chainStep3Cleared`, which equals `denominator³ · chainStep3'`.
  The denominator is nonzero near the centre, so the sign‑change witness transfers.

### 2.3 Density lift that keeps S₁ = 0 (PLAN §2.6)

This is new: `exists_PC_inputs_s1`, or fold it into `exists_Pconstructible_lift`.

- **The correction.** Let π(b) := b − (S₁(y(b))/n)·e₀, where e₀ is the constant polynomial 1,
  so y(e₀) = (1, …, 1). Then:
  - y(π b) ∈ V for every b;
  - π is continuous;
  - π preserves P‑constructibility, because S₁(y(b)) is P‑constructible by
    `psum_yvec_Pconstructible`.
- **The lift.** The preimage of U under `chainBtoY ∘ π⁶` is open. It is nonempty, because the
  centre lies in V⁶ (`centre7_s1`, `centre8_s1`), so π fixes a preimage of it. The existing
  slice‑by‑slice density argument then yields rational b's in the preimage, and applying π
  keeps them P‑constructible.
- **Alternative:** build the projection onto V into the chain definitions, so that S₁ = 0 is
  an identity for all inputs. That makes `s1_closed`/`no_open_s1` irrelevant, but touches more
  definitions.

### 2.4 Assembly: `exists_oddTschirnhaus`

- Rework `exists_b_good_of_PC_roots`. It should take the §2.2 open set, lift with §2.3, and
  **then** call `stepRoots_Pconstructible` on the lifted P‑constructible input, using the
  `hne` data.
- After that, `chainBLift_Pconstructible`, `chainBLift_yvec` and `exists_open_good_of_s1`
  finish it as they do now.

### 2.5 `Main.lean`

- Restrict `root_Pconstructible_deg8_coeffs` to the split (totally real) case, or delete it
  and keep `root_Pconstructible_totallyReal_eight` as the degree‑8 result. **No `sorry` on
  `main`.**
- Record the nonreal‑root octic as future work in PLAN §5, citing the missing statement that is
  currently in the comment at the `sorry`.

### 2.6 Cleanup

Once §2.1–2.4 land, delete the stale warnings and the refutation lemmas that only document dead
ends: `centre*_hpole2_false`, `centre*_step3_pole`, `no_open_s1`, `not_exists_open_s1`,
`centre*_not_open_s1`, and `s1_closed` unless it is reused. Also remove the WARNING paragraphs
on `exists_open_good7/8`.

---

## 3. Work split (one deliverable per `@lean-prover` call)

| # | Deliverable | File | Depends on |
|---|---|---|---|
| A | `signChange_of_simpleRoot` (or the factorization variant) | `Certificate.lean` | — |
| B | Centre simple‑root data for n = 7 and n = 8 (`norm_num`/`ring_nf`) | `Certificate.lean` | A (statement shape only) |
| C | `exists_chain_roots_local` | `Certificate.lean` | A |
| D | Restated `exists_open_good7/8` (`Injective` + `hne` data) | `Certificate.lean` | B, C |
| E | S₁‑preserving lift (§2.3) | `Certificate.lean` or new `Lift.lean` | — |
| F | `exists_oddTschirnhaus` assembly | `Certificate.lean` | D, E |
| G | `Main.lean` restatement (§2.5) | `Main.lean` | — |

- A, E and G are independent and can run in parallel.
- Consider moving C (and A) into a separate `Pptc/TotallyReal/LemmaC.lean`, so that workers
  are not all elaborating the 3,900‑line `Certificate.lean`.
- Each worker keeps its log in `HANDOFF-totallyreal-<topic>.md` and iterates with
  `lean_diagnostic_messages`. `lake_check` is for final confirmation only.
