/- Copyright (c) 2024 Lean Community. All rights reserved.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

This file is part of the Pptc (PowerPoint Constructibility) project.
-/

-- Targeted imports rather than `import Mathlib`; see the note in `Pptc.Defs`.
import Pptc.Defs
import Pptc.Tactic.Init
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Pptc.Tactic

The `pconstructible` tactic, which proves goals of the form `PConstructible e` by
recursive descent on the arithmetic structure of `e`.

## Why a tactic

`PConstructible` is closed under `+ - * /` unconditionally — `div` needs no `y ≠ 0`,
since `x / 0 = 0` and `0` is constructible — so a goal like

    PConstructible (-34 + 24 * √2 + 20 * √3 - 14 * (√2 * √3))

is settled by reading the expression tree and applying one constructor per node. Written
out as a term that is a dozen lines of `PConstructible.add (PConstructible.mul …)` whose
shape is just the parse tree of the expression restated, carrying no mathematics of its
own. The tactic writes those trees so the source can spend its lines on the parts that
are actually about constructibility.

## How it works

Implemented as an Aesop rule set rather than a bespoke elaborator. The arithmetic
constructors are `safe` rules: each one matches a distinct head symbol (`+`, `-`, `*`,
`/`), so the discrimination tree fires at most one per node and there is no branching to
back out of. That is what keeps the search linear in the size of the expression, and it
is why a failing goal fails promptly instead of thrashing.

Leaves come from two places. Values that are P-constructible outright — `Real.pi`,
`Real.cos x` for constructible `x`, each `Real.Gamma (p / q)` that `Pptc.Gamma`
reaches — are registered with the `@[pconstructible]` attribute at the point where they
are proved, so the tactic grows as the project does. Numeric literals are handled by
`Pconstructible.numTac` in `Pptc.Basic`, which reads the literal off the goal and
discharges it through `rat_Pconstructible`; that rule cannot live here because it needs
a lemma this module is imported by.

Aesop's `simp` normalisation phase is turned off (`enableSimp := false`). It has nothing
to contribute — the goals here are structural, not equational — and on a goal mentioning
a heavy definition such as `Pconstructible.lvPar` it will burn the entire heartbeat
budget before the search starts.

## Conditional leaves

Some closure results carry a side hypothesis (`Real.log x` needs `0 < x`,
`arccos_Pconstructible_of_mem_Icc` needs `x ∈ [-1, 1]`). Those are tagged
`@[pconstructible_cond]`, which registers them as *unsafe* rules so that Aesop can back
out when the side condition turns out to be unreachable, and their side goals are
discharged by `Pconstructible.sideTac`.

`sideTac` refuses to run on a `PConstructible` goal. That guard is essential: a
discharger registered without it fires on the main goals too, hands each one to
`norm_num`/`positivity`, and exhausts Aesop's rule-application budget before the search
has gone anywhere.

## Layout

The rule set itself is declared in `Pptc.Tactic.Init`, because Aesop does not make a
rule set visible in the file that declares it. That module also carries the
`@[pconstructible]` and `@[pconstructible_cond]` attributes.

## Scope

The tactic proves that an expression is constructible *because of how it is built*. It
will not notice that a whole expression is constructible for some other reason — that
`(x + y) ^ 2` is reachable when `x + y` is not, say. Where the term structure is itself
the content, write the term.
-/

namespace Pconstructible

attribute [pconstructible]
  PConstructible.base_one
  PConstructible.add
  PConstructible.sub
  PConstructible.mul
  PConstructible.div

open Lean Elab Tactic Meta in
/-- Discharge the side goal of a `@[pconstructible_cond]` rule.

Refuses `PConstructible` goals outright, so the main search is never handed to
`norm_num` or `positivity`; see the module docstring. -/
def sideTac : TacticM Unit := do
  let tgt ← whnfR (← (← getMainGoal).getType)
  if (tgt.app1? ``PConstructible).isSome then
    throwError "pconstructible: sideTac does not apply to PConstructible goals"
  evalTactic (← `(tactic| first | assumption | norm_num | positivity | linarith))

attribute [aesop safe tactic (rule_sets := [Pconstructible])] sideTac

/-- Prove `PConstructible e` by recursive descent on the arithmetic structure of `e`.

Hypotheses in context are used as leaves, as are all lemmas tagged
`@[pconstructible]` / `@[pconstructible_cond]`. To use a closure result that is not
tagged (because its side conditions are not mechanical), introduce it with `have` first
and the tactic will pick it up by assumption.

There is deliberately no `pconstructible?`: `numTac` is a plain tactic rule, which
Aesop cannot turn into a script, so the tracing variant fails on any goal containing a
numeral — which is most of them. -/
syntax (name := pconstructibleTac) "pconstructible" : tactic

macro_rules
  | `(tactic| pconstructible) =>
    `(tactic| aesop
        (config := { terminal := true, enableSimp := false,
                     maxRuleApplicationDepth := 100, maxRuleApplications := 400 })
        (rule_sets := [Pconstructible, -default]))

end Pconstructible
