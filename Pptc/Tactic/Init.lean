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

import Aesop
-- Targeted import: the lakefile sets `linter.style.header`, a non-weak option, so
-- every module in the package must import the Mathlib linter that defines it.
import Mathlib.Tactic.Linter.Header

/-! # Pptc.Tactic.Init

Declares the `Pconstructible` Aesop rule set and the attributes that populate it.

This is split out from `Pptc.Tactic` only because Aesop requires it: a rule set is not
visible in the file that declares it, so nothing can be tagged until an importing module
picks it up. Everything of substance is in `Pptc.Tactic`. -/

namespace Pconstructible

declare_aesop_rule_sets [Pconstructible]

/-- Register an unconditional closure lemma with the `pconstructible` tactic: one whose
hypotheses are all themselves `PConstructible` claims, so that applying it can never
strand the search on a side goal it cannot discharge.

Tag a lemma only when its conclusion has a head symbol no other rule claims. Two `safe`
rules matching the same goal are not an error, but Aesop commits to one of them, so the
overlap is a silent way to lose the other. -/
macro "pconstructible" : attr =>
  `(attr| aesop safe apply (rule_sets := [$(Lean.mkIdent `Pconstructible):ident]))

/-- Register a closure lemma that carries a side hypothesis beyond `PConstructible`
claims, such as a positivity or membership condition. Registered `unsafe` so that Aesop
backtracks if `Pconstructible.sideTac` cannot discharge the condition. -/
macro "pconstructible_cond" : attr =>
  `(attr| aesop unsafe 70% apply (rule_sets := [$(Lean.mkIdent `Pconstructible):ident]))

end Pconstructible
