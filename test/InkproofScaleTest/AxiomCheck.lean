/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Inkproof.Scale
import Inkproof.Scale.Proofs

/-! PROC-1: compiling this module fails if any declaration of the library depends on an axiom other
than Lean's own and those Inkproof.Core lists in `Inkproof.Core.Axioms`, or if the library declares
an axiom of its own. -/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let moduleOf (n : Name) : Option Name :=
    (env.getModuleIdxFor? n).bind (env.allImportedModuleNames[·.toNat]?)
  let coreAxioms := `Inkproof.Core.Axioms
  let mut listed : NameSet := ({} : NameSet).insert `propext |>.insert `Classical.choice
    |>.insert `Quot.sound
  let mut library : Array Name := #[]
  for (n, ci) in env.constants.map₁.toList do
    if ci matches .axiomInfo _ && moduleOf n == some coreAxioms then
      listed := listed.insert n
    unless (moduleOf n).any (`Inkproof.Scale).isPrefixOf do continue
    if ci matches .axiomInfo _ then
      throwError "axiom {n} is declared in Inkproof.Scale; only Inkproof.Core.Axioms may add axioms"
    library := library.push n
  if library.isEmpty then
    throwError "no declarations of Inkproof.Scale found; the check would pass vacuously"
  for n in library do
    for a in ← collectAxioms n do
      unless listed.contains a do
        throwError "{n} depends on axiom {a}, which is not listed in {coreAxioms}"
