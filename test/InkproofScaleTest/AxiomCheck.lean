/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Inkproof.Scale
import Inkproof.Scale.Proofs
import InkproofTools.AxiomCheck

/-! PROC-1: compiling this module fails if any declaration of the library depends on an axiom other
than Lean's own and those in `Inkproof.Float.Axioms`, or if the library declares
an axiom of its own. -/

open Lean Elab Command

run_cmd liftCoreM (InkproofTools.AxiomCheck.check `Inkproof.Scale none [`Inkproof.Float.Axioms])
