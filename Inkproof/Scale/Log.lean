/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scale.Linear

universe u

namespace Inkproof.Scale

/-- A logarithmic scale, taking the domain interval from `domainStart` to `domainEnd` onto the range
interval from `rangeStart` to `rangeEnd`, linearly in the logarithm. The logarithm is a parameter of
the operations, so the same scale runs on `Rat`-like fields and `Float`; the theorems in
`Inkproof.Scale.Proofs.Log` say what is needed of it, which a real logarithm meets on positive
values. -/
structure Log (α : Type u) where
  domainStart : α
  domainEnd : α
  rangeStart : α
  rangeEnd : α
  deriving Repr

namespace Log

variable {α : Type u}

/-- The linear scale over logarithms that `map` applies after taking the logarithm; see
`toLinear_eq`. -/
def toLinear (log : α → α) (s : Log α) : Linear α :=
  ⟨log s.domainStart, log s.domainEnd, s.rangeStart, s.rangeEnd⟩

/-- The point of the range at the same fraction along it as the logarithm of `x` is along the
logarithm of the domain; see `map_eq`, `map_domainStart`, `map_domainEnd`. Order-preserving where
the intervals run the same way and the logarithm is monotone (`map_le_map_iff_of_increasing`,
PROOF-5). -/
def map [Add α] [Sub α] [Mul α] [Div α] (log : α → α) (s : Log α) (x : α) : α :=
  (s.toLinear log).map (log x)

/-- The data value that `map` takes to `y`, given the exponential that undoes the logarithm; see
`unmap_map` and `map_unmap` (PROOF-5). -/
def unmap [Add α] [Sub α] [Mul α] [Div α] (log exp : α → α) (s : Log α) (y : α) : α :=
  exp ((s.toLinear log).inv.map y)

end Log

end Inkproof.Scale
