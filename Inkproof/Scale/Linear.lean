/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scale.Affine

universe u

namespace Inkproof.Scale

/-- A linear scale, taking the domain interval from `domainStart` to `domainEnd` onto the range
interval from `rangeStart` to `rangeEnd`. Either interval may run downwards, as screen y usually
does. The theorems in `Inkproof.Scale.Proofs.Linear` need a nondegenerate domain
(`domainStart ≠ domainEnd`), and the range too where they invert; these are hypotheses rather than
fields so that `Float` scales can be built. -/
structure Linear (α : Type u) where
  domainStart : α
  domainEnd : α
  rangeStart : α
  rangeEnd : α
  deriving Repr

namespace Linear

variable {α : Type u}

/-- The point of the range at the same fraction along it as `x` is along the domain; see `map_eq`,
`map_domainStart` and `map_domainEnd`. Order-preserving when the intervals run the same way, and
order-reversing when they run opposite ways (`map_le_map_iff_of_increasing`,
`map_le_map_iff_of_decreasing`, PROOF-5). -/
def map [Add α] [Sub α] [Mul α] [Div α] (s : Linear α) (x : α) : α :=
  s.rangeStart + (x - s.domainStart) * (s.rangeEnd - s.rangeStart) / (s.domainEnd - s.domainStart)

/-- The scale from the range back to the domain; see `inv_map_map` and `map_inv_map`
(PROOF-5). -/
def inv (s : Linear α) : Linear α :=
  ⟨s.rangeStart, s.rangeEnd, s.domainStart, s.domainEnd⟩

/-- The same scale for data measured from `origin`: `map` of the rebased scale at `x - origin` is
`map` of the original at `x`; see `map_rebase` (SCALE-3, PROOF-5). With `origin` near the view,
`x - origin` is small however large `x` is, so little precision is lost. -/
def rebase [Sub α] (s : Linear α) (origin : α) : Linear α :=
  ⟨s.domainStart - origin, s.domainEnd - origin, s.rangeStart, s.rangeEnd⟩

/-- `map` as an affine map, for composing with other transforms; see `toAffine_apply` and
`toAffine_inv`. -/
def toAffine [Sub α] [Mul α] [Div α] (s : Linear α) : Affine α :=
  let slope := (s.rangeEnd - s.rangeStart) / (s.domainEnd - s.domainStart)
  ⟨slope, s.rangeStart - slope * s.domainStart⟩

end Linear

end Inkproof.Scale
