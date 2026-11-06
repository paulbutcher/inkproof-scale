/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

universe u

namespace Inkproof.Scale

/-- The affine map `x ↦ slope * x + offset` on one axis, such as data space to screen space.
Definitions ask only for the operations they compute with, so they run on `Float`; the theorems in
`Inkproof.Scale.Proofs.Affine` hold over any ordered field. -/
structure Affine (α : Type u) where
  slope : α
  offset : α
  deriving Repr

namespace Affine

variable {α : Type u}

/-- `slope * x + offset`; see `apply_eq`. Order-preserving for a positive slope and order-reversing
for a negative one (`apply_le_apply_iff_of_pos`, `apply_le_apply_iff_of_neg`). -/
def apply [Add α] [Mul α] (t : Affine α) (x : α) : α := t.slope * x + t.offset

/-- The identity map; see `id_apply`. -/
protected def id [OfNat α 0] [OfNat α 1] : Affine α := ⟨1, 0⟩

/-- `g.comp f` applies `f`, then `g`; see `comp_apply` (PROOF-5). -/
def comp [Add α] [Mul α] (g f : Affine α) : Affine α :=
  ⟨g.slope * f.slope, g.slope * f.offset + g.offset⟩

/-- The inverse map, defined when the slope is nonzero; see `inv_apply_apply` and
`apply_inv_apply` (PROOF-5). -/
def inv [OfNat α 1] [Div α] [Neg α] (t : Affine α) : Affine α :=
  ⟨1 / t.slope, -t.offset / t.slope⟩

end Affine

end Inkproof.Scale
