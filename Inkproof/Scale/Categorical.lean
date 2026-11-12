/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scale.Affine

universe u v

namespace Inkproof.Scale

/-- A categorical scale, dividing the range interval from `rangeStart` to `rangeEnd` into one band
per category, in the order of `categories`. -/
structure Categorical (κ : Type u) (α : Type v) where
  categories : Array κ
  rangeStart : α
  rangeEnd : α
  deriving Repr

namespace Categorical

variable {κ : Type u} {α : Type v}

/-- The length of each band, signed: negative where the range runs downwards. See `bandwidth_eq`. -/
def bandwidth [NatCast α] [Sub α] [Div α] (s : Categorical κ α) : α :=
  (s.rangeEnd - s.rangeStart) / (s.categories.size : α)

/-- Where the `i`th band starts; see `bandStart_eq`, `bandStart_zero`, `bandStart_size`. -/
def bandStart [NatCast α] [Add α] [Sub α] [Mul α] [Div α] (s : Categorical κ α) (i : Nat) : α :=
  s.rangeStart + (i : α) * s.bandwidth

/-- The band starts as an affine map of the band's index, for composing with a transform; see
`toAffine_apply`. -/
def toAffine [NatCast α] [Sub α] [Div α] (s : Categorical κ α) : Affine α :=
  ⟨s.bandwidth, s.rangeStart⟩

/-- The position of the first occurrence of `k` among the categories; see `index?_eq`. -/
def index? [BEq κ] (s : Categorical κ α) (k : κ) : Option Nat :=
  s.categories.findIdx? (· == k)

/-- Where the band of `k` starts, or `none` for a value that is not a category; see `map?_eq`. -/
def map? [BEq κ] [NatCast α] [Add α] [Sub α] [Mul α] [Div α] (s : Categorical κ α) (k : κ) :
    Option α :=
  (s.index? k).map s.bandStart

/-- The category whose band starts at `y`, or `none` where none does; see `unmap?_map?`. -/
def unmap? [BEq α] [NatCast α] [Add α] [Sub α] [Mul α] [Div α] (s : Categorical κ α) (y : α) :
    Option κ :=
  ((List.range s.categories.size).find? (fun i => s.bandStart i == y)).bind (s.categories[·]?)

end Categorical

end Inkproof.Scale
