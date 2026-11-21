/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scale.Linear

universe u

namespace Inkproof.Scale

/-- A scale that is linear in a transformed space, taking the domain interval from `domainStart` to
`domainEnd` onto the range interval from `rangeStart` to `rangeEnd` after a caller-supplied forward
function. The forward function and its inverse are parameters of the operations, so the same scale
runs on `Rat`-like fields and `Float`; the theorems in `Inkproof.Scale.Proofs.Transformed` say what
is needed of them. -/
structure Transformed (α : Type u) where
  domainStart : α
  domainEnd : α
  rangeStart : α
  rangeEnd : α
  deriving Repr

namespace Transformed

variable {α : Type u}

/-- The linear scale over transformed values that `map` applies after the forward function. -/
def toLinear (f : α → α) (s : Transformed α) : Linear α :=
  ⟨f s.domainStart, f s.domainEnd, s.rangeStart, s.rangeEnd⟩

/-- The point of the range at the same fraction along it as `f x` is along the transformed domain;
see `map_eq`. -/
def map [Add α] [Sub α] [Mul α] [Div α] (f : α → α) (s : Transformed α) (x : α) : α :=
  (s.toLinear f).map (f x)

/-- The data value that `map` takes to `y`, given the function `g` that undoes `f`. -/
def unmap [Add α] [Sub α] [Mul α] [Div α] (f g : α → α) (s : Transformed α) (y : α) : α :=
  g ((s.toLinear f).inv.map y)

end Transformed

/-- An arcsinh scale, linear within `threshold` of zero and logarithmic far from it, so data of
either sign and any magnitude fits. It is the `Transformed` scale for `x ↦ asinh (x / threshold)`;
`asinh` and its inverse `sinh` are parameters of the operations. -/
structure Asinh (α : Type u) where
  domainStart : α
  domainEnd : α
  rangeStart : α
  rangeEnd : α
  threshold : α
  deriving Repr

namespace Asinh

variable {α : Type u}

/-- The forward function of the scale. -/
def forward [Div α] (asinh : α → α) (threshold : α) (x : α) : α :=
  asinh (x / threshold)

/-- The inverse of `forward`, given the `sinh` that undoes `asinh`. -/
def backward [Mul α] (sinh : α → α) (threshold : α) (u : α) : α :=
  threshold * sinh u

/-- The same scale as a `Transformed` one. -/
def toTransformed (s : Asinh α) : Transformed α :=
  ⟨s.domainStart, s.domainEnd, s.rangeStart, s.rangeEnd⟩

/-- The linear scale over transformed values that `map` applies. -/
def toLinear [Div α] (asinh : α → α) (s : Asinh α) : Linear α :=
  s.toTransformed.toLinear (forward asinh s.threshold)

/-- The point of the range for the data value `x`; see `map_eq`. -/
def map [Add α] [Sub α] [Mul α] [Div α] (asinh : α → α) (s : Asinh α) (x : α) : α :=
  s.toTransformed.map (forward asinh s.threshold) x

/-- The data value that `map` takes to `y`; see `unmap_map`. -/
def unmap [Add α] [Sub α] [Mul α] [Div α] (asinh sinh : α → α) (s : Asinh α) (y : α) : α :=
  s.toTransformed.unmap (forward asinh s.threshold) (backward sinh s.threshold) y

end Asinh

end Inkproof.Scale
