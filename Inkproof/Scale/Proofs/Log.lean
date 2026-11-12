/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scale.Log
import Inkproof.Scale.Proofs.Linear

universe u

namespace Inkproof.Scale.Log

open Lean.Grind

variable {α : Type u}

/-- The scale over logarithms has the logarithms of the domain's ends as its domain. -/
theorem toLinear_eq (log : α → α) (s : Log α) :
    s.toLinear log = ⟨log s.domainStart, log s.domainEnd, s.rangeStart, s.rangeEnd⟩ :=
  rfl

/-- A logarithmic scale maps `x` as the linear scale over logarithms maps the logarithm of `x`. -/
theorem map_eq [Add α] [Sub α] [Mul α] [Div α] (log : α → α) (s : Log α) (x : α) :
    s.map log x = (s.toLinear log).map (log x) :=
  rfl

/-- The inverse image of `y` is the exponential of its image under the inverse scale over
logarithms. -/
theorem unmap_eq [Add α] [Sub α] [Mul α] [Div α] (log exp : α → α) (s : Log α) (y : α) :
    s.unmap log exp y = exp ((s.toLinear log).inv.map y) :=
  rfl

section Field

variable [Field α]

/-- The start of the domain maps to the start of the range. -/
theorem map_domainStart (log : α → α) (s : Log α) : s.map log s.domainStart = s.rangeStart :=
  (s.toLinear log).map_domainStart

/-- Where the logarithms of the domain's ends differ, the end of the domain maps to the end of the
range. -/
theorem map_domainEnd (log : α → α) (s : Log α) (hd : log s.domainStart ≠ log s.domainEnd) :
    s.map log s.domainEnd = s.rangeEnd :=
  (s.toLinear log).map_domainEnd hd

/-- PROOF-5: where the logarithms of the domain's ends differ, the range is nondegenerate and `exp`
undoes `log` at `x`, the inverse takes the image of `x` back to `x`. -/
theorem unmap_map (log exp : α → α) (s : Log α) (hd : log s.domainStart ≠ log s.domainEnd)
    (hr : s.rangeStart ≠ s.rangeEnd) {x : α} (hx : exp (log x) = x) :
    s.unmap log exp (s.map log x) = x := by
  simp only [unmap, map]
  rw [(s.toLinear log).inv_map_map hd hr, hx]

/-- PROOF-5: where the logarithms of the domain's ends differ, the range is nondegenerate and
`log` undoes `exp` at the inverse scale's image of `y`, the image of the inverse image of `y` is
`y`. -/
theorem map_unmap (log exp : α → α) (s : Log α) (hd : log s.domainStart ≠ log s.domainEnd)
    (hr : s.rangeStart ≠ s.rangeEnd) {y : α} (hy : log (exp ((s.toLinear log).inv.map y)) =
      (s.toLinear log).inv.map y) :
    s.map log (s.unmap log exp y) = y := by
  simp only [unmap, map]
  rw [hy]
  exact (s.toLinear log).map_inv_map hd hr y

/-- PROOF-5: an affine map applied after a logarithmic scale is the combined transform applied to
the logarithm. -/
theorem toAffine_comp_apply (log : α → α) (s : Log α) (a : Affine α) (x : α) :
    a.apply (s.map log x) = (a.comp (s.toLinear log).toAffine).apply (log x) := by
  rw [Affine.comp_apply, Linear.toAffine_apply]; rfl

end Field

section Ordered

variable [Field α] [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α]

/-- PROOF-5: where the logarithm is monotone on the positive values, the domain's ends are
positive and the intervals run the same way, the scale preserves order on positive values. -/
theorem map_le_map_iff_of_increasing (log : α → α) (s : Log α)
    (hlog : ∀ x y : α, 0 < x → 0 < y → (log x ≤ log y ↔ x ≤ y))
    (h : log s.domainStart < log s.domainEnd ∧ s.rangeStart < s.rangeEnd ∨
      log s.domainEnd < log s.domainStart ∧ s.rangeEnd < s.rangeStart)
    {x y : α} (hx : 0 < x) (hy : 0 < y) : s.map log x ≤ s.map log y ↔ x ≤ y := by
  rw [map_eq, map_eq, (s.toLinear log).map_le_map_iff_of_increasing h]
  exact hlog x y hx hy

/-- PROOF-5: the same for strict order. -/
theorem map_lt_map_iff_of_increasing (log : α → α) (s : Log α)
    (hlog : ∀ x y : α, 0 < x → 0 < y → (log x ≤ log y ↔ x ≤ y))
    (h : log s.domainStart < log s.domainEnd ∧ s.rangeStart < s.rangeEnd ∨
      log s.domainEnd < log s.domainStart ∧ s.rangeEnd < s.rangeStart)
    {x y : α} (hx : 0 < x) (hy : 0 < y) : s.map log x < s.map log y ↔ x < y := by
  rw [map_eq, map_eq, (s.toLinear log).map_lt_map_iff_of_increasing h]
  have := hlog x y hx hy
  have := hlog y x hy hx
  grind

/-- PROOF-5: where the logarithm is monotone on the positive values and the intervals run opposite
ways, as with screen y, the scale reverses order on positive values. -/
theorem map_le_map_iff_of_decreasing (log : α → α) (s : Log α)
    (hlog : ∀ x y : α, 0 < x → 0 < y → (log x ≤ log y ↔ x ≤ y))
    (h : log s.domainStart < log s.domainEnd ∧ s.rangeEnd < s.rangeStart ∨
      log s.domainEnd < log s.domainStart ∧ s.rangeStart < s.rangeEnd)
    {x y : α} (hx : 0 < x) (hy : 0 < y) : s.map log x ≤ s.map log y ↔ y ≤ x := by
  rw [map_eq, map_eq, (s.toLinear log).map_le_map_iff_of_decreasing h]
  exact hlog y x hy hx

/-- PROOF-5: the same for strict order. -/
theorem map_lt_map_iff_of_decreasing (log : α → α) (s : Log α)
    (hlog : ∀ x y : α, 0 < x → 0 < y → (log x ≤ log y ↔ x ≤ y))
    (h : log s.domainStart < log s.domainEnd ∧ s.rangeEnd < s.rangeStart ∨
      log s.domainEnd < log s.domainStart ∧ s.rangeStart < s.rangeEnd)
    {x y : α} (hx : 0 < x) (hy : 0 < y) : s.map log x < s.map log y ↔ y < x := by
  rw [map_eq, map_eq, (s.toLinear log).map_lt_map_iff_of_decreasing h]
  have := hlog x y hx hy
  have := hlog y x hy hx
  grind

end Ordered

end Inkproof.Scale.Log
