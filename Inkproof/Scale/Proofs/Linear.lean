/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scale.Linear
import Inkproof.Scale.Proofs.Affine

universe u

namespace Inkproof.Scale.Linear

open Lean.Grind

variable {α : Type u}

/-- A linear scale takes `x` to `rangeStart` plus the range's length times `x`'s distance from
`domainStart` as a fraction of the domain's length. -/
theorem map_eq [Add α] [Sub α] [Mul α] [Div α] (s : Linear α) (x : α) :
    s.map x = s.rangeStart +
      (x - s.domainStart) * (s.rangeEnd - s.rangeStart) / (s.domainEnd - s.domainStart) :=
  rfl

/-- The inverse scale runs from the range back to the domain. -/
theorem inv_eq (s : Linear α) :
    s.inv = ⟨s.rangeStart, s.rangeEnd, s.domainStart, s.domainEnd⟩ :=
  rfl

/-- Inverting a scale twice gives back the original scale. -/
theorem inv_inv (s : Linear α) : s.inv.inv = s :=
  rfl

/-- As an affine map, a scale's slope is the range's length over the domain's, and it takes
`domainStart` to `rangeStart`. -/
theorem toAffine_eq [Sub α] [Mul α] [Div α] (s : Linear α) :
    s.toAffine =
      let slope := (s.rangeEnd - s.rangeStart) / (s.domainEnd - s.domainStart)
      ⟨slope, s.rangeStart - slope * s.domainStart⟩ :=
  rfl

section Field

variable [Field α]

/-- A scale's affine map takes every point where the scale does. -/
theorem toAffine_apply (s : Linear α) (x : α) : s.toAffine.apply x = s.map x := by
  simp only [Affine.apply, toAffine, map, Field.div_eq_mul_inv]; grind

/-- The start of the domain maps to the start of the range. -/
theorem map_domainStart (s : Linear α) : s.map s.domainStart = s.rangeStart := by
  simp only [map, Field.div_eq_mul_inv]; grind

/-- Where the domain is nondegenerate, the end of the domain maps to the end of the range. -/
theorem map_domainEnd (s : Linear α) (hd : s.domainStart ≠ s.domainEnd) :
    s.map s.domainEnd = s.rangeEnd := by
  have : (s.domainEnd - s.domainStart) * (s.domainEnd - s.domainStart)⁻¹ = 1 :=
    Field.mul_inv_cancel (by grind)
  simp only [map, Field.div_eq_mul_inv]; grind

/-- PROOF-5: where the domain and range are both nondegenerate, the inverse scale takes every image
back to the point it came from. -/
theorem inv_map_map (s : Linear α) (hd : s.domainStart ≠ s.domainEnd)
    (hr : s.rangeStart ≠ s.rangeEnd) (x : α) : s.inv.map (s.map x) = x := by
  have : (s.domainEnd - s.domainStart) * (s.domainEnd - s.domainStart)⁻¹ = 1 :=
    Field.mul_inv_cancel (by grind)
  have : (s.rangeEnd - s.rangeStart) * (s.rangeEnd - s.rangeStart)⁻¹ = 1 :=
    Field.mul_inv_cancel (by grind)
  simp only [map, inv, Field.div_eq_mul_inv]; grind

/-- PROOF-5: where the domain and range are both nondegenerate, every point of the range space is the
image of its inverse image. -/
theorem map_inv_map (s : Linear α) (hd : s.domainStart ≠ s.domainEnd)
    (hr : s.rangeStart ≠ s.rangeEnd) (y : α) : s.map (s.inv.map y) = y :=
  s.inv.inv_map_map hr hd y

/-- Where the domain and range are both nondegenerate, the inverse scale's affine map is the
inverse of the scale's. -/
theorem toAffine_inv (s : Linear α) (hd : s.domainStart ≠ s.domainEnd)
    (hr : s.rangeStart ≠ s.rangeEnd) : s.inv.toAffine = s.toAffine.inv := by
  have : (s.domainEnd - s.domainStart) * (s.domainEnd - s.domainStart)⁻¹ = 1 :=
    Field.mul_inv_cancel (by grind)
  have : (s.rangeEnd - s.rangeStart) * (s.rangeEnd - s.rangeStart)⁻¹ = 1 :=
    Field.mul_inv_cancel (by grind)
  simp only [toAffine, inv, Affine.inv_eq, Affine.mk.injEq, Field.div_eq_mul_inv,
    Field.inv_mul, Field.inv_inv]
  constructor <;> grind

/-- Where the domain and range are both nondegenerate, the scale's affine map has a nonzero slope,
so `Affine.inv` undoes it. -/
theorem toAffine_slope_ne_zero (s : Linear α) (hd : s.domainStart ≠ s.domainEnd)
    (hr : s.rangeStart ≠ s.rangeEnd) : s.toAffine.slope ≠ 0 := by
  simp only [toAffine, Field.div_eq_mul_inv]
  intro h
  rcases Field.of_mul_eq_zero h with h | h
  · grind
  · exact hd (by have := Field.inv_eq_zero_iff.mp h; grind)

end Field

section Ordered

variable [Field α] [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α]

/-- Where the domain and range run the same way, the scale's affine map has a positive slope. -/
theorem toAffine_slope_pos (s : Linear α)
    (h : s.domainStart < s.domainEnd ∧ s.rangeStart < s.rangeEnd ∨
      s.domainEnd < s.domainStart ∧ s.rangeEnd < s.rangeStart) :
    0 < s.toAffine.slope := by
  simp only [toAffine, Field.div_eq_mul_inv]
  rcases h with ⟨hd, hr⟩ | ⟨hd, hr⟩
  · exact OrderedRing.mul_pos (by grind) (Field.IsOrdered.inv_pos_iff.mpr (by grind))
  · exact OrderedRing.mul_pos_of_neg_of_neg (by grind) (Field.IsOrdered.inv_neg_iff.mpr (by grind))

/-- Where the domain and range run opposite ways, the scale's affine map has a negative slope. -/
theorem toAffine_slope_neg (s : Linear α)
    (h : s.domainStart < s.domainEnd ∧ s.rangeEnd < s.rangeStart ∨
      s.domainEnd < s.domainStart ∧ s.rangeStart < s.rangeEnd) :
    s.toAffine.slope < 0 := by
  simp only [toAffine, Field.div_eq_mul_inv]
  rcases h with ⟨hd, hr⟩ | ⟨hd, hr⟩
  · exact OrderedRing.mul_neg_of_neg_of_pos (by grind) (Field.IsOrdered.inv_pos_iff.mpr (by grind))
  · exact OrderedRing.mul_neg_of_pos_of_neg (by grind) (Field.IsOrdered.inv_neg_iff.mpr (by grind))

/-- PROOF-5: where the domain and range run the same way, the scale preserves order. -/
theorem map_le_map_iff_of_increasing (s : Linear α)
    (h : s.domainStart < s.domainEnd ∧ s.rangeStart < s.rangeEnd ∨
      s.domainEnd < s.domainStart ∧ s.rangeEnd < s.rangeStart) {x y : α} :
    s.map x ≤ s.map y ↔ x ≤ y := by
  rw [← toAffine_apply, ← toAffine_apply]
  exact Affine.apply_le_apply_iff_of_pos _ (s.toAffine_slope_pos h)

/-- PROOF-5: where the domain and range run the same way, the scale preserves strict order. -/
theorem map_lt_map_iff_of_increasing (s : Linear α)
    (h : s.domainStart < s.domainEnd ∧ s.rangeStart < s.rangeEnd ∨
      s.domainEnd < s.domainStart ∧ s.rangeEnd < s.rangeStart) {x y : α} :
    s.map x < s.map y ↔ x < y := by
  rw [← toAffine_apply, ← toAffine_apply]
  exact Affine.apply_lt_apply_iff_of_pos _ (s.toAffine_slope_pos h)

/-- PROOF-5: where the domain and range run opposite ways, as with screen y, the scale reverses
order. -/
theorem map_le_map_iff_of_decreasing (s : Linear α)
    (h : s.domainStart < s.domainEnd ∧ s.rangeEnd < s.rangeStart ∨
      s.domainEnd < s.domainStart ∧ s.rangeStart < s.rangeEnd) {x y : α} :
    s.map x ≤ s.map y ↔ y ≤ x := by
  rw [← toAffine_apply, ← toAffine_apply]
  exact Affine.apply_le_apply_iff_of_neg _ (s.toAffine_slope_neg h)

/-- PROOF-5: where the domain and range run opposite ways, as with screen y, the scale reverses
strict order. -/
theorem map_lt_map_iff_of_decreasing (s : Linear α)
    (h : s.domainStart < s.domainEnd ∧ s.rangeEnd < s.rangeStart ∨
      s.domainEnd < s.domainStart ∧ s.rangeStart < s.rangeEnd) {x y : α} :
    s.map x < s.map y ↔ y < x := by
  rw [← toAffine_apply, ← toAffine_apply]
  exact Affine.apply_lt_apply_iff_of_neg _ (s.toAffine_slope_neg h)

end Ordered

end Inkproof.Scale.Linear
