/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scale.Affine

universe u

namespace Inkproof.Scale.Affine

open Lean.Grind

variable {α : Type u}

/-- An affine map takes `x` to `slope * x + offset`. -/
theorem apply_eq [Add α] [Mul α] (t : Affine α) (x : α) : t.apply x = t.slope * x + t.offset :=
  rfl

/-- Rebasing keeps the slope and moves the offset by the slope times the origin. -/
theorem rebase_eq [Add α] [Mul α] (t : Affine α) (origin : α) :
    t.rebase origin = ⟨t.slope, t.slope * origin + t.offset⟩ :=
  rfl

section Field

variable [Field α]

/-- PROOF-5: the rebased map at a point measured from the origin gives what the original gives at
the point itself. -/
theorem rebase_apply (t : Affine α) (origin x : α) :
    (t.rebase origin).apply (x - origin) = t.apply x := by
  simp only [apply, rebase]; grind

/-- The identity map takes every point to itself. -/
theorem id_apply (x : α) : (Affine.id : Affine α).apply x = x := by
  simp only [apply, Affine.id]; grind

/-- PROOF-5: the composed transform takes every point where applying the two transforms in turn
takes it. -/
theorem comp_apply (g f : Affine α) (x : α) : (g.comp f).apply x = g.apply (f.apply x) := by
  simp only [apply, comp]; grind

/-- Composition is associative, so a chain of transforms may be combined in any grouping. -/
theorem comp_assoc (h g f : Affine α) : (h.comp g).comp f = h.comp (g.comp f) := by
  simp only [comp, Affine.mk.injEq]; constructor <;> grind

/-- Composing with the identity on the left changes nothing. -/
theorem id_comp (t : Affine α) : Affine.id.comp t = t := by
  cases t; simp only [comp, Affine.id, Affine.mk.injEq]; constructor <;> grind

/-- Composing with the identity on the right changes nothing. -/
theorem comp_id (t : Affine α) : t.comp Affine.id = t := by
  cases t; simp only [comp, Affine.id, Affine.mk.injEq]; constructor <;> grind

/-- The inverse has the reciprocal slope, and offset `-(offset / slope)`. -/
theorem inv_eq (t : Affine α) : t.inv = ⟨t.slope⁻¹, -(t.offset * t.slope⁻¹)⟩ := by
  simp only [inv, Affine.mk.injEq, Field.div_eq_mul_inv]; constructor <;> grind

/-- PROOF-5: where the slope is nonzero, the inverse takes every image back to the point it came
from. -/
theorem inv_apply_apply (t : Affine α) (h : t.slope ≠ 0) (x : α) : t.inv.apply (t.apply x) = x := by
  have := Field.mul_inv_cancel h
  simp only [apply, inv_eq]; grind

/-- PROOF-5: where the slope is nonzero, every point is the image of its inverse image. -/
theorem apply_inv_apply (t : Affine α) (h : t.slope ≠ 0) (y : α) : t.apply (t.inv.apply y) = y := by
  have := Field.mul_inv_cancel h
  simp only [apply, inv_eq]; grind

/-- Where the slope is nonzero, the inverse composed after the map is the identity. -/
theorem inv_comp (t : Affine α) (h : t.slope ≠ 0) : t.inv.comp t = Affine.id := by
  have := Field.mul_inv_cancel h
  simp only [comp, inv_eq, Affine.id, Affine.mk.injEq]; constructor <;> grind

/-- Where the slope is nonzero, the map composed after its inverse is the identity. -/
theorem comp_inv (t : Affine α) (h : t.slope ≠ 0) : t.comp t.inv = Affine.id := by
  have := Field.mul_inv_cancel h
  simp only [comp, inv_eq, Affine.id, Affine.mk.injEq]; constructor <;> grind

/-- Where the slope is nonzero, inverting twice gives back the original map. -/
theorem inv_inv (t : Affine α) (h : t.slope ≠ 0) : t.inv.inv = t := by
  have h' : t.slope⁻¹ ≠ 0 := fun h0 => by
    have := Field.mul_inv_cancel h; rw [h0] at this; grind
  have := Field.mul_inv_cancel h
  have := Field.mul_inv_cancel h'
  cases t
  simp only [inv_eq, Affine.mk.injEq] at *
  constructor <;> grind

/-- Where the slope is nonzero, distinct points have distinct images. -/
theorem apply_inj (t : Affine α) (h : t.slope ≠ 0) {x y : α} : t.apply x = t.apply y ↔ x = y := by
  constructor
  · intro hxy
    rw [← t.inv_apply_apply h x, ← t.inv_apply_apply h y, hxy]
  · intro hxy; rw [hxy]

end Field

section Ordered

variable [Field α] [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α]

/-- PROOF-5: a map with positive slope preserves order. -/
theorem apply_le_apply_iff_of_pos (t : Affine α) (h : 0 < t.slope) {x y : α} :
    t.apply x ≤ t.apply y ↔ x ≤ y := by
  simp only [apply]
  rw [← OrderedAdd.add_le_left_iff, Field.IsOrdered.mul_le_mul_iff_of_pos_left h]

/-- PROOF-5: a map with positive slope preserves strict order. -/
theorem apply_lt_apply_iff_of_pos (t : Affine α) (h : 0 < t.slope) {x y : α} :
    t.apply x < t.apply y ↔ x < y := by
  simp only [apply]
  rw [← OrderedAdd.add_lt_left_iff, Field.IsOrdered.mul_lt_mul_iff_of_pos_left h]

/-- PROOF-5: a map with negative slope reverses order. -/
theorem apply_le_apply_iff_of_neg (t : Affine α) (h : t.slope < 0) {x y : α} :
    t.apply x ≤ t.apply y ↔ y ≤ x := by
  simp only [apply]
  rw [← OrderedAdd.add_le_left_iff, Field.IsOrdered.mul_le_mul_iff_of_neg_left h]

/-- PROOF-5: a map with negative slope reverses strict order. -/
theorem apply_lt_apply_iff_of_neg (t : Affine α) (h : t.slope < 0) {x y : α} :
    t.apply x < t.apply y ↔ y < x := by
  simp only [apply]
  rw [← OrderedAdd.add_lt_left_iff, Field.IsOrdered.mul_lt_mul_iff_of_neg_left h]

end Ordered

end Inkproof.Scale.Affine
