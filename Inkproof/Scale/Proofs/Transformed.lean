/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scale.Transformed
import Inkproof.Scale.Proofs.Linear

universe u

namespace Inkproof.Scale.Transformed

open Lean.Grind

variable {α : Type u}

/-- The scale over transformed values has the transformed ends of the domain as its domain. -/
theorem toLinear_eq (f : α → α) (s : Transformed α) :
    s.toLinear f = ⟨f s.domainStart, f s.domainEnd, s.rangeStart, s.rangeEnd⟩ :=
  rfl

/-- A transformed scale maps `x` as the linear scale over transformed values maps `f x`. -/
theorem map_eq [Add α] [Sub α] [Mul α] [Div α] (f : α → α) (s : Transformed α) (x : α) :
    s.map f x = (s.toLinear f).map (f x) :=
  rfl

/-- The inverse image of `y` is `g` of its image under the inverse scale over transformed values. -/
theorem unmap_eq [Add α] [Sub α] [Mul α] [Div α] (f g : α → α) (s : Transformed α) (y : α) :
    s.unmap f g y = g ((s.toLinear f).inv.map y) :=
  rfl

section Field

variable [Field α]

/-- The start of the domain maps to the start of the range. -/
theorem map_domainStart (f : α → α) (s : Transformed α) : s.map f s.domainStart = s.rangeStart :=
  (s.toLinear f).map_domainStart

/-- Where the transformed ends of the domain differ, the end of the domain maps to the end of the
range. -/
theorem map_domainEnd (f : α → α) (s : Transformed α) (hd : f s.domainStart ≠ f s.domainEnd) :
    s.map f s.domainEnd = s.rangeEnd :=
  (s.toLinear f).map_domainEnd hd

/-- Where the transformed ends of the domain differ, the range is nondegenerate and `g` undoes `f`
at `x`, the inverse takes the image of `x` back to `x`. -/
theorem unmap_map (f g : α → α) (s : Transformed α) (hd : f s.domainStart ≠ f s.domainEnd)
    (hr : s.rangeStart ≠ s.rangeEnd) {x : α} (hx : g (f x) = x) :
    s.unmap f g (s.map f x) = x := by
  simp only [unmap, map]
  rw [(s.toLinear f).inv_map_map hd hr, hx]

/-- Where the transformed ends of the domain differ, the range is nondegenerate and `f` undoes `g`
at the inverse scale's image of `y`, the image of the inverse image of `y` is `y`. -/
theorem map_unmap (f g : α → α) (s : Transformed α) (hd : f s.domainStart ≠ f s.domainEnd)
    (hr : s.rangeStart ≠ s.rangeEnd) {y : α} (hy : f (g ((s.toLinear f).inv.map y)) =
      (s.toLinear f).inv.map y) :
    s.map f (s.unmap f g y) = y := by
  simp only [unmap, map]
  rw [hy]
  exact (s.toLinear f).map_inv_map hd hr y

/-- An affine map applied after a transformed scale is the combined transform applied to `f x`. -/
theorem toAffine_comp_apply (f : α → α) (s : Transformed α) (a : Affine α) (x : α) :
    a.apply (s.map f x) = (a.comp (s.toLinear f).toAffine).apply (f x) := by
  rw [Affine.comp_apply, Linear.toAffine_apply]; rfl

end Field

section Ordered

variable [Field α] [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α]

/-- Where `f` is monotone on the points satisfying `D` and the intervals run the same way, the
scale preserves order on them. -/
theorem map_le_map_iff_of_increasing (f : α → α) (D : α → Prop) (s : Transformed α)
    (hf : ∀ x y : α, D x → D y → (f x ≤ f y ↔ x ≤ y))
    (h : f s.domainStart < f s.domainEnd ∧ s.rangeStart < s.rangeEnd ∨
      f s.domainEnd < f s.domainStart ∧ s.rangeEnd < s.rangeStart)
    {x y : α} (hx : D x) (hy : D y) : s.map f x ≤ s.map f y ↔ x ≤ y := by
  rw [map_eq, map_eq, (s.toLinear f).map_le_map_iff_of_increasing h]
  exact hf x y hx hy

/-- The same for strict order. -/
theorem map_lt_map_iff_of_increasing (f : α → α) (D : α → Prop) (s : Transformed α)
    (hf : ∀ x y : α, D x → D y → (f x ≤ f y ↔ x ≤ y))
    (h : f s.domainStart < f s.domainEnd ∧ s.rangeStart < s.rangeEnd ∨
      f s.domainEnd < f s.domainStart ∧ s.rangeEnd < s.rangeStart)
    {x y : α} (hx : D x) (hy : D y) : s.map f x < s.map f y ↔ x < y := by
  rw [map_eq, map_eq, (s.toLinear f).map_lt_map_iff_of_increasing h]
  have := hf x y hx hy
  have := hf y x hy hx
  grind

/-- Where `f` is monotone on the points satisfying `D` and the intervals run opposite ways, as with
screen y, the scale reverses order on them. -/
theorem map_le_map_iff_of_decreasing (f : α → α) (D : α → Prop) (s : Transformed α)
    (hf : ∀ x y : α, D x → D y → (f x ≤ f y ↔ x ≤ y))
    (h : f s.domainStart < f s.domainEnd ∧ s.rangeEnd < s.rangeStart ∨
      f s.domainEnd < f s.domainStart ∧ s.rangeStart < s.rangeEnd)
    {x y : α} (hx : D x) (hy : D y) : s.map f x ≤ s.map f y ↔ y ≤ x := by
  rw [map_eq, map_eq, (s.toLinear f).map_le_map_iff_of_decreasing h]
  exact hf y x hy hx

/-- The same for strict order. -/
theorem map_lt_map_iff_of_decreasing (f : α → α) (D : α → Prop) (s : Transformed α)
    (hf : ∀ x y : α, D x → D y → (f x ≤ f y ↔ x ≤ y))
    (h : f s.domainStart < f s.domainEnd ∧ s.rangeEnd < s.rangeStart ∨
      f s.domainEnd < f s.domainStart ∧ s.rangeStart < s.rangeEnd)
    {x y : α} (hx : D x) (hy : D y) : s.map f x < s.map f y ↔ y < x := by
  rw [map_eq, map_eq, (s.toLinear f).map_lt_map_iff_of_decreasing h]
  have := hf x y hx hy
  have := hf y x hy hx
  grind

end Ordered

end Inkproof.Scale.Transformed

namespace Inkproof.Scale.Asinh

open Lean.Grind

variable {α : Type u}

/-- The forward function takes `x` to `asinh` of `x` over the threshold. -/
theorem forward_eq [Div α] (asinh : α → α) (threshold x : α) :
    forward asinh threshold x = asinh (x / threshold) :=
  rfl

/-- The backward function takes `u` to the threshold times `sinh u`. -/
theorem backward_eq [Mul α] (sinh : α → α) (threshold u : α) :
    backward sinh threshold u = threshold * sinh u :=
  rfl

/-- The transformed scale has the same domain and range. -/
theorem toTransformed_eq (s : Asinh α) :
    s.toTransformed = ⟨s.domainStart, s.domainEnd, s.rangeStart, s.rangeEnd⟩ :=
  rfl

/-- The linear scale over transformed values has `asinh` of the ends over the threshold as its
domain. -/
theorem toLinear_eq [Div α] (asinh : α → α) (s : Asinh α) :
    s.toLinear asinh = ⟨asinh (s.domainStart / s.threshold), asinh (s.domainEnd / s.threshold),
      s.rangeStart, s.rangeEnd⟩ :=
  rfl

/-- The arcsinh scale maps `x` as the transformed scale for `forward` does. -/
theorem map_eq [Add α] [Sub α] [Mul α] [Div α] (asinh : α → α) (s : Asinh α) (x : α) :
    s.map asinh x = (s.toLinear asinh).map (asinh (x / s.threshold)) :=
  rfl

/-- The inverse image of `y` is the threshold times `sinh` of its image under the inverse scale
over transformed values. -/
theorem unmap_eq [Add α] [Sub α] [Mul α] [Div α] (asinh sinh : α → α) (s : Asinh α) (y : α) :
    s.unmap asinh sinh y = s.threshold * sinh ((s.toLinear asinh).inv.map y) :=
  rfl

section Field

variable [Field α]

/-- The start of the domain maps to the start of the range. -/
theorem map_domainStart (asinh : α → α) (s : Asinh α) : s.map asinh s.domainStart = s.rangeStart :=
  Transformed.map_domainStart _ s.toTransformed

/-- Where the transformed ends of the domain differ, the end of the domain maps to the end of the
range. -/
theorem map_domainEnd (asinh : α → α) (s : Asinh α)
    (hd : asinh (s.domainStart / s.threshold) ≠ asinh (s.domainEnd / s.threshold)) :
    s.map asinh s.domainEnd = s.rangeEnd :=
  Transformed.map_domainEnd _ s.toTransformed hd

/-- Where the threshold is nonzero, the transformed ends of the domain differ, the range is
nondegenerate and `sinh` undoes `asinh` at `x / threshold`, the inverse takes the image of `x` back
to `x`. -/
theorem unmap_map (asinh sinh : α → α) (s : Asinh α) (ht : s.threshold ≠ 0)
    (hd : asinh (s.domainStart / s.threshold) ≠ asinh (s.domainEnd / s.threshold))
    (hr : s.rangeStart ≠ s.rangeEnd) {x : α} (hx : sinh (asinh (x / s.threshold)) = x / s.threshold) :
    s.unmap asinh sinh (s.map asinh x) = x := by
  refine Transformed.unmap_map _ _ s.toTransformed hd hr ?_
  show s.threshold * sinh (asinh (x / s.threshold)) = x
  rw [hx]
  grind

/-- Where the threshold is nonzero, the transformed ends of the domain differ, the range is
nondegenerate and `asinh` undoes `sinh` at the inverse scale's image of `y`, the image of the
inverse image of `y` is `y`. -/
theorem map_unmap (asinh sinh : α → α) (s : Asinh α) (ht : s.threshold ≠ 0)
    (hd : asinh (s.domainStart / s.threshold) ≠ asinh (s.domainEnd / s.threshold))
    (hr : s.rangeStart ≠ s.rangeEnd) {y : α}
    (hy : asinh (sinh ((s.toLinear asinh).inv.map y)) = (s.toLinear asinh).inv.map y) :
    s.map asinh (s.unmap asinh sinh y) = y := by
  refine Transformed.map_unmap _ _ s.toTransformed hd hr ?_
  show asinh (s.threshold * sinh ((s.toLinear asinh).inv.map y) / s.threshold) = _
  have : s.threshold * sinh ((s.toLinear asinh).inv.map y) / s.threshold =
      sinh ((s.toLinear asinh).inv.map y) := by grind
  rw [this]
  exact hy

end Field

section Ordered

variable [Field α] [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α]

private theorem forward_le_iff (asinh : α → α) (t : α) (ht : 0 < t)
    (h : ∀ x y : α, asinh x ≤ asinh y ↔ x ≤ y) (x y : α) :
    Asinh.forward asinh t x ≤ Asinh.forward asinh t y ↔ x ≤ y := by
  simp only [Asinh.forward]
  rw [h]
  have hi : 0 < t⁻¹ := Field.IsOrdered.inv_pos_iff.mpr ht
  constructor
  · intro hxy
    have := OrderedRing.mul_le_mul_of_nonneg_right hxy (Std.le_of_lt ht)
    grind
  · intro hxy
    have := OrderedRing.mul_le_mul_of_nonneg_right hxy (Std.le_of_lt hi)
    grind

/-- Where `asinh` is monotone, the threshold is positive, the transformed ends of the domain are
ordered like the range's and the intervals run the same way, the scale preserves order. -/
theorem map_le_map_iff_of_increasing (asinh : α → α) (s : Asinh α)
    (hasinh : ∀ x y : α, asinh x ≤ asinh y ↔ x ≤ y) (ht : 0 < s.threshold)
    (h : asinh (s.domainStart / s.threshold) < asinh (s.domainEnd / s.threshold) ∧
        s.rangeStart < s.rangeEnd ∨
      asinh (s.domainEnd / s.threshold) < asinh (s.domainStart / s.threshold) ∧
        s.rangeEnd < s.rangeStart)
    (x y : α) : s.map asinh x ≤ s.map asinh y ↔ x ≤ y :=
  Transformed.map_le_map_iff_of_increasing (Asinh.forward asinh s.threshold) (fun _ => True)
    s.toTransformed (fun x y _ _ => forward_le_iff asinh _ ht hasinh x y) h trivial trivial

/-- The same for strict order. -/
theorem map_lt_map_iff_of_increasing (asinh : α → α) (s : Asinh α)
    (hasinh : ∀ x y : α, asinh x ≤ asinh y ↔ x ≤ y) (ht : 0 < s.threshold)
    (h : asinh (s.domainStart / s.threshold) < asinh (s.domainEnd / s.threshold) ∧
        s.rangeStart < s.rangeEnd ∨
      asinh (s.domainEnd / s.threshold) < asinh (s.domainStart / s.threshold) ∧
        s.rangeEnd < s.rangeStart)
    (x y : α) : s.map asinh x < s.map asinh y ↔ x < y := by
  have h1 := map_le_map_iff_of_increasing asinh s hasinh ht h x y
  have h2 := map_le_map_iff_of_increasing asinh s hasinh ht h y x
  have := Std.IsLinearOrder.le_total (a := s.map asinh x) (b := s.map asinh y)
  grind

end Ordered

end Inkproof.Scale.Asinh
