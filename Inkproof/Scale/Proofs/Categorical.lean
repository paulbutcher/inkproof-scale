/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scale.Categorical
import Inkproof.Scale.Proofs.Affine

universe u v

namespace Inkproof.Scale.Categorical

open Lean.Grind

variable {κ : Type u} {α : Type v}

attribute [local instance] Semiring.natCast

/-- Each band is the range's length over the number of categories. -/
theorem bandwidth_eq [NatCast α] [Sub α] [Div α] (s : Categorical κ α) :
    s.bandwidth = (s.rangeEnd - s.rangeStart) / (s.categories.size : α) :=
  rfl

/-- The `i`th band starts `i` bands after the start of the range. -/
theorem bandStart_eq [NatCast α] [Add α] [Sub α] [Mul α] [Div α] (s : Categorical κ α) (i : Nat) :
    s.bandStart i = s.rangeStart + (i : α) * s.bandwidth :=
  rfl

/-- The index of a category is the position of the first element equal to it. -/
theorem index?_eq [BEq κ] (s : Categorical κ α) (k : κ) :
    s.index? k = s.categories.findIdx? (· == k) :=
  rfl

/-- A category's band starts where the first band with its value does, if there is one. -/
theorem map?_eq [BEq κ] [NatCast α] [Add α] [Sub α] [Mul α] [Div α] (s : Categorical κ α)
    (k : κ) : s.map? k = (s.index? k).map s.bandStart :=
  rfl

/-- The category at the band starting at `y` is the one at the first index whose band does. -/
theorem unmap?_eq [BEq α] [NatCast α] [Add α] [Sub α] [Mul α] [Div α] (s : Categorical κ α)
    (y : α) : s.unmap? y =
      ((List.range s.categories.size).find? (fun i => s.bandStart i == y)).bind (s.categories[·]?) :=
  rfl

section Field

variable [Field α] (s : Categorical κ α)

/-- The affine map of the band's index takes it to where the band starts. -/
theorem toAffine_apply (i : Nat) : s.toAffine.apply (i : α) = s.bandStart i := by
  simp only [Affine.apply, toAffine, bandStart]; grind

/-- An affine map after the scale is the transform of the band's index that combines them. -/
theorem toAffine_comp_apply (t : Affine α) (i : Nat) :
    t.apply (s.bandStart i) = (t.comp s.toAffine).apply (i : α) := by
  rw [Affine.comp_apply, toAffine_apply]

/-- The first band starts at the start of the range. -/
theorem bandStart_zero : s.bandStart 0 = s.rangeStart := by
  simp only [bandStart]; grind

end Field

section OrderedField

variable [Field α] [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α]
  (s : Categorical κ α)

theorem natCast_lt_natCast_of_lt {i j : Nat} (h : i < j) : (i : α) < (j : α) := by
  have h1 := OrderedRing.zero_lt_one (R := α)
  induction j with
  | zero => omega
  | succ j ih =>
    rw [Semiring.natCast_succ j]
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | h'
    · have := ih h'; grind
    · subst h'; grind

/-- Natural numbers are ordered as their images in the field are. -/
theorem natCast_lt_natCast_iff {i j : Nat} : (i : α) < (j : α) ↔ i < j := by
  refine ⟨fun h => ?_, natCast_lt_natCast_of_lt⟩
  rcases Nat.lt_or_ge i j with h' | h'
  · exact h'
  · rcases Nat.eq_or_lt_of_le h' with h'' | h''
    · subst h''; grind
    · have := natCast_lt_natCast_of_lt (α := α) h''; grind

/-- Natural numbers are ordered as their images in the field are. -/
theorem natCast_le_natCast_iff {i j : Nat} : (i : α) ≤ (j : α) ↔ i ≤ j := by
  have := @natCast_lt_natCast_iff α _ _ _ _ _ _ j i
  grind

theorem natCast_inj {i j : Nat} : (i : α) = (j : α) ↔ i = j := by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  have h1 := natCast_le_natCast_iff (α := α) (i := i) (j := j)
  have h2 := natCast_le_natCast_iff (α := α) (i := j) (j := i)
  have := h1.mp (by grind)
  have := h2.mp (by grind)
  omega

/-- Where there are categories, the band after the last starts at the end of the range. -/
theorem bandStart_size (h : s.categories.size ≠ 0) : s.bandStart s.categories.size = s.rangeEnd := by
  have : (s.categories.size : α) ≠ 0 := fun h' => h ((natCast_inj (α := α) (j := 0)).mp (by rw [Semiring.natCast_zero (α := α)]; exact h'))
  simp only [bandStart, bandwidth]
  rw [Field.div_eq_mul_inv]
  have := Field.mul_inv_cancel this
  grind

theorem inv_pos_of_pos {a : α} (h : 0 < a) : 0 < a⁻¹ := by
  have h1 : a ≠ 0 := by grind
  have h2 := Field.mul_inv_cancel h1
  have h3 := OrderedRing.zero_lt_one (R := α)
  by_cases h4 : 0 < a⁻¹
  · exact h4
  · have h5 : a⁻¹ ≤ 0 := by grind
    rcases Std.le_iff_lt_or_eq.mp h5 with h6 | h6
    · have := OrderedRing.mul_pos h (show 0 < -a⁻¹ by grind)
      grind
    · grind

theorem bandwidth_pos (h : s.categories.size ≠ 0) (hr : s.rangeStart < s.rangeEnd) :
    0 < s.bandwidth := by
  have hn : (0 : α) < (s.categories.size : α) := by
    have := natCast_lt_natCast_iff (α := α) (i := 0) (j := s.categories.size)
    grind
  simp only [bandwidth, Field.div_eq_mul_inv]
  exact OrderedRing.mul_pos (by grind) (inv_pos_of_pos hn)

theorem bandwidth_neg (h : s.categories.size ≠ 0) (hr : s.rangeEnd < s.rangeStart) :
    s.bandwidth < 0 := by
  have hn : (0 : α) < (s.categories.size : α) := by
    have := natCast_lt_natCast_iff (α := α) (i := 0) (j := s.categories.size)
    grind
  simp only [bandwidth, Field.div_eq_mul_inv]
  have := OrderedRing.mul_pos (show 0 < s.rangeStart - s.rangeEnd by grind) (inv_pos_of_pos hn)
  grind

/-- PROOF-5: where the range runs upwards, a later category starts later. -/
theorem bandStart_lt_bandStart_iff_of_increasing (h : s.categories.size ≠ 0)
    (hr : s.rangeStart < s.rangeEnd) {i j : Nat} : s.bandStart i < s.bandStart j ↔ i < j := by
  rw [← toAffine_apply, ← toAffine_apply,
    Affine.apply_lt_apply_iff_of_pos _ (bandwidth_pos s h hr), natCast_lt_natCast_iff]

/-- PROOF-5: where the range runs downwards, a later category starts earlier. -/
theorem bandStart_lt_bandStart_iff_of_decreasing (h : s.categories.size ≠ 0)
    (hr : s.rangeEnd < s.rangeStart) {i j : Nat} : s.bandStart i < s.bandStart j ↔ j < i := by
  rw [← toAffine_apply, ← toAffine_apply,
    Affine.apply_lt_apply_iff_of_neg _ (bandwidth_neg s h hr), natCast_lt_natCast_iff]

/-- PROOF-5: where the range runs upwards, a later category starts no earlier. -/
theorem bandStart_le_bandStart_iff_of_increasing (h : s.categories.size ≠ 0)
    (hr : s.rangeStart < s.rangeEnd) {i j : Nat} : s.bandStart i ≤ s.bandStart j ↔ i ≤ j := by
  rw [← toAffine_apply, ← toAffine_apply,
    Affine.apply_le_apply_iff_of_pos _ (bandwidth_pos s h hr), natCast_le_natCast_iff]

/-- PROOF-5: where the range runs downwards, a later category starts no later. -/
theorem bandStart_le_bandStart_iff_of_decreasing (h : s.categories.size ≠ 0)
    (hr : s.rangeEnd < s.rangeStart) {i j : Nat} : s.bandStart i ≤ s.bandStart j ↔ j ≤ i := by
  rw [← toAffine_apply, ← toAffine_apply,
    Affine.apply_le_apply_iff_of_neg _ (bandwidth_neg s h hr), natCast_le_natCast_iff]

/-- PROOF-5: where the range is nondegenerate, bands start at distinct places. -/
theorem bandStart_inj (h : s.categories.size ≠ 0) (hr : s.rangeStart ≠ s.rangeEnd) {i j : Nat} :
    s.bandStart i = s.bandStart j ↔ i = j := by
  refine ⟨fun e => ?_, fun e => by rw [e]⟩
  rcases Std.lt_trichotomy s.rangeStart s.rangeEnd with hr' | hr' | hr'
  · have := (bandStart_le_bandStart_iff_of_increasing s h hr' (i := i) (j := j)).mp (by grind)
    have := (bandStart_le_bandStart_iff_of_increasing s h hr' (i := j) (j := i)).mp (by grind)
    omega
  · exact absurd hr' hr
  · have := (bandStart_le_bandStart_iff_of_decreasing s h hr' (i := i) (j := j)).mp (by grind)
    have := (bandStart_le_bandStart_iff_of_decreasing s h hr' (i := j) (j := i)).mp (by grind)
    omega

/-- PROOF-5: where the range is nondegenerate, the category found at the start of a category's band
is that category. -/
theorem unmap?_map? [BEq κ] [LawfulBEq κ] [BEq α] [LawfulBEq α] (hr : s.rangeStart ≠ s.rangeEnd)
    {k : κ} {y : α} (hy : s.map? k = some y) : s.unmap? y = some k := by
  simp only [map?, index?, Option.map_eq_some_iff] at hy
  obtain ⟨i, hi, rfl⟩ := hy
  obtain ⟨hlt, hk, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp hi
  have hne : s.categories.size ≠ 0 := by omega
  have : (List.range s.categories.size).find? (fun j => s.bandStart j == s.bandStart i) = some i := by
    rw [List.find?_range_eq_some]
    refine ⟨by simp, by simpa using hlt, fun j hj => ?_⟩
    have := (bandStart_inj s hne hr (i := j) (j := i)).mp
    grind
  simp only [unmap?, this, Option.bind_some, Array.getElem?_eq_getElem hlt]
  simpa using hk

end OrderedField

end Inkproof.Scale.Categorical
