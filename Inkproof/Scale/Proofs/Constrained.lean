/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scale.Constrained

universe u

namespace Inkproof.Scale

variable {α : Type u} {P : α → α → Prop} [∀ a b, Decidable (P a b)]

/-- A scale whose domain meets the constraint is accepted, unchanged. -/
theorem Linear.check?_eq_some {s : Linear α} (h : P s.domainStart s.domainEnd) :
    Linear.check? P s = some ⟨s, h⟩ :=
  by simp [Linear.check?, h]

/-- A scale whose domain breaks the constraint is refused. -/
theorem Linear.check?_eq_none {s : Linear α} (h : ¬P s.domainStart s.domainEnd) :
    Linear.check? P s = none :=
  by simp [Linear.check?, h]

/-- A new domain is accepted exactly when it meets the constraint, and then the scale
differs from the old one only in its domain. -/
theorem Constrained.withDomain?_eq_some {c : Constrained α P} {a b : α} (h : P a b) :
    c.withDomain? a b = some ⟨{ c.scale with domainStart := a, domainEnd := b }, h⟩ :=
  by simp [Constrained.withDomain?, Linear.check?, h]

/-- A new domain that breaks the constraint is refused. -/
theorem Constrained.withDomain?_eq_none {c : Constrained α P} {a b : α} (h : ¬P a b) :
    c.withDomain? a b = none :=
  by simp [Constrained.withDomain?, Linear.check?, h]

section Includes

variable [LE α] [Std.IsLinearOrder α] [DecidableLE α]

/-- Widening a domain makes it contain the value. -/
theorem Includes.widen_includes (v a b : α) :
    Includes v (Includes.widen v a b).1 (Includes.widen v a b).2 := by
  have total : ∀ x y : α, x ≤ y ∨ y ≤ x := fun x y => Std.le_total (a := x) (b := y)
  unfold Includes
  by_cases hab : a ≤ b <;> simp only [Includes.widen, hab, ↓reduceIte]
  · left
    constructor
    · split
      · exact Std.le_refl v
      · rename_i h; exact (total v a).resolve_left h
    · split
      · exact Std.le_refl v
      · rename_i h; exact (total b v).resolve_left h
  · right
    constructor
    · split
      · exact Std.le_refl v
      · rename_i h; exact (total v b).resolve_left h
    · split
      · exact Std.le_refl v
      · rename_i h; exact (total a v).resolve_left h

/-- Widening only moves the end points outward, so the domain keeps its direction. -/
theorem Includes.widen_outward (v a b : α) :
    (a ≤ b → (Includes.widen v a b).1 ≤ a ∧ b ≤ (Includes.widen v a b).2) ∧
    (¬a ≤ b → (Includes.widen v a b).2 ≤ b ∧ a ≤ (Includes.widen v a b).1) := by
  constructor
  · intro hab
    simp only [Includes.widen, hab, ↓reduceIte]
    constructor
    · split
      · rename_i h; exact h
      · exact Std.le_refl a
    · split
      · rename_i h; exact h
      · exact Std.le_refl b
  · intro hab
    simp only [Includes.widen, hab, ↓reduceIte]
    constructor
    · split
      · rename_i h; exact h
      · exact Std.le_refl b
    · split
      · rename_i h; exact h
      · exact Std.le_refl a

/-- A domain that already contains the value is left alone. -/
theorem Includes.widen_of_includes {v a b : α} (h : Includes v a b) :
    Includes.widen v a b = (a, b) := by
  have anti : ∀ {x y : α}, x ≤ y → y ≤ x → x = y := Std.le_antisymm
  have trans : ∀ {x y z : α}, x ≤ y → y ≤ z → x ≤ z := Std.le_trans
  unfold Includes.widen
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hab : a ≤ b := trans h1 h2
    simp only [hab, ite_true]
    congr 1
    · split
      · rename_i h; exact anti h h1
      · rfl
    · split
      · rename_i h; exact anti h2 h
      · rfl
  · split
    · rename_i hab
      have e1 : a = v := anti (trans hab h1) h2
      have e2 : b = v := anti h1 (trans h2 hab)
      subst e1; subst e2
      simp
    · congr 1
      · split
        · rename_i h; exact anti h2 h
        · rfl
      · split
        · rename_i h; exact anti h h1
        · rfl

end Includes

end Inkproof.Scale
