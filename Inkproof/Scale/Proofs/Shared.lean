/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scale.Shared
import Inkproof.Scale.Linear

universe u v

namespace Inkproof.Scale.Shared

variable {σ : Type u} {β : Type v}

/-- Reading a handle applies the view to the scale it holds. -/
theorem read_eq (h : Shared σ) (f : σ → β) : h.read f = f h.scale :=
  rfl

/-- SCALE-4: any two views reading the same handle, however they are written, get the same result
from it. -/
theorem read_congr {h₁ h₂ : Shared σ} (e : h₁ = h₂) (f : σ → β) : h₁.read f = h₂.read f :=
  e ▸ rfl

/-- SCALE-4: after an update every holder of the new handle reads the updated scale. -/
theorem read_update (h : Shared σ) (f : σ → σ) (g : σ → β) : (h.update f).read g = g (f h.scale) :=
  rfl

/-- SCALE-4: two charts holding the same handle map every datum to the same position. -/
theorem map_eq_of_eq {α : Type u} [Add α] [Sub α] [Mul α] [Div α] {h₁ h₂ : Shared (Linear α)}
    (e : h₁ = h₂) (x : α) : h₁.read (·.map x) = h₂.read (·.map x) :=
  read_congr e _

end Inkproof.Scale.Shared
