/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
universe u v

namespace Inkproof.Scale

/-- A scale held by reference: linked charts each keep the same handle and read it through `read`,
so they agree by construction (SCALE-4). A zoom or pan is `update`, which gives the one new handle
every chart then holds; see `read_eq`, `read_congr` and `read_update`. -/
structure Shared (σ : Type u) where
  scale : σ

namespace Shared

variable {σ : Type u} {β : Type v}

/-- What a view computes from the shared scale, such as `Linear.map` at a point. -/
def read (h : Shared σ) (f : σ → β) : β := f h.scale

/-- The handle for the scale after `f`, for example a rebase or a new domain. -/
def update (h : Shared σ) (f : σ → σ) : Shared σ := ⟨f h.scale⟩

end Shared

end Inkproof.Scale
