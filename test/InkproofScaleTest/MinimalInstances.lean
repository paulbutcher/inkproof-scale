/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scale
import Inkproof.Scale.Proofs

/-! VAL-1 and VAL-2: the theorems instantiated with `Rat` scales whose domains exclude zero, one of
them with screen y's downward range, with every hypothesis discharged and the theorems applied. -/

namespace InkproofScaleTest.MinimalInstances

open Inkproof.Scale

/-- Timestamps far from zero, onto 800 pixels. -/
def time : Linear Rat := ⟨1000000, 1000060, 0, 800⟩

/-- Negative readings onto a 600-pixel range drawn downwards. -/
def reading : Linear Rat := ⟨-40, -10, 600, 0⟩

theorem time_increasing :
    time.domainStart < time.domainEnd ∧ time.rangeStart < time.rangeEnd ∨
      time.domainEnd < time.domainStart ∧ time.rangeEnd < time.rangeStart := by
  simp only [time]; grind

theorem reading_decreasing :
    reading.domainStart < reading.domainEnd ∧ reading.rangeEnd < reading.rangeStart ∨
      reading.domainEnd < reading.domainStart ∧ reading.rangeStart < reading.rangeEnd := by
  simp only [reading]; grind

theorem time_nondegenerate : time.domainStart ≠ time.domainEnd ∧ time.rangeStart ≠ time.rangeEnd := by
  simp only [time]; grind

theorem reading_nondegenerate :
    reading.domainStart ≠ reading.domainEnd ∧ reading.rangeStart ≠ reading.rangeEnd := by
  simp only [reading]; grind

example (x y : Rat) (h : x < y) : time.map x < time.map y :=
  (time.map_lt_map_iff_of_increasing time_increasing).mpr h

/-- A higher reading is drawn higher up the screen, at a smaller y. -/
example (x y : Rat) (h : x ≤ y) : reading.map y ≤ reading.map x :=
  (reading.map_le_map_iff_of_decreasing reading_decreasing).mpr h

example (x : Rat) : time.inv.map (time.map x) = x :=
  time.inv_map_map time_nondegenerate.1 time_nondegenerate.2 x

example (py : Rat) : reading.map (reading.inv.map py) = py :=
  reading.map_inv_map reading_nondegenerate.1 reading_nondegenerate.2 py

example : reading.map reading.domainEnd = reading.rangeEnd :=
  reading.map_domainEnd reading_nondegenerate.1

/-- Rebasing in the shape SCALE-3 will need: subtracting a view origin from the data before a scale
fitted to the rebased domain is the same as the original scale, as a single affine map. -/
def rebase : Affine Rat := ⟨1, -1000000⟩

def rebasedTime : Linear Rat := ⟨0, 60, 0, 800⟩

example (x : Rat) : (rebasedTime.toAffine.comp rebase).apply x = time.map x := by
  rw [Affine.comp_apply, Linear.toAffine_apply, Linear.map_eq, Linear.map_eq]
  simp only [rebase, rebasedTime, time, Affine.apply]
  grind

/-- Data to device pixels and back, through the scale composed with a device-pixel-ratio transform. -/
example (x : Rat) :
    (time.toAffine.inv.comp (Affine.mk 2 0).inv).apply ((Affine.mk 2 0).comp time.toAffine |>.apply x)
      = x := by
  have hs : (Affine.mk (2 : Rat) 0).slope ≠ 0 := by simp only; grind
  have ht := time.toAffine_slope_ne_zero time_nondegenerate.1 time_nondegenerate.2
  rw [Affine.comp_apply, Affine.comp_apply, Affine.inv_apply_apply _ hs, Affine.inv_apply_apply _ ht]

end InkproofScaleTest.MinimalInstances
