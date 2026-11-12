/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scale.Elapsed
import Inkproof.Scale.Proofs.Linear

universe u

namespace Inkproof.Scale

open Lean.Grind

variable {α : Type u}

namespace Duration

/-- A count of units lasts that count times the unit. -/
theorem ofUnits_seconds [Mul α] (unitSeconds n : α) : (ofUnits unitSeconds n).seconds = n * unitSeconds :=
  rfl

/-- A duration's count of units is its seconds over the unit. -/
theorem toUnits_eq [Div α] (d : Duration α) (unitSeconds : α) :
    d.toUnits unitSeconds = d.seconds / unitSeconds :=
  rfl

/-- PROOF-5: where the unit is nonzero, converting a duration to units and back gives the duration
it started as. -/
theorem ofUnits_toUnits [Field α] (d : Duration α) {u : α} (hu : u ≠ 0) :
    ofUnits u (d.toUnits u) = d := by
  have : u * u⁻¹ = 1 := Field.mul_inv_cancel hu
  cases d
  simp only [ofUnits, toUnits, Field.div_eq_mul_inv, Duration.mk.injEq]; grind

/-- PROOF-5: where the unit is nonzero, converting units to a duration and back gives the count it
started as. -/
theorem toUnits_ofUnits [Field α] {u : α} (hu : u ≠ 0) (n : α) : (ofUnits u n).toUnits u = n := by
  have : u * u⁻¹ = 1 := Field.mul_inv_cancel hu
  simp only [ofUnits, toUnits, Field.div_eq_mul_inv]; grind

/-- The unit conversion maps a count of units to the seconds it lasts. -/
theorem unitAffine_apply [Field α] (u n : α) : (unitAffine u).apply n = (ofUnits u n).seconds := by
  simp only [Affine.apply, unitAffine, ofUnits]; grind

/-- PROOF-5: where the unit is nonzero, the conversion's inverse takes seconds to a count of units. -/
theorem unitAffine_inv_apply [Field α] {u : α} (hu : u ≠ 0) (d : Duration α) :
    (unitAffine u).inv.apply d.seconds = d.toUnits u := by
  have : u * u⁻¹ = 1 := Field.mul_inv_cancel hu
  simp only [Affine.inv_eq, Affine.apply, unitAffine, toUnits, Field.div_eq_mul_inv]; grind

end Duration

namespace Linear

/-- A scale between durations maps a duration as the linear scale over seconds maps its seconds. -/
theorem ofDurations_map [Add α] [Sub α] [Mul α] [Div α] (start stop : Duration α)
    (rangeStart rangeEnd : α) (d : Duration α) :
    (ofDurations start stop rangeStart rangeEnd).map d.seconds =
      rangeStart + (d.seconds - start.seconds) * (rangeEnd - rangeStart) /
        (stop.seconds - start.seconds) :=
  rfl

/-- PROOF-5: a scale over seconds composed after the unit conversion maps a count of units to
what the scale maps the seconds it lasts to. -/
theorem toAffine_comp_unitAffine_apply [Field α] (s : Linear α) (u n : α) :
    (s.toAffine.comp (Duration.unitAffine u)).apply n = s.map (Duration.ofUnits u n).seconds := by
  rw [Affine.comp_apply, Duration.unitAffine_apply, toAffine_apply]

end Linear

end Inkproof.Scale
