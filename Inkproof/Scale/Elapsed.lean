/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scale.Linear

universe u

namespace Inkproof.Scale

/-- A length of elapsed time, held in seconds so that every unit is a scale factor away. -/
structure Duration (α : Type u) where
  seconds : α
  deriving Repr

namespace Duration

variable {α : Type u}

/-- The duration of `n` units that are each `unitSeconds` long; see `ofUnits_seconds`. -/
def ofUnits [Mul α] (unitSeconds n : α) : Duration α := ⟨n * unitSeconds⟩

/-- The number of units of `unitSeconds` seconds in the duration; see `toUnits_ofUnits`. -/
def toUnits [Div α] (d : Duration α) (unitSeconds : α) : α := d.seconds / unitSeconds

/-- The affine map from a count of units of `unitSeconds` seconds to seconds, for composing with a
scale over seconds; see `unitAffine_apply` and `toAffine_comp_unitAffine_apply`. -/
def unitAffine [OfNat α 0] (unitSeconds : α) : Affine α := ⟨unitSeconds, 0⟩

end Duration

namespace Linear

variable {α : Type u}

/-- The linear scale taking the span from `start` to `stop` onto the range, so that elapsed
durations are plotted along an ordinary linear scale over seconds; see `ofDurations_map`. -/
def ofDurations (start stop : Duration α) (rangeStart rangeEnd : α) : Linear α :=
  ⟨start.seconds, stop.seconds, rangeStart, rangeEnd⟩

end Linear

end Inkproof.Scale
