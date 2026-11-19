/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scale.Linear

universe u

namespace Inkproof.Scale

/-- Optional limits on an automatic range. A soft limit is a value the range reaches at least as
far as; a hard limit is one it never passes. -/
structure RangeLimits (α : Type u) where
  softLo : Option α := none
  softHi : Option α := none
  hardLo : Option α := none
  hardHi : Option α := none
  deriving Repr

variable {α : Type u}

/-- The extent from `lo` to `hi` (with `lo ≤ hi`) padded on each side by `pad` times its width, or
by one where it has no width. The padding does not carry the range across zero when the extent does
not: an extent on one side of zero stays on it. See `padExtent_contains` and `padExtent_lt`. -/
def padExtent [Add α] [Sub α] [Mul α] [OfNat α 0] [OfNat α 1] [LT α] [DecidableLT α]
    (pad lo hi : α) : α × α :=
  let d := if lo < hi then (hi - lo) * pad else 1
  let a := lo - d
  let b := hi + d
  (if lo < 0 then a else if a < 0 then 0 else a,
   if lo < 0 then (if 0 < hi then b else if 0 < b then 0 else b) else b)

/-- The range from `a` to `b` widened to reach each soft limit, then clipped to each hard one; see
`apply_le` and `le_apply`. -/
def RangeLimits.apply [LT α] [DecidableLT α] (l : RangeLimits α) (r : α × α) : α × α :=
  let a := match l.softLo with | some s => if s < r.1 then s else r.1 | none => r.1
  let b := match l.softHi with | some s => if r.2 < s then s else r.2 | none => r.2
  (match l.hardLo with | some h => if a < h then h else a | none => a,
   match l.hardHi with | some h => if h < b then h else b | none => b)

/-- The range a chart shows for data spanning `lo` to `hi` (with `lo ≤ hi`): the extent padded, as
`padExtent` does, then limited by `l`. See `autoRange_contains` and `autoRange_nonempty`. -/
def autoRange [Add α] [Sub α] [Mul α] [OfNat α 0] [OfNat α 1] [LT α] [DecidableLT α]
    (pad lo hi : α) (l : RangeLimits α := {}) : α × α :=
  l.apply (padExtent pad lo hi)

end Inkproof.Scale
