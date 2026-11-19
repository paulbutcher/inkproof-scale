/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scale.AutoRange

universe u

namespace Inkproof.Scale

open Lean.Grind

variable {α : Type u} [LT α] [DecidableLT α]

section Limits

variable [LE α] [Std.IsLinearOrder α] [Std.LawfulOrderLT α] {l : RangeLimits α} {r : α × α}

/-- Where no hard limit passes `x`, applying the limits leaves the range's start at or below it,
provided it was. -/
theorem RangeLimits.apply_le {x : α} (h : r.1 ≤ x) (hl : ∀ h, l.hardLo = some h → h ≤ x) :
    (l.apply r).1 ≤ x := by
  obtain ⟨sl, sh, hl', hh'⟩ := l
  simp only [RangeLimits.apply] at *
  rcases sl with _ | s <;> rcases hl' with _ | h' <;> simp <;> grind

/-- Where no hard limit passes `x`, applying the limits leaves the range's end at or above it,
provided it was. -/
theorem RangeLimits.le_apply {x : α} (h : x ≤ r.2) (hh : ∀ h, l.hardHi = some h → x ≤ h) :
    x ≤ (l.apply r).2 := by
  obtain ⟨sl, sh, hl', hh'⟩ := l
  simp only [RangeLimits.apply] at *
  rcases sh with _ | s <;> rcases hh' with _ | h' <;> simp <;> grind

/-- Without hard limits, applying the limits keeps the range's start below its end. -/
theorem RangeLimits.apply_lt (hl : l.hardLo = none) (hh : l.hardHi = none) (h : r.1 < r.2) :
    (l.apply r).1 < (l.apply r).2 := by
  obtain ⟨sl, sh, hl', hh'⟩ := l
  simp only at hl hh
  subst hl hh
  simp only [RangeLimits.apply]
  rcases sl with _ | s <;> rcases sh with _ | t <;> simp <;> grind

end Limits

section LimitEquations

variable {l : RangeLimits α} {r : α × α}

/-- With no limits set, the range is unchanged. -/
theorem RangeLimits.apply_default (r : α × α) : ({} : RangeLimits α).apply r = r := rfl

/-- With only a soft lower limit `s`, the range starts at `s` if that is below its start. -/
theorem RangeLimits.apply_fst_soft {s : α} (hs : l.softLo = some s) (hl : l.hardLo = none) :
    (l.apply r).1 = if s < r.1 then s else r.1 := by
  obtain ⟨sl, sh, hl', hh'⟩ := l
  simp only at hs hl
  subst hs hl
  simp [RangeLimits.apply]

/-- With only a soft upper limit `s`, the range ends at `s` if that is above its end. -/
theorem RangeLimits.apply_snd_soft {s : α} (hs : l.softHi = some s) (hh : l.hardHi = none) :
    (l.apply r).2 = if r.2 < s then s else r.2 := by
  obtain ⟨sl, sh, hl', hh'⟩ := l
  simp only at hs hh
  subst hs hh
  simp [RangeLimits.apply]

/-- With only a hard lower limit `h`, the range starts at `h` if its start is below it. -/
theorem RangeLimits.apply_fst_hard {h : α} (hs : l.softLo = none) (hl : l.hardLo = some h) :
    (l.apply r).1 = if r.1 < h then h else r.1 := by
  obtain ⟨sl, sh, hl', hh'⟩ := l
  simp only at hs hl
  subst hs hl
  simp [RangeLimits.apply]

/-- With only a hard upper limit `h`, the range ends at `h` if its end is above it. -/
theorem RangeLimits.apply_snd_hard {h : α} (hs : l.softHi = none) (hh : l.hardHi = some h) :
    (l.apply r).2 = if h < r.2 then h else r.2 := by
  obtain ⟨sl, sh, hl', hh'⟩ := l
  simp only at hs hh
  subst hs hh
  simp [RangeLimits.apply]

end LimitEquations

section Pad

variable [Field α] [LE α] [Std.IsLinearOrder α] [Std.LawfulOrderLT α] [OrderedRing α]
  {pad lo hi : α}

/-- The padded extent contains the extent. -/
theorem padExtent_contains (hp : 0 ≤ pad) (h : lo ≤ hi) :
    (padExtent pad lo hi).1 ≤ lo ∧ hi ≤ (padExtent pad lo hi).2 := by
  simp only [padExtent]
  have : 0 ≤ (hi - lo) * pad := by
    have : 0 ≤ hi - lo := by grind
    exact OrderedRing.mul_nonneg this hp
  constructor <;> split <;> grind

/-- The padded extent is never empty. -/
theorem padExtent_lt (hp : 0 ≤ pad) (h : lo ≤ hi) :
    (padExtent pad lo hi).1 < (padExtent pad lo hi).2 := by
  simp only [padExtent]
  have : 0 ≤ (hi - lo) * pad := by
    have : 0 ≤ hi - lo := by grind
    exact OrderedRing.mul_nonneg this hp
  split <;> split <;> grind

/-- Provided no hard limit cuts into the data, the range contains it. -/
theorem autoRange_contains {l : RangeLimits α} (hp : 0 ≤ pad) (h : lo ≤ hi)
    (hl : ∀ x, l.hardLo = some x → x ≤ lo) (hh : ∀ x, l.hardHi = some x → hi ≤ x) :
    (autoRange pad lo hi l).1 ≤ lo ∧ hi ≤ (autoRange pad lo hi l).2 :=
  ⟨l.apply_le (padExtent_contains hp h).1 hl, l.le_apply (padExtent_contains hp h).2 hh⟩

/-- Without hard limits, the range is never empty, however narrow the data, including a single
value. -/
theorem autoRange_nonempty {l : RangeLimits α} (hp : 0 ≤ pad) (h : lo ≤ hi)
    (hl : l.hardLo = none) (hh : l.hardHi = none) :
    (autoRange pad lo hi l).1 < (autoRange pad lo hi l).2 :=
  l.apply_lt hl hh (padExtent_lt hp h)

end Pad

section PadEquations

variable [Add α] [Sub α] [Mul α] [OfNat α 0] [OfNat α 1] {pad lo hi : α}

/-- Without limits, the automatic range is the padded extent. -/
theorem autoRange_default :
    autoRange pad lo hi = padExtent pad lo hi := rfl

/-- The padding is `pad` times the width of the extent, or one where it has no width. -/
theorem padExtent_of_neg {d : α} (hd : d = if lo < hi then (hi - lo) * pad else 1) (hlo : lo < 0) :
    padExtent pad lo hi = (lo - d, if 0 < hi then hi + d else if 0 < hi + d then 0 else hi + d) := by
  subst hd
  simp [padExtent, hlo]

/-- An extent that starts at or above zero is padded below only as far as zero. -/
theorem padExtent_of_nonneg {d : α} (hd : d = if lo < hi then (hi - lo) * pad else 1)
    (hlo : ¬ lo < 0) :
    padExtent pad lo hi = (if lo - d < 0 then 0 else lo - d, hi + d) := by
  subst hd
  simp [padExtent, hlo]

end PadEquations

section PadNonneg

variable [Field α] [LE α] [Std.IsLinearOrder α] [Std.LawfulOrderLT α] [OrderedRing α]
  {pad lo hi : α}

/-- Data that does not go below zero gets a range that does not either. -/
theorem padExtent_nonneg (hlo : 0 ≤ lo) : 0 ≤ (padExtent pad lo hi).1 := by
  simp only [padExtent]
  split <;> split <;> grind

end PadNonneg

end Inkproof.Scale
