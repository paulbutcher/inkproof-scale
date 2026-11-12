/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scale
import InkproofScaleTest.Harness

/-! Float categorical scales: bands stay ordered, start at the range's start and invert. -/

namespace InkproofScaleTest.CategoricalTests

open Inkproof.Scale

instance : NatCast Float := ⟨Float.ofNat⟩

def floatBands : TestCase := .mk "Float categorical scale orders bands and inverts them" <|
  forAll 2000 (fun g =>
    let (n, g) := g.below 40
    let (a, g) := g.below 1000
    let (w, g) := g.below 100000
    ((n + 1, a, w + 1), g)) fun (n, a, w) => do
    let cats := (Array.range n).map (s!"c{·}")
    let s : Categorical String Float := ⟨cats, a.toFloat, a.toFloat + w.toFloat⟩
    check (s.map? "c0" == some s.rangeStart) "first band not at rangeStart"
    check (s.map? "missing" == none) "unknown category mapped"
    for i in [0:n] do
      let k := s!"c{i}"
      match s.map? k with
      | none => check false s!"{k} unmapped"
      | some y =>
        check (s.unmap? y == some k) s!"{k} did not invert"
        if i + 1 < n then
          check (y < s.bandStart (i + 1)) s!"{k} band not before the next"

def tests : List TestCase := [floatBands]

end InkproofScaleTest.CategoricalTests
