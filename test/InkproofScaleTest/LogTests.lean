/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scale
import InkproofTools.Test.Harness

/-! Float logarithmic scales: what rounding must still preserve. -/

namespace InkproofScaleTest.LogTests

open InkproofTools.Test

open Inkproof.Scale

def floatLog : TestCase := .mk "Float log scale keeps order, its start and round trips" <|
  forAll 2000 (fun g =>
    let (a, g) := g.below 1000
    let (b, g) := g.below 100000
    let (x, g) := g.below 100000
    let (y, g) := g.below 100000
    ((a + 1, b + 2, x + 1, y + 1), g)) fun (a, b, x, y) => do
    let a : Float := a.toFloat
    let s : Log Float := ⟨a, a + b.toFloat, 0, 800⟩
    let x : Float := x.toFloat
    let y : Float := y.toFloat
    check (s.map Float.log s.domainStart == 0) "domainStart not at rangeStart"
    check (x ≤ y → s.map Float.log x ≤ s.map Float.log y) s!"order {x} {y}"
    let back := s.unmap Float.log Float.exp (s.map Float.log x)
    check ((back - x).abs ≤ 1e-9 * x) s!"round trip {back} vs {x}"

def tests : List TestCase := [floatLog]

end InkproofScaleTest.LogTests
