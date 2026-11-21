/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scale
import InkproofTools.Test.Harness

/-! Float arcsinh and caller-supplied transform scales: what rounding must still preserve. -/

namespace InkproofScaleTest.TransformedTests

open InkproofTools.Test

open Inkproof.Scale

def floatAsinh : TestCase := .mk "Float asinh scale keeps order, its start and round trips" <|
  forAll 2000 (fun g =>
    let (t, g) := g.below 100
    let (a, g) := g.below 100000
    let (b, g) := g.below 100000
    let (x, g) := g.below 200000
    let (y, g) := g.below 200000
    ((t + 1, a, b + 1, x, y), g)) fun (t, a, b, x, y) => do
    let s : Asinh Float :=
      ⟨-a.toFloat, b.toFloat, 0, 800, t.toFloat⟩
    let x : Float := x.toFloat - 100000
    let y : Float := y.toFloat - 100000
    check (s.map Float.asinh s.domainStart == 0) "domainStart not at rangeStart"
    check (x ≤ y → s.map Float.asinh x ≤ s.map Float.asinh y) s!"order {x} {y}"
    let back := s.unmap Float.asinh Float.sinh (s.map Float.asinh x)
    check ((back - x).abs ≤ 1e-9 * (x.abs + 1)) s!"round trip {back} vs {x}"

def floatTransformed : TestCase := .mk "Float transform scale with a supplied inverse round trips" <|
  forAll 2000 (fun g =>
    let (x, g) := g.below 998
    (x, g)) fun x => do
    let f (v : Float) : Float := Float.log (-Float.log (1 - v))
    let g (v : Float) : Float := 1 - Float.exp (-Float.exp v)
    let s : Transformed Float := ⟨0.001, 0.999, 0, 800⟩
    let x : Float := (x.toFloat + 1) / 1000
    let back := s.unmap f g (s.map f x)
    check ((back - x).abs ≤ 1e-9) s!"round trip {back} vs {x}"

def tests : List TestCase := [floatAsinh, floatTransformed]

end InkproofScaleTest.TransformedTests
