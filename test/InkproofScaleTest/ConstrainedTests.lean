/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scale
import InkproofTools.Test.Harness

/-! A scale constrained to include zero stays so through every zoom that is accepted. -/

namespace InkproofScaleTest.ConstrainedTests

open InkproofTools.Test

open Inkproof.Scale

def includesZero : TestCase := .mk "Zooms are accepted exactly when the domain includes zero" <|
  forAll 2000 (fun g =>
    let (a, g) := g.below 200
    let (b, g) := g.below 200
    let (c, g) := g.below 200
    let (d, g) := g.below 200
    ((a, b, c, d), g)) fun (a, b, c, d) => do
    let lo := a.toFloat - 100
    let hi := b.toFloat - 100
    let nlo := c.toFloat - 100
    let nhi := d.toFloat - 100
    let s : Linear Float := ⟨lo, hi, 0, 800⟩
    let inc (x y : Float) : Bool := (x ≤ 0 && 0 ≤ y) || (y ≤ 0 && 0 ≤ x)
    check ((s.check? (Includes (0 : Float))).isSome == inc lo hi) "check? disagrees with the constraint"
    match s.check? (Includes (0 : Float)) with
    | none => pure ()
    | some k =>
      match k.withDomain? nlo nhi with
      | none => check (!inc nlo nhi) "zoom containing zero refused"
      | some z =>
        check (inc nlo nhi) "zoom excluding zero accepted"
        check (z.scale.domainStart == nlo && z.scale.domainEnd == nhi && z.scale.rangeEnd == 800)
          "accepted zoom changed more than the domain"

def widenIncludes : TestCase := .mk "Widening keeps direction and includes the value" <|
  forAll 2000 (fun g =>
    let (a, g) := g.below 200
    let (b, g) := g.below 200
    ((a, b), g)) fun (a, b) => do
    let x := a.toFloat - 100
    let y := b.toFloat - 100
    let (lo, hi) := Includes.widen (0 : Float) x y
    check ((lo ≤ 0 && 0 ≤ hi) || (hi ≤ 0 && 0 ≤ lo)) "result excludes zero"
    check ((x ≤ y) == (lo ≤ hi) || lo == hi) "direction changed"
    let included := (x ≤ 0 && 0 ≤ y) || (y ≤ 0 && 0 ≤ x)
    check (!included || (lo == x && hi == y)) "included domain was changed"

def tests : List TestCase := [includesZero, widenIncludes]

end InkproofScaleTest.ConstrainedTests
