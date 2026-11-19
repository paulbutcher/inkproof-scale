/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scale
import InkproofTools.Test.Harness

/-! Float automatic ranges: they contain the data, keep one-signed data on its side of zero, and
are never empty. -/

namespace InkproofScaleTest.AutoRangeTests

open InkproofTools.Test

open Inkproof.Scale

def floatRanges : TestCase := .mk "Float auto range contains the data and is never empty" <|
  forAll 2000 (fun g =>
    let (a, g) := g.below 200001
    let (w, g) := g.below 1000
    let (p, g) := g.below 50
    ((a.toFloat - 100000, w.toFloat, p.toFloat / 100), g)) fun (lo, w, pad) => do
    let hi := lo + w
    let (a, b) := autoRange pad lo hi
    check (a ≤ lo && hi ≤ b) "range does not contain the data"
    check (a < b) "range is empty"
    check (!(0 ≤ lo) || 0 ≤ a) "range crossed zero below non-negative data"
    check (!(hi ≤ 0) || b ≤ 0) "range crossed zero above non-positive data"

def zeroRule : TestCase := .mk "Float auto range keeps data away from zero at zero" <| do
  let (a, b) := autoRange (0.1 : Float) 3 97
  check (a == 0) "start not held at zero"
  check (b > 97 && b < 107) "end not padded by a tenth of the width"

def limits : TestCase := .mk "Float auto range honours soft and hard limits" <| do
  let (a, b) := autoRange (0.1 : Float) 40 60 { softLo := some 0, softHi := some 100, hardHi := some 90 }
  check (a == 0) "soft start not reached"
  check (b == 90) "hard end not applied"

def tests : List TestCase := [floatRanges, zeroRule, limits]

end InkproofScaleTest.AutoRangeTests
