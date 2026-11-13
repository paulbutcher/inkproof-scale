/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scale
import InkproofTools.Test.Harness

/-! Float durations: a count of units mapped through the composed conversion agrees with mapping its
seconds directly, to within rounding. -/

namespace InkproofScaleTest.ElapsedTests

open InkproofTools.Test

open Inkproof.Scale

def floatConversion : TestCase := .mk "Float unit conversion composes with a duration scale" <|
  forAll 2000 (fun g =>
    let (u, g) := g.below 3600
    let (n, g) := g.below 100000
    let (a, g) := g.below 100000
    ((u + 1, n, a), g)) fun (u, n, a) => do
    let u : Float := u.toFloat
    let n : Float := n.toFloat
    let s := Linear.ofDurations ⟨a.toFloat⟩ ⟨a.toFloat + 1000000⟩ 0 800
    let viaAffine := (s.toAffine.comp (Duration.unitAffine u)).apply n
    let direct := s.map (Duration.ofUnits u n).seconds
    check ((viaAffine - direct).abs ≤ 1e-6 * (direct.abs + 1)) s!"{viaAffine} vs {direct}"
    let back := (Duration.ofUnits u n).toUnits u
    check ((back - n).abs ≤ 1e-9 * (n.abs + 1)) s!"round trip {back} vs {n}"

def tests : List TestCase := [floatConversion]

end InkproofScaleTest.ElapsedTests
