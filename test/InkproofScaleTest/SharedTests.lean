/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scale
import InkproofScaleTest.Harness

/-! Two charts holding one handle agree before and after an update. -/

namespace InkproofScaleTest.SharedTests

open Inkproof.Scale

def chartsAgree : TestCase := .mk "Charts sharing a handle agree, also after a zoom" <|
  forAll 2000 (fun g =>
    let (a, g) := g.below 1000
    let (w, g) := g.below 1000
    let (x, g) := g.below 5000
    ((a, w + 1, x), g)) fun (a, w, x) => do
    let h : Shared (Linear Float) := ⟨⟨a.toFloat, (a + w).toFloat, 0, 800⟩⟩
    let chartA := h
    let chartB := h
    check (chartA.read (·.map x.toFloat) == chartB.read (·.map x.toFloat)) "charts disagree"
    let zoomed := h.update fun s => { s with domainEnd := s.domainStart + 1 }
    check (zoomed.read (·.map x.toFloat) == (Linear.map ⟨a.toFloat, a.toFloat + 1, 0, 800⟩ x.toFloat))
      "zoomed handle differs from the zoomed scale"
    check (zoomed.read (·.domainEnd) == a.toFloat + 1) "zoom not visible through the handle"

def tests : List TestCase := [chartsAgree]

end InkproofScaleTest.SharedTests
