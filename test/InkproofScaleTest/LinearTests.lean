/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scale
import InkproofTools.Test.Harness

/-! Linear scales run natively and under Lasm. Over `Rat` the theorems already say what these check,
so the tests guard the compilers beneath them. Over `Float` there are no theorems, since floats are
opaque to proofs and are not a field; the properties here are what rounding must still preserve. -/

namespace InkproofScaleTest.LinearTests

open InkproofTools.Test

open Inkproof.Scale

/-- A whole number in `[-span, span]`. -/
def genInt (span : Nat) (g : Rng) : Int × Rng :=
  let (n, g) := g.below (2 * span + 1)
  (n - span, g)

/-- Two distinct whole numbers, in either order. -/
def genInterval (span : Nat) (g : Rng) : (Int × Int) × Rng :=
  let (a, g) := genInt span g
  let (d, g) := g.below span
  let (down, g) := g.below 2
  let b := a + d + 1
  (if down == 0 then (a, b) else (b, a), g)

/-- A scale with nondegenerate intervals far from zero half the time, and two points in its domain
space. -/
def genCase (g : Rng) : (Int × Int × Int × Int × Int × Int) × Rng :=
  let (far, g) := g.below 2
  let base : Int := if far == 0 then 0 else 1700000000
  let ((d₀, d₁), g) := genInterval 1000 g
  let ((r₀, r₁), g) := genInterval 1000 g
  let (x, g) := genInt 2000 g
  let (y, g) := genInt 2000 g
  ((base + d₀, base + d₁, r₀, r₁, base + x, base + y), g)

def ratScale (c : Int × Int × Int × Int × Int × Int) : Linear Rat × Rat × Rat :=
  let (d₀, d₁, r₀, r₁, x, y) := c
  (⟨d₀, d₁, r₀, r₁⟩, x, y)

def floatScale (c : Int × Int × Int × Int × Int × Int) : Linear Float × Float × Float :=
  let (d₀, d₁, r₀, r₁, x, y) := c
  (⟨.ofInt d₀, .ofInt d₁, .ofInt r₀, .ofInt r₁⟩, .ofInt x, .ofInt y)

def increasing {α : Type} [LT α] [DecidableLT α] (s : Linear α) : Bool :=
  (s.domainStart < s.domainEnd) == (s.rangeStart < s.rangeEnd)

def ratExact : TestCase := .mk "Rat scales hit their endpoints, invert exactly and keep order" <|
  forAll 2000 genCase fun c => do
    let (s, x, y) := ratScale c
    check (s.map s.domainStart == s.rangeStart) "domainStart does not map to rangeStart"
    check (s.map s.domainEnd == s.rangeEnd) "domainEnd does not map to rangeEnd"
    check (s.inv.map (s.map x) == x) "inv.map does not undo map"
    check (s.toAffine.apply x == s.map x) "toAffine disagrees with map"
    check (s.toAffine.inv.apply (s.map x) == x) "toAffine.inv does not undo map"
    let sameOrder := (s.map x ≤ s.map y) == (x ≤ y)
    check (if increasing s then sameOrder else (s.map y ≤ s.map x) == (x ≤ y)) "order not kept"

/-- Within `tol` times the larger magnitude. -/
def close (a b tol : Float) : Bool :=
  (a - b).abs ≤ tol * max 1 (max a.abs b.abs)

def floatRounding : TestCase := .mk "Float scales keep order and invert to within rounding" <|
  forAll 2000 genCase fun c => do
    let (s, x, y) := floatScale c
    -- Each IEEE operation is monotone, so their composition keeps non-strict order.
    if x ≤ y then
      check (if increasing s then s.map x ≤ s.map y else s.map y ≤ s.map x) "order not kept"
    check (s.map s.domainStart == s.rangeStart) "domainStart does not map to rangeStart"
    check (close (s.map s.domainEnd) s.rangeEnd 1e-12) s!"domainEnd maps to {s.map s.domainEnd}"
    check (close (s.inv.map (s.map x)) x 1e-12) s!"round trip gives {s.inv.map (s.map x)}"
    check (close (s.toAffine.apply x) (s.map x) 1e-6) "toAffine disagrees with map"

def tests : List TestCase := [ratExact, floatRounding]

end InkproofScaleTest.LinearTests
