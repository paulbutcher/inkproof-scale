/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scale
import InkproofScaleTest.Harness
import InkproofScaleTest.LinearTests
import InkproofScaleTest.ElapsedTests
import InkproofScaleTest.LogTests
import InkproofScaleTest.CategoricalTests

open InkproofScaleTest

/-- Guards against the Lasm step silently running a native build. -/
def platformTest (expectWasm : Bool) : TestCase :=
  .mk "runs on the expected platform" do
    check (System.Platform.isEmscripten == expectWasm)
      s!"isEmscripten = {System.Platform.isEmscripten}, target {System.Platform.target}"

def main (args : List String) : IO UInt32 :=
  runTests (platformTest (args.contains "--expect-wasm") :: LinearTests.tests ++ ElapsedTests.tests ++ LogTests.tests ++ CategoricalTests.tests)
