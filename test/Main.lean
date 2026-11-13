/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Scale
import InkproofTools.Test.Platform
import InkproofScaleTest.LinearTests
import InkproofScaleTest.ElapsedTests
import InkproofScaleTest.LogTests
import InkproofScaleTest.CategoricalTests
import InkproofScaleTest.SharedTests
import InkproofScaleTest.ConstrainedTests

open InkproofScaleTest InkproofTools.Test

def main (args : List String) : IO UInt32 :=
  runTests (platformTest (args.contains "--expect-wasm") :: LinearTests.tests ++ ElapsedTests.tests ++ LogTests.tests ++ CategoricalTests.tests ++ SharedTests.tests ++ ConstrainedTests.tests)
