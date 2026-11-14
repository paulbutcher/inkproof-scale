# Changelog

## [0.5.0]

- The float error proofs use `inkproof-core` v0.6.0's `Rat.abs` lemmas in place of private copies; the theorem statements say `Rat.abs` where they said `ratAbs`.

## [0.4.2]

- The README states that the float error theorems rely on Core's `float_rounding_model` axiom.

## [0.4.1]

- The documentation no longer calls floats opaque to proofs; it says Float is excluded because it is not a field.
- The tests use the shared test harness and Lasm driver from `inkproof-core` v0.5.1, and the private copies are gone.

## [0.4.0]

- The natural-number cast lemmas are no longer published; use `Lean.Grind.OrderedRing` in Lean core.

## [0.3.0]

- Log, elapsed-duration and categorical scales, with monotonicity, inversion and composition proved.
- Shared scale handles, proved to give every holder the same reading.
- Linear scales constrained to a checked domain property, such as including zero.

## [0.2.0]

- Rebasing for linear scales and affine maps, proved equal to the unrebased map.
- Float linear and rebased maps proved within an explicit bound of the exact result, under `Inkproof.Core.float_rounding_model`.

## [0.1.1]

The README shows the require line and lists v0.1.0 in the supported versions.

## [0.1.0]

Affine transforms and linear scales, with order-preservation, invertibility and composition proved.
