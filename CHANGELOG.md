# Changelog

## [0.12.1]

- README names no pinned versions; it points to the latest release tag and to `lakefile.lean`.

## [0.12.0]

- Removes `Categorical.inv_pos_of_pos`; use core's `Lean.Grind.Field.IsOrdered.inv_pos_iff`.

## [0.11.0]

- Adds `Transformed`, a scale linear in a caller-supplied transform, and `Asinh`, an arcsinh scale, with inversion and monotonicity proved.

## [0.10.0]

- Adds `autoRange`, the range a chart shows for a data extent, with `padExtent` and `RangeLimits`.

## [0.9.0]

- Adds `Categorical.bandCentre`, the middle of a category's band.

## [0.8.0]

- Adds `Affine.rebaseErrorBound`, the bound stated by `Affine.rebase_apply_float_error` and `Affine.rebase_apply_float32_error`, evaluable at a view.

## [0.7.1]

- Lasm tests run under `@lasm/cli` 0.8.0.

## [0.7.0]

- Adds `Affine.rebase_apply_float32_error`, the binary32 counterpart of `Affine.rebase_apply_float_error`.

## [0.6.1]

- Depends on `inkproof-float` v0.4.0 and uses its rounding-unit lemmas in place of private constants.

## [0.6.0]

- Depends on `inkproof-float` v0.2.0 instead of `inkproof-core`; the float error theorems are stated over `Inkproof.Float` names.
- Uses `inkproof-float`'s relative-error lemmas in place of private copies.

## [0.5.2]

- Development tooling and the axiom check come from `inkproof-tools` v0.2.0; `inkproof-core` is required at v0.6.1.

## [0.5.1]

- `approx_rel` in the float error proofs is derived from Core's `Float.Approximates.rel`.

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
