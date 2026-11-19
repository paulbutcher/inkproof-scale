# Inkproof.Scale

Linear scales and affine transforms between data space and screen space, with order-preservation, invertibility and composition proved. Part of the Inkproof charting libraries; it knows about ordered fields and intervals, never about what the data measures.

## What it does

- Map a data value to a screen position and back with a linear scale: `Linear.map`, `Linear.inv`, `Linear.toAffine`.
- Turn a scale into a plain slope and offset, apply, compose and invert it: `Affine.apply`, `Affine.comp`, `Affine.inv`.
- Put bands for categories (bar charts, heatmaps) on an axis, and look a category up by key or a position back to its category: `Categorical.bandStart`, `Categorical.bandwidth`, `Categorical.bandCentre`, `Categorical.map?`, `Categorical.unmap?`, `Categorical.index?`, `Categorical.toAffine`.
- Scale on a log axis: `Log.map`, `Log.unmap`, `Log.toLinear`.
- Scale time: convert durations and units, and build a scale from a time span: `Duration.ofUnits`, `Duration.toUnits`, `Duration.unitAffine`, `Linear.ofDurations`.
- Keep float precision when zoomed far into large coordinates by rebasing a scale to a nearby origin: `Affine.rebase`, `Linear.rebase`.
- Bound the Float rounding error of a map, rebased or not, for binary64 and binary32: `Linear.map_float_error`, `Linear.rebase_map_float_error`, `Affine.rebase_apply_float_error`, `Affine.rebase_apply_float32_error`, evaluated with `Affine.rebaseErrorBound` and `Linear.NormalSteps`.
- Require a scale's domain to satisfy a condition, such as nonzero width or positive values, and make a change of domain fail rather than break it: `Constrained`, `Linear.check?`, `Constrained.withDomain?`.
- Widen a domain so that it includes a value: `Includes`, `Includes.widen`.
- Choose the range a chart shows from its data extent, padded, kept at zero where the data does not cross it, and limited by soft and hard bounds: `autoRange`, `padExtent`, `RangeLimits`.
- Share one scale between linked charts so a zoom or pan reaches all of them: `Shared`, `Shared.read`, `Shared.update`.

## Supported versions

| Inkproof.Scale | Lean | Lasm (`@lasm/cli`) | Inkproof.Float |
| --- | --- | --- | --- |
| `main` | `leanprover/lean4:v4.35.0` | 0.8.0 | `v0.4.0` |
| `v0.7.1` | `leanprover/lean4:v4.35.0` | 0.8.0 | `v0.4.0` |

The library builds natively and under Lasm from the same source.

## Using it

```lean
require «inkproof-scale» from git "https://github.com/tentenths/inkproof-scale" @ "v0.7.1"
```

`import Inkproof.Scale` brings in everything a program runs. `import Inkproof.Scale.Proofs` adds the published theorems, which a browser build need not link. Each definition's docstring names the theorems about it, and each theorem's docstring states it in plain English.

## Guarantees

These hold for any ordered field: a type with Lean core's `Lean.Grind.Field`, `Lean.Grind.OrderedRing`, `Std.IsLinearOrder` and `Std.LawfulOrderLT`, such as `Rat`.

- Composing two affine transforms gives one that maps every point as applying them in turn does (`Affine.comp_apply`).
- An affine transform with a nonzero slope is undone by its inverse, in both directions (`Affine.inv_apply_apply`, `Affine.apply_inv_apply`).
- An affine transform with a positive slope preserves order, and one with a negative slope reverses it (`Affine.apply_le_apply_iff_of_pos` and its variants).
- A linear scale maps its domain's start and end to its range's (`Linear.map_domainStart`, `Linear.map_domainEnd`), and agrees with its affine map (`Linear.toAffine_apply`).
- A linear scale with a nondegenerate domain and range is undone by its inverse, in both directions (`Linear.inv_map_map`, `Linear.map_inv_map`).
- A linear scale preserves order when its domain and range run the same way, and reverses it when they run opposite ways, as with screen y (`Linear.map_le_map_iff_of_increasing`, `Linear.map_le_map_iff_of_decreasing` and their strict variants).

`Float` is not covered by the theorems: it is not a field (rounding breaks the field laws), though Lean models it as IEEE 754 binary64, so it is not opaque to proofs. Float scales run the same code, and the tests check that rounding keeps order and that round trips land within a relative `1e-12`. A check in the tests fails if any axiom beyond Lean's own and those in `Inkproof.Float.Axioms` creeps in. [DESIGN.md](DESIGN.md) describes the design, and `API.lock` lists every public declaration and theorem statement.

## Trusted computing base

The proofs cover the Lean source. These are trusted beneath them:

| Component | Why trusted | Mitigation |
| --- | --- | --- |
| Lean compiler and runtime | Compiles the proved source | Pinned in `lean-toolchain`; the same test program runs natively and under Lasm |
| Lasm compiler, runtime and Emscripten | Compiles Lean to Wasm | Pinned exactly in the test subproject; the same test program runs natively and under Lasm |

The library declares no axioms of its own; its float error theorems rely on Float's `float_rounding_model` axiom (FP-3). It has no generated code and no hand-written JavaScript.
