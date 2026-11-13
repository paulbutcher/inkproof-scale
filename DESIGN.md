# Inkproof.Scale design

Inkproof.Scale maps values between data space and screen space with scales and affine transforms whose order-preservation, invertibility and composition are proved. It knows about ordered fields and intervals, never about what the data measures. Requirement IDs refer to `REQUIREMENTS.md` in `inkproof-coordination`.

## Packages and modules

- The package `inkproof-scale` depends only on `inkproof-core`, at a release tag, and on Lean at the toolchain Lasm supports (`lean-toolchain`); it builds natively and under Lasm from the same source (ARCH-1, PLAT-1).
- Runtime modules live under `Inkproof.Scale`, and `import Inkproof.Scale` brings in all of them; this is what a browser build links.
- Published theorems live under `Inkproof.Scale.Proofs`, which runtime modules never import (PROC-5, PLAT-3).
- The library declares no axioms. The tests fail if a declaration depends on any axiom beyond Lean's `propext`, `Classical.choice` and `Quot.sound` and those in `Inkproof.Core.Axioms` (PROC-1).

## Generic foundations

- Definitions take only the operations they compute with (`Add`, `Mul`, `Div` and so on), so the same code runs on `Rat`, `Float` or a consumer's own type.
- Theorems are stated over any ordered field, given by Lean core's `Lean.Grind.Field`, `Lean.Grind.OrderedRing`, `Std.IsLinearOrder` and `Std.LawfulOrderLT` (FP-1), the classes Lean's own ordered-field lemmas use. `Rat` has them all. The library does not use Mathlib.
- Order hypotheses appear only on the theorems about order; the algebraic theorems need only `Lean.Grind.Field`.
- Nondegeneracy (`slope ≠ 0`, `domainStart ≠ domainEnd`) is a theorem hypothesis, not a structure field. A field would need a proof of nondegeneracy for every `Float` scale.

## Affine transforms

- `Affine α` is the map `x ↦ slope * x + offset` on one axis (SCALE-2). A 2D transform between data and screen space is one per axis.
- `comp` combines two transforms into one, and `comp_apply` proves it maps every point as applying the two in turn does (PROOF-5). `id` is its identity, and composition is associative.
- `inv` is total, with the field convention `0⁻¹ = 0`; the theorems that it undoes the map assume a nonzero slope (PROOF-5).
- A positive slope preserves order and a negative one reverses it, strictly and non-strictly.

## Linear scales

- `Linear α` takes the domain interval `domainStart`, `domainEnd` onto the range interval `rangeStart`, `rangeEnd` (SCALE-1). Either may run downwards, as screen y usually does, so monotonicity is stated for both directions.
- `map` computes `rangeStart + (x - domainStart) * (rangeEnd - rangeStart) / (domainEnd - domainStart)`, so `domainStart` maps to `rangeStart` exactly, in floats too. `toAffine` gives the same map as an `Affine`, for composing, and `toAffine_apply` proves they agree.
- `inv` swaps domain and range. Where both are nondegenerate, it undoes `map` and its affine map is the inverse of the scale's (PROOF-5).
- Rebasing (SCALE-3) composes a scale's affine map with a translation, and the test subproject shows that shape.

## Shared scales

- `Shared σ` is a handle on a scale (SCALE-4). Linked charts hold the same handle and read it with `read`, so `read_congr` proves they agree, and `read_update` that after a zoom or pan they all read the updated scale.

## Constrained domains

- `Constrained α P` is a linear scale with a proof that `P domainStart domainEnd` holds, for a consumer's constraint `P` (SCALE-6). `Linear.check?` and `withDomain?` build one by testing `P`, so a zoom that breaks it is refused, never applied; the proof is erased at run time.
- `Includes v` is the constraint "the domain contains `v`", in either direction. `Includes.widen` moves a domain outward until it does, and leaves one that already does alone.

## Elapsed durations

- `Duration α` is a length of time in seconds (SCALE-1). `Linear.ofDurations` builds an ordinary linear scale over seconds, so every Linear theorem, including monotonicity and inversion, applies unchanged and nothing is restricted.
- A unit is a scale factor in seconds. `Duration.ofUnits` and `toUnits` convert, inverse to each other for a nonzero unit, and `unitAffine` is the same conversion as an `Affine` for composing with a scale (PROOF-5).

## Log scales

- `Log α` is a linear scale over logarithms (SCALE-1). The logarithm and its inverse are parameters of `map` and `unmap`, so `Float.log` and `Float.exp` run it and the theorems need only what a real logarithm provides.
- The hypotheses are ones a consumer meets with positive data: `exp (log x) = x` for the point inverted, and for order, `log x ≤ log y ↔ x ≤ y` at positive `x` and `y`. Composition with an `Affine` is `toAffine_comp_apply` (PROOF-5).

## Categorical scales

- `Categorical κ α` divides a range into one equal band per category, in the order of the array (SCALE-1). `bandStart i` is `rangeStart + i * bandwidth`, equal to the `Affine` `toAffine` applied to the index, so composing with a transform is `Affine.comp`.
- `map?` and `unmap?` are partial: a value that is not a category has no band, and a position that starts no band has no category. A repeated category maps through its first occurrence.
- Where the range is nondegenerate, band starts are ordered with the index (upwards or downwards) and distinct, and `unmap?` undoes `map?` (PROOF-5). Counting needs an ordered field of characteristic zero, which the ordered-field classes give.

## Floats

- `Float` is not covered by the theorems: it is not a field, though Lean models it as IEEE 754 binary64, so it is not opaque to proofs. Float scales run the same definitions, and the tests check what rounding must still preserve: non-strict order, `domainStart` mapping exactly to `rangeStart`, and round trips to within a relative `1e-12`.
- `Inkproof.Scale.Proofs.FloatBound` proves the Float affine, linear and rebased maps within an explicit multiple of `2 ^ -49` of the exact result, assuming no overflow or subnormal intermediate; binary32 is not covered.

## Testing

- Tests live in the `test` subproject (CLAUDE.md's Test layout). `lake test` builds it, runs `Main.lean` natively, then compiles and runs the same `Main.lean` with Lasm, pinned exactly in `test/package.json`. A check inside the program confirms that the Lasm run executes as wasm. Without Lasm the step is skipped with a warning; with `INKPROOF_REQUIRE_LASM=1` the skip fails instead.
- VAL-1 and VAL-2 live in the test library, where compiling is passing: `Rat` scales whose domains exclude zero, one with a downward range, with every hypothesis discharged and the theorems applied.

## API lock

- `scripts/api-lock.sh` runs Inkproof.Core's `api-lock` executable over `Inkproof.Scale` and `Inkproof.Scale.Proofs`: one line per public declaration, with theorem statements as their types. CI compares the output with `API.lock`, and CODEOWNERS sends changes to the human.
