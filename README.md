# Inkproof.Scale

Linear scales and affine transforms between data space and screen space, with order-preservation, invertibility and composition proved. Part of the Inkproof charting libraries; it knows about ordered fields and intervals, never about what the data measures.

## Supported versions

| Inkproof.Scale | Lean | Lasm (`@lasm/cli`) | Inkproof.Core |
| --- | --- | --- | --- |
| `main` | `leanprover/lean4:v4.35.0` | 0.3.5 | `v0.1.0` |
| `v0.1.0` | `leanprover/lean4:v4.35.0` | 0.3.5 | `v0.1.0` |

The library builds natively and under Lasm from the same source.

## Using it

```lean
require «inkproof-scale» from git "https://github.com/tentenths/inkproof-scale" @ "v0.1.0"
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

`Float` is not covered by the theorems: it is not a field (rounding breaks the field laws), though Lean models it as IEEE 754 binary64, so it is not opaque to proofs. Float scales run the same code, and the tests check that rounding keeps order and that round trips land within a relative `1e-12`. A check in the tests fails if any axiom beyond Lean's own and those in `Inkproof.Core.Axioms` creeps in. [DESIGN.md](DESIGN.md) describes the design, and `API.lock` lists every public declaration and theorem statement.

## Trusted computing base

The proofs cover the Lean source. These are trusted beneath them:

| Component | Why trusted | Mitigation |
| --- | --- | --- |
| Lean compiler and runtime | Compiles the proved source | Pinned in `lean-toolchain`; the same test program runs natively and under Lasm |
| Lasm compiler, runtime and Emscripten | Compiles Lean to Wasm | Pinned exactly in the test subproject; the same test program runs natively and under Lasm |

The library declares no axioms of its own; its float error theorems rely on Core's `float_rounding_model` axiom (FP-3). It has no generated code and no hand-written JavaScript.
