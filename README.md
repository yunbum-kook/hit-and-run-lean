# Spectral Gaps of Hit-and-Run and Coordinate Hit-and-Run

Lean 4 formalization of the 13 named results in [Yunbum Kook and Santosh S. Vempala, arXiv:2608.16878v1](https://arxiv.org/abs/2608.16878v1).

## Status

All **13/13 named source results** have source-faithfulness reviews, successful importing consumers, and transitive axiom checks using only `propext`, `Classical.choice`, and `Quot.sound`. This includes the spectral-gap bounds and native-law mixing corollary for both algorithms. Helper lemmas are not counted as paper results.

**Separate build gate:** the final integration was checked through ordinary `lake env lean` imports using hash-verified compiled artifacts. A full normal Lake source rebuild has not yet been certified. The result is therefore source-complete within the stated scope, not an assertion that every release gate has passed. See [verification](verification/README.md).

**Private distribution only:** part of the reverse-Buser proof depends on privately reused code without a public redistribution grant. This repository is not cleared for a public release. See [licenses and provenance](docs/LICENSES.md).

## Build and check

Required pins:

- Lean: `leanprover/lean4:v4.35.0`, fixed by [lean-toolchain](lean-toolchain).
- Mathlib: `56a005855ea17e0b0958f73ec801ae140b0a1679`.
- All transitive revisions: [lake-manifest.json](lake-manifest.json).

From the repository root, with Elan installed:

```sh
lake build HitAndRun

env -u LEAN_PATH lake env lean \
  -DautoImplicit=false -DmaxSynthPendingDepth=3 \
  verification/consumers/MainSourceComplete.lean
```

The first command is the normal source build. The second checks full main-theorem and mixing signatures and prints their transitive axioms; it does not replace the source build. No machine-specific dependency path or distributed `.olean` files are required. Do not run `lake update` or change the manifest when reproducing this snapshot. [Verification instructions](verification/README.md) cover the other source results.

Use `import HitAndRun` for the project library. The final main declarations are `HitAndRun.Markov.mainSource_complete`, `mixingSource_complete`, `mixingSource_HAR_accuracy_complete`, and `mixingSource_CHAR_accuracy_complete`.

## Mathematical scope

The proofs use the actual normalized-chord HAR/CHAR kernels, uniform-sphere or coordinate averaging, uniform convex-body measure, weak Sobolev spaces, and rough distributional data. The main bounds retain an arbitrary inscribed-unit-ball center, actual covariance and optimal Poincaré constants, and dimension-independent universal constants. The external KLS bound is proved code, not an assumed Poincaré conclusion.

For Corollary 1.2, exponential contraction allows arbitrary initial probability laws, with extended-real chi-square. A finite iteration budget requires finite initial chi-square and positive accuracy. It is zero when the initial error is already small enough; otherwise it is the natural-number ceiling of a positive logarithmic expression. No negative iteration count or finite-time guarantee for infinite initial chi-square is claimed.

See the [source-to-Lean map and edge conventions](docs/SOURCE_MAP.md) for all 13 statements. The manuscript is fixed at v1; [source/MANIFEST.json](source/MANIFEST.json) records attribution and original-byte checksums.

## Layout

- `HitAndRun.lean`, `HitAndRun/`: project library and mathematical proofs.
- `vendor/ProjectAdapters/`: paper-facing adapters, registered under their existing Lean module names.
- `vendor/KLS15/`: the exact adapted, separately licensed KLS15 import closure.
- `CvxBody/`: the required private reverse-Buser closure and separately licensed external components.
- `source/`: immutable manuscript files and checksums.
- `docs/`: source correspondence and distribution scope.
- `verification/`: compact compilation receipts and reproducible importing consumers.

Build products, temporary experiments, local working records, and recovery snapshots are excluded from the release tree. Component licenses and notices retain their original scope; no new project-wide code license is granted here.
