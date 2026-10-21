# Adapted KLS15 dependency

This directory is the selected KLS15 proof dependency for the Hit-and-Run formalization, not a standalone checkout of the upstream KLS15 project.

The retained endpoint is `KLS15.openaiKLS`, with the explicit Poincaré constant 15. Its production consumer is [KLS15Endpoint.lean](../../verification/consumers/KLS15Endpoint.lean). Paper-facing uniform-measure, covariance, and Sobolev adapters are in [ProjectAdapters](../ProjectAdapters/), not additional hypotheses of the vendor theorem.

## Exact source scope

- Extraction: `chewisinho/cvx_body_lean@0e96a41441c2a3878dd0a4e5ea5dc5590eaf4fcf`.
- 1,654 Lean modules in this directory; three shared external modules remain at their canonical `CvxBody/External/` paths.
- The root Lake configuration registers the original module names without renaming theorem namespaces.
- Production pins: Lean `4.35.0` and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.
- Original and adapted per-file hashes: [PRODUCTION-PROVENANCE.json](PRODUCTION-PROVENANCE.json).
- Adaptation details: [PORT-MODIFICATIONS.md](PORT-MODIFICATIONS.md).

All vendored Lean modules are transitively required by the current `HitAndRun` umbrella. Do not remove a file merely because the manuscript does not cite that helper directly.

## Verification scope

The adapted closure passed its isolated production-pin checks. Ordinary registered Lake importing consumers also passed using exact hash-verified artifacts, and the endpoint transitive axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`. These facts do **not** establish a completed clean normal source rebuild of this entire repository. The current project-level record is [verification/main-source-complete.json](../../verification/main-source-complete.json).

Build from the repository root with `lake build HitAndRun`; see the [project verification instructions](../../verification/README.md). Do not apply historical upstream build claims or toolchain settings to this adapted integration.

## Licensing and historical records

Keep [LICENSE](LICENSE), [NOTICE](NOTICE), all referenced component licenses, author headers, and modification records. The original upstream README is preserved byte-for-byte as [UPSTREAM-README.md](UPSTREAM-README.md) solely as historical source documentation; its build claims and relative links refer to the upstream repository, not this integration. The historical backport manifests and patch similarly describe earlier source states; current file identity is governed by `PRODUCTION-PROVENANCE.json` and the current project verification receipts.

These licensed sources do not grant a public license for the separately authored private reverse-Buser code in `CvxBody/`. See the [project distribution scope](../../docs/LICENSES.md).
