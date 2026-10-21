# Licenses and provenance

This is a private formalization snapshot. It is **not cleared for public redistribution**. License files in a component apply to that component, not automatically to this entire project.

## Original project code

No project-wide public license is granted for `HitAndRun/`, `vendor/ProjectAdapters/`, or other original project contributions by this snapshot. Owner authorization to work in the private repository is not a public license. Existing author headers and the scoped third-party records below remain applicable.

## Private reverse-Buser dependency

The selected `CvxBody/` closure comes from `chewisinho/cvx_body_lean` at commit `41678c03373f8d3ac9d95bab31bcc17022d85bec`. It contains 45 Lean modules, including 29 authored modules for which no project-wide license was located. Reuse was authorized for this private project; public redistribution permission is not inferred.

Keep [PRIVATE-REUSE.md](../CvxBody/PRIVATE-REUSE.md), [PROVENANCE.json](../CvxBody/PROVENANCE.json), original headers, and the separately scoped [OAI](../CvxBody/External/OAI/README.md) and [TauCeti](../CvxBody/External/TauCeti/README.md) attribution. The shared external modules are used canonically, not duplicated.

## KLS15 adapted closure

`vendor/KLS15/` contains only the selected import closure. Its project code carries the retained [Apache-2.0 license](../vendor/KLS15/LICENSE); bundled components keep their own notices and licenses listed in [NOTICE](../vendor/KLS15/NOTICE).

The exact extraction is recorded at `chewisinho/cvx_body_lean@0e96a41441c2a3878dd0a4e5ea5dc5590eaf4fcf`; the retained backport metadata also pins the earlier `HongruZhao/KLS15@fe59199e9c039a79a436daa939f79662df2596da` source. [Production provenance](../vendor/KLS15/PRODUCTION-PROVENANCE.json) maps original blobs and SHA256s to adapted file bytes. [Port modifications](../vendor/KLS15/PORT-MODIFICATIONS.md) distinguish this project's Lean/Mathlib adaptation from upstream.

The KLS15 license does not license the separately authored private `CvxBody/` closure.

## Other imported code

- `HitAndRun/External/EllipticPDE/`: retained [license](../HitAndRun/External/EllipticPDE/LICENSE) and [provenance](../HitAndRun/External/EllipticPDE/PROVENANCE.json), including the separate [convolution](../HitAndRun/External/EllipticPDE/Convolution-PROVENANCE.json), [mollifier](../HitAndRun/External/EllipticPDE/Mollifier-PROVENANCE.json), and convolution-compatibility records.
- `HitAndRun/External/Dikin/`: retained [provenance](../HitAndRun/External/Dikin/PROVENANCE.json), [selected-contraction provenance](../HitAndRun/External/Dikin/Contraction-PROVENANCE.json), probability-median provenance, and scoped Markov-process license. Selected Dikin operator reuse does not imply a blanket public license for Dikin-derived project code.
- `docs/third-party/`: retained OpenAI Apache-2.0 and TauCeti license texts referenced by the canonical external modules.
- Mathlib and its transitive packages: exact revisions are in `lake-manifest.json`; their own licenses apply. Installed package trees and compiled caches are not distributed here.

## Manuscript

The fixed manuscript is *Spectral Gaps of Hit-and-Run and Coordinate Hit-and-Run*, Yunbum Kook and Santosh S. Vempala, arXiv:2608.16878v1, under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/). [The manifest](../source/MANIFEST.json) records source URLs, authors, version, and checksums. The manuscript bytes are unchanged. Its license does not determine the license for newly authored Lean proofs.

## Before any public release

1. Obtain explicit public-redistribution permission for every required privately authored component, especially the 29 `CvxBody/` modules, or replace it with an independently proved, appropriately licensed dependency.
2. Establish the intended public license and necessary rights for original project and reused Dikin-derived code.
3. Recheck retained third-party notices, modification records, source maps, and the exact import closure after any changes.
4. Complete and record the normal source rebuild and source-consumer checks for the exact release snapshot.
5. Separately authorize any repository-visibility change or public publication.

Private cleanup and source verification do not themselves satisfy this checklist.
