# Spectral Gaps of Hit-and-Run and Coordinate Hit-and-Run

Work-in-progress Lean 4 formalization of [arXiv:2608.16878](https://arxiv.org/abs/2608.16878), by Yunbum Kook and Santosh S. Vempala.

## Status

11 of 13 named source results are verified (84.6%): Lemma 1.3, Theorem 1.4, Propositions 2.1–2.2, Theorem 3.1, Corollary 3.2 and Lemmas B.1–B.5. The main geometry-dependent spectral-gap and mixing results (S01/S02) remain open. The weighted inequalities now use an actually proved ordinary-L1 reverse-Buser input, not an assumed premise. See `planning/PROGRESS.json` and `verification/` for exact source-indexed evidence. Helpers are not counted as source results.

The rough estimate is proved for actual L2 distributional data, without a smoothness or global H1 assumption. Both algorithms use actual normalized chords, and HAR uses genuine uniform-sphere moments and proved measurable averaging. Further verified helper packets include native-law chi-square contraction, integer accuracy budgets, convex W12 smooth density and centered covariance geometry; these do not close the remaining source statements by themselves.

The workflow is: source-indexed planning → search existing formalizations → assess reuse and provenance → revise the dependency plan → implement disjoint proof slices → compile and audit → repeat discovery. The source index and reuse assessment live in `planning/`; the exact source version and checksums live in `source/`.

## Reproducible dependencies

- Lean: `leanprover/lean4:v4.35.0`
- Mathlib: `56a005855ea17e0b0958f73ec801ae140b0a1679`
- Transitive dependencies: pinned in `lake-manifest.json`

Use `lake build` with the pinned toolchain. Published verification records describe the focused module builds and importing consumers actually run; they do not claim a fresh full checkout build. Build caches and installed dependencies are not distributed in this repository. On the development machine, the already installed compatible Mathlib environment is shared to avoid duplicate storage; a fresh checkout uses the dependency pins instead of machine-specific paths.

## Acceptance criteria

Each completed paper statement must have a source-faithful statement review, actual successful consumer compilation, and a transitive axiom report using only standard Lean axioms. Hypotheses, constants, carriers, and conclusions are not silently weakened. Proposed constructions, scratch proofs, imported results, and accepted production proofs remain distinct. No `sorry`, `sorryAx`, or custom axioms may close a claimed result.

Reuse from the Dikin formalization and other repositories is assessed at exact commits, with licenses and provenance preserved. Source indexing, theorem counts, and helper counts are separate. Commits group meaningful mathematical or infrastructure milestones rather than routine activity.

## Repository scope

`HitAndRun/` contains formalization code; `source/` fixes the manuscript inputs; `planning/` records the dependency and reuse plan. Only compact final validation evidence belongs in the repository. Temporary build outputs, local coordination files, and recovery copies are ignored.

This repository is private. The archived manuscript is distributed under its existing [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/) license; see `source/MANIFEST.json` for attribution and exact source provenance. No new license grant for original Lean project code is made here. Third-party material, when incorporated, retains its original license and attribution.

## Private reused source

`CvxBody/` contains only the selected reverse-Buser dependency closure, with scoped upstream elaboration options. Its 29 authored modules are reused at the user’s direction from a private repository; no project-wide license or public redistribution grant is inferred. Do not make this repository public without resolving that scope. Existing separately licensed OAI/TauCeti notices are preserved. See `CvxBody/PRIVATE-REUSE.md` and `CvxBody/PROVENANCE.json`. The full KLS15 endpoint is not part of this checkpoint.
