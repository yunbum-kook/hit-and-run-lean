# Spectral Gaps of Hit-and-Run and Coordinate Hit-and-Run

Work-in-progress Lean 4 formalization of [arXiv:2608.16878](https://arxiv.org/abs/2608.16878), by Yunbum Kook and Santosh S. Vempala.

## Status

9 of 13 named source results are verified (69.2%): Lemma 1.3 (attained divergence solver), Theorem 1.4 (exact Babuska–Aziz/improved-Poincare comparison), Proposition 2.1 (actual Hit-and-Run gap), Proposition 2.2 (actual coordinate Hit-and-Run gap), Lemma B.1 (duality), Lemma B.2 (Riesz field), Lemma B.3 (curl energy), Lemma B.4 (residual identities), and Lemma B.5 (rough weighted gradient estimate). The main geometry-dependent spectral-gap and mixing theorems remain open. See `planning/PROGRESS.json` and `verification/` for source-indexed status and actual consumer/axiom evidence. Helpers are not counted as source results.

Additional verified foundations include body-valued HAR and CHAR algorithms using actual uniform chords, the actual uniform sphere and its complete fourth-moment tensor, conditional-projection gap certificates, boundary-distance geometry, and smooth cutoff/distance-limit estimates. Both exact finite-CBA gap propositions are proved for the actual algorithms. Both chains additionally have native-law chi-square contraction, joint reversibility and exact integer accuracy budgets under finite CBA. The rough-data weighted estimate and exact CBA ≤ 1+4CIPI comparison are proved. The logarithmic geometric estimate, weighted-L1 geometric comparison, and main geometry-dependent rates remain open. Translation and convex-body/interior transport, actual centered-covariance radius and inner-ball bounds, median minimality, and the full ambient locally-Lipschitz class transfer are also verified. These are supporting bridges, not additional named source completions.

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

## Normalization and geometric bridges

Verified helpers now construct the actual centered-covariance inverse-square-root normalization, prove uniform pushforward and genuine weak-Sobolev Poincare transport, and establish finite ordinary CPI on every bounded open convex domain. Maximum inscribed radius attainment and arbitrary-center/body-boundary transport are proved. Weighted source-form inequalities remain explicitly conditional on a universal ordinary-L1 reverse-Buser input; these helpers do not close S07 or S08. Actual HAR/CHAR gap consequences of finite IPI are also verified. Named completion remains 9/13.
