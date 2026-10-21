# Quarantined KLS15 reuse candidate

Read-only source review on 2026-10-21. Candidate: `chewisinho/cvx_body_lean` commit `0e96a41441c2a3878dd0a4e5ea5dc5590eaf4fcf`. No candidate code imported, compiled, or accepted as a proved dependency in this project.

## What was checked

The endpoint `KLS15.poincare15_mem` delegates through `ActualKLS15VerifiedEndpoints` to `KLS149963.poincare149963_mem`. It genuinely states a dimension-free constant 15 for isotropic log-concave probability measures. `KLS/Definitions.lean` uses probability, compact-set measure log-concavity and actual coordinate mean/covariance isotropy, actual gradient energy and `ProbabilityTheory.evariance`. No Poincare conclusion is hidden in `admissibleMeasure` in the inspected definition.

`CvxBody/Analysis/KLSPoincare.lean` transfers this to actual centered covariance by whitening, with explicit full affine support. The wrapper is not a direct proof of the paper's Klartag logarithmic bound.

The endpoint discharges regularization's `hregular` and the regular-law theorem's `hcoupled`/`hthree` using `PaperRegularApproximation`, `ActualWeightedAppellInductionSub15`, `ActualSymmetricCubicSeed245Cap`, and the graded operator endgame. Inspected files contain no `sorry` or declared custom axioms. This statement is NOT a scan or audit of the entire import closure.

## Unresolved verification gates

1. Independently compile the exact endpoint closure and inspect transitive axioms; source-level `#print axioms` commands are not evidence of their output. Upstream documentation reports 1,654 modules / 10,586 build jobs; those reported builds were not reproduced here.
2. Review the global law/test maximizer and compactness bridge (`ActualWeightedAppellMaximizer`), polynomial projection, regularization transfer, and graded-gradient geometry. These carry the substantive mathematics, not the short endpoint wrapper.
3. Resolve upstream Lean 4.34.1 / Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` against this project's unchanged Lean 4.35.0 / Mathlib pins.
4. Vendored KLS15 has an Apache-2.0 LICENSE. No root LICENSE was visible in CvxBody's repository tree; do not infer a license for its separately authored wrappers.

The provenance JSON identifies upstream `HongruZhao/KLS15` commit `fe59199e9c039a79a436daa939f79662df2596da`. Its blob-verification claims remain third-party evidence, not an independent verification performed here.

## Decision

Quarantine the full KLS15 endpoint. Keep the paper-faithful plan and 0/13 source-result count unchanged. Smaller moment/whitening components are potential future reuse, subject to their own source/closure/license checks. Finding no obvious issue in selected files does not establish correctness of the whole theorem; its unusually strong conclusion alone does not establish an error either.
