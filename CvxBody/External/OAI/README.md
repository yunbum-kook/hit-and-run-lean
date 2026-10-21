# Vendored: Prékopa–Leindler and log-concavity from `openai/math`

Source: https://github.com/openai/math, revision `1581d4cbdd69a0faf34b2089614fe2a814316a6a`
(2026-10-12), upstream path `lean/OAI/Analysis/KLS/`. Apache License 2.0, Copyright OpenAI
(copy in `docs/third-party/openai-math-Apache-2.0.txt`). Obtained through the sibling diffusion
project (`optimal_diffusion/lean/DiffusionLower/External/KLS/`, commit
`4ce41d06257e8faf73efc36360bd803b7f95d7d0`), which ported them from upstream with import-only changes
and the same Lean and Mathlib pins as this repository.

Vendored here: `Model`, `Convexity/LogConcavity`, `Convexity/PrekopaLeindler`,
`Convexity/Prekopa`, `Convexity/PrekopaReal`. Only module paths changed
(`DiffusionLower.External.KLS.*` to `CvxBody.External.OAI.KLS.*`); statements, proofs, declaration
names and the upstream namespace `OAI.LeanBlast.KLS` are untouched.

Main statements: `AsymptoticStatistics.prekopaLeindler` (n-dimensional Prékopa–Leindler, in
`ℝ≥0∞`), `LeanBlast.KLS.prekopaLeindler_space`, `prekopaLeindler_integral` (real form),
`lintegral_marginal_rpow_le` and `isLogConcaveFunction_marginal` (marginals of jointly
log-concave functions are log-concave).
