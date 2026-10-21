# S07 reverse Poincare comparison: reuse assessment

Status (2026-10-21): source-only research, not a compiled dependency or a proof of S07. No private source was copied into production. The candidate is independent of the quarantined KLS15 endpoint.

## Required mathematical input

Source `source/tex/main.tex`, Theorem 3.1, needs the dimension-free continuous L2-to-L1 comparison for the uniform measure of a convex body. For an actual valid ordinary Poincare bound P > 0, the desired unweighted median inequality has coefficient at most a universal constant times sqrt(P). Its dilation to alpha K supplies the second term of the weighted inequality. Discrete kernel Cheeger inequalities do not supply this input.

## Candidate interfaces, not validated reuse

Authorized connected repository `chewisinho/cvx_body_lean` is private. Inspected commit: `0e96a41441c2a3878dd0a4e5ea5dc5590eaf4fcf`.

- `CvxBody/Analysis/MilmanPoincare.lean`, `CvxBody.needle_decomposition_exists`: a measurable logconcave density on Euclidean space, whose density measure is a probability measure with finite first moment, admits a guided needle decomposition for each measurable set of mass strictly between zero and one. No Cheeger or Poincare inequality is assumed.
- `CvxBody/Analysis/NeedleDecomposition.lean`, `CvxBody.cheeger_of_needle_decomposition`: a genuine guided decomposition, an integrable guide, positive s, and guide mean absolute deviation at most s imply outer-Minkowski Cheeger bound 1/(256 s). The decomposition records actual probability-kernel disintegration, logconcave line densities, a 1-Lipschitz guide, and mass balance, not the desired Cheeger conclusion.
- `CvxBody/Analysis/Cheeger.lean`, `CvxBody.cheeger_l1`: for an absolutely continuous probability measure satisfying the measurable-set Cheeger bound, a nonnegative globally Lipschitz function supported on a set of measure at most one half satisfies the corresponding L1 gradient inequality.

Thus the final concentration-to-L2 theorem in MilmanPoincare is not the useful endpoint, but its intermediate needle theorem supplies a potential reverse route. This corrects the earlier inference that the entire module only helps in the opposite direction.

## Smallest implementation plan if reuse is permitted and validated

1. Prove the normalized convex-body indicator is the actual project uniform measure and is measurable/logconcave, with finite first and second moments.
2. Restrict the 1-Lipschitz guide to the actual project W12 carrier, identify its weak gradient with its almost-everywhere derivative, and prove gradient norm at most one. Apply the actual Poincare bound and Cauchy-Schwarz to obtain mean absolute deviation at most sqrt(P).
3. Compose the two needle interfaces, handling measurable sets of mass zero or one separately. Apply the L1 endpoint to the positive and negative median parts.
4. Localize ambient locally Lipschitz test functions near the compact body closure to match the global-Lipschitz interface. Supply the existing Haar dilation and boundary-distance bridges for alpha K.
5. If the project's Poincare constant is an infimum, use admissible P above it and pass to the limit unless attainment is already proved. Do not silently replace the actual H1 constant by an unrelated predicate.

No covariance bound, smooth boundary, or assumed needle existence should be introduced into the S07 endpoint. The first radial term and the S08 H1-density extension remain separate obligations.

## Dependency footprint and validation limits

Recursive source import inspection from MilmanPoincare resolves 45 non-Mathlib modules totaling 639,613 UTF-8 bytes: 29 CvxBody-authored modules and 16 externally attributed modules. No vendor/KLS15 module is in this closure. The proof chain includes Lipschitz maximization, mass balance, ray disintegration, Alexandrov/ray-Hessian geometry, logconcave needles, one-dimensional isoperimetry, and coarea. No unresolved imports or source occurrences of proof placeholders, added axioms, unsafe proof mechanisms, or native_decide were found by the bounded scan. This is not compilation, a transitive kernel axiom audit, or a full semantic audit.

The candidate's pins are Lean 4.34.1 and mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`; this project remains on Lean 4.35 and mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. No builds, dependency installation, or pin changes were attempted in this discovery pass.

## Permission required before selecting code

No license was located for the 29 private CvxBody-authored dependency files; fetching root LICENSE at the inspected commit returned 404. Accordingly these files cannot count as an authorized redistributable dependency. Connected read access does not grant publication or redistribution rights. Do not vendor or publish their source while this remains unresolved.

Narrow request to the owner: permission to reuse, adapt to the project's Lean/mathlib pins, and redistribute with the project's source only the 29 CvxBody-authored files in the pinned MilmanPoincare import closure, preserving the owner's requested attribution and license notices. This does not require permission for the entire repository or its unrelated KLS15 development.

An even smaller owner-supplied alternative would be a separately licensed, independently buildable theorem package proving the measurable-set Cheeger bound 1/(256 sqrt(P)) directly from a valid ordinary Poincare bound for a bounded full-dimensional logconcave probability density, together with its actual dependency closure. Pair that with a licensed Cheeger-to-median-L1 package, or ask for the combined median L1 inequality. A theorem statement alone or an unproved decomposition assumption is insufficient. The owner must license every required authored dependency, not just the endpoint file.

## Separately licensed upstream support

- [TauCetiProject/TauCeti, commit bab6e39bcc08efc89140619387bfe20d3c8797e1](https://github.com/TauCetiProject/TauCeti/tree/bab6e39bcc08efc89140619387bfe20d3c8797e1): [Apache-2.0 license verified at the pin](https://github.com/TauCetiProject/TauCeti/blob/bab6e39bcc08efc89140619387bfe20d3c8797e1/LICENSE). Fourteen attributed modules in the inspected closure support Alexandrov, convex differentiability/subgradients, second-order expansion, equal-dimensional Sard, and measure-theoretic infrastructure. Prefer upstream source and preserve notices; port compatibility still requires validation.
- [openai/math, commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a](https://github.com/openai/math/tree/1581d4cbdd69a0faf34b2089614fe2a814316a6a): [Apache-2.0 license verified at the pin](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/LICENSE). The two attributed modules are `lean/OAI/Analysis/KLS/Model.lean` and `lean/OAI/Analysis/KLS/Convexity/LogConcavity.lean`. They provide model/logconcavity infrastructure, not the reverse comparison theorem.

These upstream licenses do not license the 29 separately authored CvxBody files. No independently verified standalone reverse-Buser endpoint was located in the bounded public search or pinned mathlib inspection; this is not a claim that no such formalization exists.

### Additional permission check (2026-10-21 09:20 UTC)

The coordinator checked the complete, non-truncated repository tree at the pinned commit, the full README, and the first 30 lines of each of the 29 CvxBody-authored dependency files. No per-file license/SPDX grant or project-wide reuse grant was located. License paths in the tree cover named third-party/vendor components, not the authored needle closure. This strengthens the bounded missing-permission finding; it does not claim that no separate permission could exist. No private source code was copied into this project during the check.

### Renewed metadata/license check (2026-10-21 13:25 UTC)

Connected GitHub reads verified current `main` at `41678c03373f8d3ac9d95bab31bcc17022d85bec` (commit time 2026-10-21 05:15:51 UTC), tree `f23f0a25149bc97b162d6b18870ad7c798df7a3f`. Repository metadata still reports private visibility and `license: null`. The complete recursive tree was non-truncated (4,518 entries). No root/project license, copying, or permission file was found. Among paths matching license, notice, copying, permission, provenance, or README, only the root README changed relative to the earlier inspected pin; its complete current text contains no authored-code reuse grant. Current external-component READMEs and the KLS15 NOTICE preserve their component-specific scopes, not a grant for the authored needle closure.

All 29 authored closure files have exactly the same Git blob identities as the earlier read-only inspection recorded in `/tmp/reverse-buser-source-inspection.json`; therefore the earlier per-file header check remains applicable to those exact bytes. No newly verified reuse/adaptation/redistribution grant covering those files was found. This is an unresolved missing grant, not an author denial or a claim that separate permission cannot exist. No proof bodies were copied, no author contacted, and no project source pin, visibility or permission changed in this renewed check.

### Later user direction and private integration (2026-10-21 15:53 UTC)

The user subsequently explicitly directed reuse of Sinho’s code. The selected closure is now integrated privately under that direction, with original notices preserved and no invented license. The earlier missing-grant observations remain accurate as public-redistribution limitations, not a denial and not a claim that the user never authorized private reuse. Normal production-Lake and full source-form consumers now pass; S07/S08 acceptance is recorded in verification/reverse-buser-source.json. No public visibility change is authorized or made here.
