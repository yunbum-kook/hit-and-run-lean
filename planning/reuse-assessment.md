# Reuse assessment — 2026-10-21

Status: source inspection and planning, not a compilation or axiom certificate. Refer to source-index.md for the fixed 13-result denominator and exact manuscript. No inherited lemma counts as a completed new source result. Existing Mathlib pin is 56a005855ea17e0b0958f73ec801ae140b0a1679, Lean 4.35.0; do not upgrade to match a candidate dependency.

## Decisions

1. Reuse selected Dikin native probability/L2 infrastructure, not its whole repository or build environment.
2. Use Mathlib conditional expectation as the projection foundation. HAR/CHAR are non-lazy PSD chains. Do not replace them by the half-lazy Dikin algorithm.
3. Adapt the small EllipticPDE weak-derivative/H01 graph closure first. Its actual Sobolev carriers are substantially closer to the paper than an assumed PDE interface.
4. Keep weighted boundary-distance Poincare, Babuška–Aziz, chord identification and sphere moments as explicit outstanding proofs. Searching did not establish that no external proof exists.
5. Search again at each concrete blocker. Prefer exact small declarations and their transitive closure; do not vendor a large project just because its README advertises the desired result.

## Dikin source map

Reference remote revision: [c5f8471b62573fc0417bfafeb16c2b5be2637ff1](https://github.com/yunbum-kook/dikin-d2/tree/c5f8471b62573fc0417bfafeb16c2b5be2637ff1). Local production source was inspected; before copying record individual bytes against that revision. Private owner-authorized reuse is not a blanket public license.

| Source/API | Intended new use | Remaining obligation |
|---|---|---|
| DikinD2/Markov/KernelLpLift.lean: MarkovProcess.kernelLpFinite, coeFn_kernelLpFinite, norm_kernelLpFinite_apply_le | Native L2 action of an invariant kernel | Actual HAR/CHAR kernel construction, invariance and projection identification |
| Markov/NativeOperator.lean: DikinD2.NativeL2.operator, operator_ae, operator_contract, inner_operator, operator_selfAdjoint, meanZero_invariant | Reversible action on actual Lp and centered subspace | Correct uniform measure and reversible kernel |
| Markov/InvariantContraction.lean: LazyL2Contraction.iterate_sq_le_exp_on_submodule | Positive operator + invariant subspace + gap implies exp(-2 lambda N) squared-norm decay | PSD and exact spectral gap; despite namespace, this generic theorem does not require half-laziness |
| Probability/ChiSquareDensity.lean: density_representation, finite_iff_ac_memLp, finite_density_package, chiSquare_eq_centered_norm_sq | Actual extended-real chi-square, finite-density conversion | Match paper law/normalization; handle infinite input separately |
| Markov/NativeChiSquareDecay.lean: lawOrbit, densityOrbit, lawOrbit_density, centered_densityOrbit | Actual iterate law bridge for Corollary1.2 | Extract/adapt probability orbit portion without importing the conductance endpoint unnecessarily |
| Markov/NativeDecay.lean and final chiSquare_lawOrbit_le_exp | Proof pattern only | These final declarations assume half-laziness/cut conductance; not the correct HAR/CHAR theorem |

KernelLpLift's source is [Scott Armstrong/MarkovProcess@666cda029098a1106914fc9fa7abd1727573284a](https://github.com/scottnarmstrong/MarkovProcess/tree/666cda029098a1106914fc9fa7abd1727573284a), Apache-2.0, Copyright2026 Scott Armstrong. Dikin retains licenses/MarkovProcess/PROVENANCE.md, exact upstream files and adaptation patches; retain relevant notices with reuse. Other Dikin matrix/Gaussian/SC-barrier modules are not presently needed.

## Exact pinned Mathlib APIs

Paths below are under Mathlib at the pinned revision above, Apache-2.0.

| File / declaration | Source target | Scope |
|---|---|---|
| MeasureTheory/Function/ConditionalExpectation/CondexpL2.lean: condExpL2, norm_condExpL2_le_one, inner_condExpL2_left_eq_right, inner_condExpL2_eq_inner_fun | projection identity preceding S05/S06 | Actual L2 orthogonal conditional projection. Output is lpMeas subtype; include it back into ambient L2 explicitly |
| Analysis/InnerProductSpace/Projection/Minimal.lean: exists_norm_eq_iInf_of_complete_convex | S03/Lemma1.3 | Nearest point in closed affine divergence fiber; first establish gradient-Hilbert completeness and nonempty fiber from finite extended CBA |
| Analysis/InnerProductSpace/Dual.lean: InnerProductSpace.toDual, toDual_apply_apply, toDual_symm_apply | S10/LemmaB.2 | Riesz representation; instantiate genuine gradient-Hilbert domain, not an opaque certificate |
| Analysis/InnerProductSpace/Adjoint.lean | S09/LemmaB.1 | Adjoint API; reverse implication still requires closed-range/surjectivity proof |
| Analysis/Distribution/Distribution.lean and calculus integration-by-parts APIs | S11–S13 | Distributional framework; no automatic zero-trace vector Sobolev identities or weighted boundary approximation |

The pinned tree has SobolevInequality.lean and Distribution/Sobolev.lean, but their existence does not supply the exact bounded-domain H01/weighted IPI needed here. Searches for sphere-integral and fourth-moment APIs did not locate the exact arbitrary-matrix identity required by S05; continue targeted discovery before implementing it.

## EllipticPDE selected candidate

Authoritative repository: [alejandro-soto-franco/EllipticPDE@ec784093f30308ef770ff855ce624725adf6f870](https://github.com/alejandro-soto-franco/EllipticPDE/tree/ec784093f30308ef770ff855ce624725adf6f870). Source headers and LICENSE identify Alejandro Soto Franco, Apache-2.0. Upstream Lean4.35.0-rc3, Mathlib c55e6e786f49471c72fbddbec5415808896aec1e; adaptation to our final4.35 pin remains to be compiled.

Inspected actual source, not merely README:

- lean/EllipticPdes/Sobolev/WeakDeriv.lean: HasWeakLineDerivOn, HasWeakFDerivOn, test-function integral characterization, uniqueness a.e., linearity, classical-to-weak derivative, zero-extension support theorem. Imports Analysis/SmoothCutoff plus Mathlib.
- lean/EllipticPdes/Sobolev/Graph.lean: H1Graph is the actual L2 function×gradient product; W12 is the closed weak-derivative graph; H01 is closure of smooth compact-supported test graphs. Relevant APIs: fnL, gradL, testGraphₗ, mem_W12_iff_hasWeakFDerivOn, H01_le_W12, exists_seq_testGraphₗ_tendsto. Graph blob6ab94ead57cc33d6a7288e36e127a5116c1523d1; WeakDeriv blob6237fb588668a9187d7d6fa0406e55338e1125dc.
- lean/EllipticPdes/Poincare/GraphBounded.lean: poincare_H01_of_bounded proves existence of C≥0 with ||fnL U||²≤C||gradL U||² for U in H01, finite-dimensional nontrivial real inner-product E, additive Haar measure and bounded domain. This is enough for norm-equivalence infrastructure, not the paper's centered Neumann CPI or improved CIPI. It imports Poincare/Slab and Sobolev/Graph.
- lean/EllipticPdes/Form/HnegGraph.lean: hneg_characterization genuinely represents H01 dual by f0−divF and a least product norm. Useful reference but optional; it uses the full H1 graph norm, not automatically the gradient-only norm of AppendixB.

Import only the chosen closure and retain license/provenance and local changes. Upstream Challenge.lean is described as containing sorry and is not the default library target: exclude challenge/demo files, but still audit every selected transitive declaration. No independent successful consumer compilation or transitive axiom audit has yet occurred in this project.

## Other discovery and rejected shortcuts

- Scott Armstrong's CoarseGraining and DeGiorgi have weak derivatives and domain-specific Poincare machinery. Their precise declarations/licenses were not audited here; do not add as dependencies merely on search hits. EllipticPDE is the narrower first candidate.
- Gaussian Sobolev/Poincare projects (lean-stat-learning-theory, ginibre-poincare) do not directly prove uniform-convex-domain boundary-weighted IPI.
- Verified reference [chewisinho/cvx_body_lean@0e96a41441c2a3878dd0a4e5ea5dc5590eaf4fcf](https://github.com/chewisinho/cvx_body_lean/tree/0e96a41441c2a3878dd0a4e5ea5dc5590eaf4fcf): CvxBody/Analysis/KLSPoincare.lean has isPoincareBound_covariance_of_logConcave with actual covariance and a claimed stronger dimension-free factor15. It imports a very large vendor/KLS15 closure. This is inspected source, NOT independent validation of that stronger theorem. Root LICENSE retrieval did not yield a usable license; per-file/provenance licensing and complete axiom/semantic dependency review remain required before copying. Do not treat this as Klartag's logarithmic bound already proved. MilmanPoincare.lean similarly has a substantial needle-decomposition closure, not a one-file reusable theorem.

## Target-to-gap map

- S01: S04–S08 plus covariance lower bound, convex support/full dimensionality, and externally cited logarithmic KLS bound. The covariance endpoint is not complete if only CPI endpoint is proved.
- S02: substantial Dikin native probability reuse; new PSD gap bridge and actual HAR/CHAR law interface, plus zero-step/ceiling edge cases.
- S03: Mathlib minimizer plus EllipticPDE H01, new gradient norm/divergence and extended-infimum feasibility.
- S04: depends on S09–S13; no direct external exact theorem verified.
- S05: conditional projection infrastructure plus new sphere probability/moments, measurable chord family, zero-trace annihilation, dual certificate.
- S06: finite conditional projection family, zero-trace coordinate annihilation, norm estimate. Implement finite CHAR before continuous HAR to expose reusable interfaces.
- S07/S08: genuinely new boundary-distance convex geometry and weighted Poincare proof, median/positive-part chain rule and smooth H1 density; ordinary H01 Poincare is not a substitute.
- S09/S10: generic Hilbert duality/Riesz with concrete Sobolev instantiation.
- S11/S12: smooth IBP finite-coordinate identity, extend via H01 density, then distributional residual identity. Never assert classical second derivatives of an L2 datum.
- S13: hardest local analytic step: weighted cutoff/regularization preserving distributional equation and exact upper-triangle skew norm, Lipschitz boundary distance, limiting argument. Formalizing only the smooth calculation does not complete LemmaB.5.

## Disjoint implementation queues

Each worker keeps at least two ready tasks; completed target IDs, not helper count, determine source progress.

1. Hilbert worker: generic Riesz/supremum API → bounded-right-inverse/adjoint duality. Own abstract Hilbert files only.
2. Sobolev worker: selected WeakDeriv/Graph closure port → bounded-domain H01 Poincare consumer → gradient-norm completion/coordinate-divergence bridge. Own External/EllipticPDE and Sobolev bridge files only.
3. Kernel worker: Dikin PSD chi-square bridge extraction → finite projection-average CHAR abstract certificate → actual coordinate chord identification. Own kernel/probability files.
4. Geometry worker when available: boundary-distance and dilation lemmas → sphere second/fourth moments or weighted-IPI prerequisites, with module ownership assigned before work.

Use meaningful bundled commits after a compilable unit; record selected-source hashes and adaptation changes. Validate edited module plus affected consumer closure incrementally. Do not repeatedly rebuild unrelated dependencies. At integration/release, perform complete source-faithful statement review, fresh successful consumers, and transitive standard-only axiom audit. Semantic hypotheses and actual-carrier bridges are not optional even when compile succeeds.

## Prior skills attribution

The prior skills are **Scott Armstrong**, not Scott Morrison: [LeanAutoformalizationSkills@05a07311f16bc581729e52f3e73647b95fa9bef1](https://github.com/scottnarmstrong/LeanAutoformalizationSkills/tree/05a07311f16bc581729e52f3e73647b95fa9bef1). Local Dikin docs/SKILLS_SETUP.md, vendored README and upstream LICENSE were checked. Collection CC BY4.0, Copyright2026 Scott Armstrong; preserve third-party MIT/Apache notices. These are workflow resources, not Lean theorem dependencies. Apply locally without bundling all workflow/temp files into the eventual scientific release. No upstream installer or helper script was executed during this assessment.
