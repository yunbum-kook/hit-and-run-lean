# S07 / S08 weighted Poincare lane

Source: pinned arXiv:2608.16878v1, source/tex/main.tex, Theorem 3.1 and Corollary 3.2. This plan changes neither the manuscript nor the completion denominator. No source result in this lane is complete.

## Reduced implementation plan

1. Reuse actual boundary-distance contraction from Geometry/BoundaryDistance. Prove gauge slack times inradius is at most actual distance to frontier by approximating the gauge infimum, avoiding false attainment in an open body. Identify exact open radial sections x in tK iff gauge(x) < t. Prove the paper's contraction alpha = 1 - 1/(2n) has alpha^(-n) at most 2 using Mathlib Bernoulli.
2. Prove the radial FTC integral estimate, Haar dilation change of variables, and Tonelli rearrangement. Keep real finrank, positivity, integrability, and actual gradient explicit. The gauge identifies radial sublevel membership; it is not a freely chosen weight.
3. Supply the actual diameter/covariance bound for a convex body's uniform measure and covariance lower bound for its actual ordinary Poincare constant.
4. Supply continuous L2-to-L1 Poincare comparison for logconcave uniform measures and its scaling. This is a substantial missing mathematical theorem, not a hypothesis permitted at the S07 endpoint. Assemble the two terms of source Theorem 3.1 only after both prerequisites are established.
5. For S08: median minimizes the L1 distance; square the positive and negative median parts, apply S07 and Cauchy-Schwarz, add energies, and use variance minimization. Then extend from smooth restrictions to actual H1 via convex-domain density and bounded boundary distance. H01 density is insufficient here.

## Exact reusable APIs inspected

- Mathlib/Analysis/Convex/Gauge.lean: exists_lt_of_gauge_lt, gauge_nonneg, gauge_le_one_of_mem, interior_subset_gauge_lt_one, setOfPred_gauge_lt_one_eq_self_of_isOpen, gauge_smul_of_nonneg, gauge_le_one_iff_mem_closure. The open-body argument should use approximation rather than asserting x/gauge(x) belongs to K.
- Mathlib/Algebra/Order/Ring/Pow.lean: one_add_mul_le_pow, valid for real a >= -2. Apply a = -1/(2n).
- Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean: Measure.setIntegral_comp_smul_of_pos and integral_comp_smul_of_nonneg. These already provide the exact finrank Jacobian; no custom change-of-variables axiom is needed.
- DikinD2/Probability/ProbabilityMedian.lean: exists_probability_median for measurable functions on probability spaces, including atoms. This proves existence, not median L1 optimality or continuous L1/L2 comparison.
- DikinD2/Markov/Centering.lean and Poincare.lean: discrete/kernel cut-to-energy inequalities. These are not the required reverse L2-to-L1 logconcave continuous theorem.

## Status

Geometry/WeightedPoincareGeometry.lean has four verified helper results. On 2026-10-21 at 08:16 UTC, focused Lake builds of this module and WeightedPoincareChecks.lean succeeded. Four explicit full-statement consumer examples compiled; all four transitive axiom reports contain only propext, Classical.choice, and Quot.sound. No external source copied; all APIs above are existing pinned dependencies or local production modules. No S07/S08 completion claimed. The source endpoint must not hide diameter/covariance, logconcave L1/L2 equivalence, radial integration, or H1 density in new assumptions.

## Renewed targeted discovery

The publisher provided exact-blob-checked CvxBody source at commit 0e96a41441c2a3878dd0a4e5ea5dc5590eaf4fcf. `CvxBody/Analysis/LogConcaveGeometry.lean`, `norm_sub_le_of_levelSet`, proves an actual radius bound `(80/3) exp(c/2) n sqrt(lambda)` from integrable logconcave density, positive mass, a global density upper bound, a level-set condition, and directional second-moment bounds. Uniform convex-body indicators with c=0 fit the intended mathematical route. It is a candidate only: independent compilation, transitive audit, indicator/carrier bridges, and wrapper licensing are unresolved. No code has been copied into production.

`CvxBody/Analysis/Cheeger.lean` and `MilmanPoincare.lean` provide the opposite implication (Cheeger/concentration to L2 Poincare), not the needed continuous reverse Buser comparison. A targeted search of the staged KLS15 source found Cheeger references in definition/target files; target propositions without inhabitants are not proofs. Reverse L2-to-L1 remains open after this discovery pass.

## S08 next bridge and density scope

`WeightedPoincareMedian.lean` now proves the sign-preserving square t|t| rather than separately summing positive/negative parts. It preserves strict-tail median conditions, has derivative 2|t| even at zero, and gives the same constant 4A^2 after integrated Cauchy-Schwarz absorption. Its conditional endpoint assumes a genuinely generic weighted L1 inequality and explicit L2 membership, and does not assert that the source body satisfies that inequality.

For the H1 extension the actual carrier is `EllipticPdes.H1Graph.W12`, defined through all weak derivative identities. Existing `H01` approximation only treats zero boundary trace and cannot establish S08. Planned route: translate an interior ball to zero, pull a W12 function back by an inward dilation to obtain a weakly differentiable function on a neighborhood of the original body, then mollify at radius below the geometric margin. Prove convergence of both function and weak-gradient L2 components as dilation tends to identity and mollifier radius tends to zero. Do not assume a C1 boundary for convex bodies. PDE lane owns general interior weak-derivative convolution; this lane should reuse it and supply dilation/density assembly. The external GlobalApproximation C1-boundary result is not directly admissible.

Median bridge verification (2026-10-21 08:32 UTC): both WeightedPoincareMedian and WeightedPoincareMedianChecks built successfully. Three full-statement consumers compiled; six transitive axiom reports use only propext, Classical.choice, Quot.sound. The generic weighted-L1 to variance endpoint includes actual Frechet differential norms, median preservation, derivative on the zero set, and explicit L2 integrability. S07/S08 remain open.

The PDE lane additionally selected and verified pinned EllipticPDE Embedding/Convolution, which supplies actual Lp mollifier convergence for 1 <= p < infinity without boundary regularity. This replaces the mollification-convergence portion of the density plan, not the missing weak-derivative dilation bridge or H1 density conclusion.

Dilation checkpoint (2026-10-21 08:46 UTC): actual global-L2 vector-valued strong dilation convergence on finite restricted sets is compiled, with one full-statement consumer and five standard-only transitive axiom reports. The proof uses compact continuous approximation and the exact Haar Jacobian, not almost-everywhere pointwise convergence of arbitrary L2 representatives. Appended actual-domain zero-extension wrappers are still pending their next compiler pass. PDE owns weak derivative transport and SmoothGraph construction; this lane owns dilation convergence, avoiding duplication.

Prior verified Density source SHA256 (before adding convex import/domain wrappers): a58248ab4bdda9fb31a4a46d7508d7870f2477a297bf784c65548e35692e4ccf. Current modified source SHA256 5a4dbf5292b1f0bd0294527acd05e0a08565cd4a985a7d7ff9f7156799b1efc0 is UNVERIFIED until its next compiler pass; the previous receipt does not certify these new bytes.

Proposed smooth approximation simplification: convolve the zero extension first and evaluate the resulting smooth function at the inward point lambda*x. The existing uniform contraction ball margin allows translated-bump weak identities at that point; ordinary chain rule adds lambda. This avoids rough weak-derivative pullback before convolution. WeightedPoincareMedianApproximation.lean drafts the actual L2 diagonal lemma (global L2 convolution convergence plus positive dilation parameters tending to one implies restricted L2 convergence after composition). This new module and appended actual-domain wrappers are UNVERIFIED pending the next compile pass. It does not solve the general non-convex-domain B5 extension.

Updated verification (2026-10-21 09:02 UTC): the current actual-domain wrappers and approximation-then-dilation diagonal theorem now compile. Three full-statement consumer examples and eight transitive axiom reports pass with only propext, Classical.choice, and Quot.sound. This supersedes the pending/unverified notes above for these exact bytes:
- WeightedPoincareMedianDensity.lean: 5a4dbf5292b1f0bd0294527acd05e0a08565cd4a985a7d7ff9f7156799b1efc0
- WeightedPoincareMedianDensityChecks.lean: aa727cfffc98c433d2e5c52618d85674d67b06c216f101bdcf591591d52528cb
- WeightedPoincareMedianApproximation.lean: c4e2def0b3517f7360b217466013aab57d3fbf082b18a45a69c90620f6fc42d9
- WeightedPoincareMedianApproximationChecks.lean: a8b749fdfbdfeff99bd9e6bf3383ad8e4f927070f647df2d335a8bafed9ff68f
Successful Lake traces are under .lake/build/lib/lean/HitAndRun/Geometry with the corresponding module names. These remain analytic helpers, not source S07/S08 completion.

Renewed reverse-Buser discovery identified a viable source-only needle decomposition -> Cheeger -> median-L1 route in CvxBody, independent of the KLS15 closure. However, 29 original CvxBody-authored files in the 45-module closure have no located license or reuse permission. No copying, compilation, or publication of that closure is authorized by this discovery. The radius bridge shares this unresolved license issue. Continue independent density construction while this external reuse question is unresolved.

Convex H1 density milestone (2026-10-21 09:16 UTC): `exists_smooth_W12_approximation` is now compiled with a full imported consumer and standard-only transitive audit. It constructs global smooth functions whose restrictions converge to both actual components of every `W12` element on a finite-volume open convex set containing a positive-radius ball at zero. The sequence is explicit: a_k = 1 - 1/(2(k+1)), mollifier radius r/(4(k+1)). Zero extension is used only before convolution; translated compact test identities prove the true interior gradient, and no derivative is asserted across the boundary. No C1 regularity or H01 substitution is used. The graph-norm wrapper remains pending its consumer checkpoint.

Verified modules and checks from this milestone:
- WeightedPoincareMedianMollifier.lean: 41fbd7841768f58ab87bfa38e58a4aa074958590d6a1f61708e85df101d07f1d
- WeightedPoincareMedianMollifierChecks.lean: 16773df6b4328252dbc5adc985681318b1a03b481b0f3cdae0b884b9ae80c580
- WeightedPoincareMedianSmooth.lean: 2e2980296c85bb8467b59f0fa50e2ce21331e23161e21ee1fbe91cfa95432b13
- WeightedPoincareMedianSmoothChecks.lean: fea8cc0835507d04f132f3c4e9d6625b3a560586af35514521b0bfd78a9d3faf
- WeightedPoincareMedianH1Density.lean: a863622aeaa963e2ed5ecb421f9fa7d6ee5623f3cdf60bc2d6d54438ced65936
- WeightedPoincareMedianH1DensityChecks.lean: 5c41bce1bafba3d70277229e208840c3ff6900a10c9cac59d1c439f03ec34ce7
There are three full imported consumers and fourteen standard-only reports across these three pairs. All logs are corresponding Lake traces. Reused selected Apache-2 EllipticPDE convolution and the PDE lane's verified scalar weak-derivative convolution. No CvxBody code copied. S07/S08 remain open because density and the conditional median square bridge do not establish the body's weighted L1 bound, radial integral estimate, radius comparison or reverse Buser inequality.

Graph-norm density verified (2026-10-21 09:18:55 UTC): `exists_smoothGraph_tendsto_W12` constructs global smooth restrictions converging to each actual W12 element in the genuine H1Graph norm. The bounded open convex domain has an inner ball at zero; no C1 boundary is assumed. Full imported consumer and three transitive standard-only reports passed. This closes the convex H1 density dependency, not source S07/S08. Exact frozen hashes:
- HitAndRun/Geometry/WeightedPoincareMedianGraphDensity.lean: 48dc18c213f00ebce8bf525890953fc9315dfad092fbc44877ff4a570c3f6cf6
- HitAndRun/Geometry/WeightedPoincareMedianGraphDensityChecks.lean: e632f2433a25fc152f2f90f8bea627af8d4406a99bdd2a4457921efeee1cd249
Evidence: .lake/build/lib/lean/HitAndRun/Geometry/WeightedPoincareMedianGraphDensity.trace and WeightedPoincareMedianGraphDensityChecks.trace. All four new source/consumer pairs have four full consumers and seventeen standard-only reports. No compilation job is left running by this lane.

Radial analytic substep verified (2026-10-21 09:33 UTC): `integral_radial_difference_le_boundary` proves the actual C1 first-term error bound R a^(-n)/r times the actual boundary-distance weighted gradient integral. Boundedness and continuity discharge every integrability condition. The proof uses radial FTC, actual gauge residence Fubini, exact Haar Jacobian, and actual infDist-to-frontier geometry. Three full consumers and twelve standard-only transitive reports passed. This is not complete S07: the reverse Buser estimate and radius/CPI bridge remain separate dependencies; the complete locally Lipschitz source class is also not claimed from this C1 substep. Frozen files:
- WeightedPoincareRadial: d44ecfc3c9e13b113d345d593b52b5b9598814bc39e05fb7382b9ba9cca503c7
- WeightedPoincareResidence: 8f029a9410a72fae3e2e21c67c0a8cff22415d475729cc68640715537a2c9c3a
- WeightedPoincareRadialTransport: 27df352a34a185d46204df4b2f83d180c9d833421cf7f62c3da78ed23d862f7b
- WeightedPoincareRadialChecks: ad29b743bf2943baa99a63a40ac5233232379de56bc928abd0e9ac06a8baf9f6
- WeightedPoincareRadialBound: 907464e8775e9f5744923279eaf19c2d8d60a8eddbcffaa5a93c10df4d3dc6c0
- WeightedPoincareRadialBoundChecks: 54ab95dfaac0ab3d4cac3307fac6d5ca1ad223f16cf484a37570a6b365c3ab1a
Evidence is in corresponding Lake build traces. No unlicensed CvxBody code is used.

Conditional radial assembly verified (2026-10-21 09:36 UTC): `exists_weighted_center_of_ordinaryL1` combines both actual radial terms. Given an explicitly ordinary C1 L1 inequality with coefficient B and a genuine radius bound R, it produces a weighted center with coefficient R a^(-n)/r + B a a^(-n)/((1-a)r). The ordinary L1 inequality is NOT asserted from CPI, logconcavity or a worker claim. All analytic integrability is discharged. One full imported consumer and two standard-only transitive reports passed. Frozen hashes:
- WeightedPoincareInterior: 65bb40721e28dc9edbc5a5d3703948ad07c573daebb9995e350ce250d8e80ba6
- WeightedPoincareAssembly: b9c208ca0eabad88300e17474d4b108c7370e742423d699daee7dd4df71cdac8
- WeightedPoincareAssemblyChecks: 6b53f2901845b9fa0f81d6995aab7f6642b0b19d41edc55b2f994c944c6a4c45
The median-minimality interface is owned by the transfer worker. S07/S08 are still not counted complete by this conditional assembly.

Numeric coefficient verified (2026-10-21 09:38 UTC): at alpha=1-1/(2n), the assembly coefficient is at most (2R+4nB)/r. Full consumer and standard-only axiom report passed. Frozen hashes: WeightedPoincareCoefficient d7e9ce0f2e8ad5e39647ba230fcf12b7b87b4c4727034bb644450e8f3d1bdb59; WeightedPoincareCoefficientChecks ceb79ccf33285b2e5cea7e5c3105e15dbebcd655d20e1c48de5c4972ce7b5f55. The independent covariance lane has separately reported actual radius R=6n sqrt(CPI), hence the C1 assembly becomes (12n sqrt(CPI)+4nB)/r once that module is imported. No reverse Buser statement is inferred.

Full S07 class extension remains open. Exact Mathlib entry points located: LocallyLipschitzOn.exists_lipschitzOnWith_of_compact in Topology/Algebra/MetricSpace/Lipschitz.lean, and LipschitzWith.ae_differentiableAt / LipschitzOnWith.ae_differentiableWithinAt_of_mem in Analysis/Calculus/Rademacher.lean. A source-faithful extension can use compact-neighborhood Lipschitz control, smoothing, and convergence of actual gradients, but no ready weak-gradient integration-by-parts constructor was found in the selected EllipticPDE Sobolev files. Do not replace the source locally-Lipschitz class by C1 while claiming S07 complete. The existing C1 route is sufficient for the separately proved conditional H1/IPI transfer.

Source class audit (2026-10-21 09:49 UTC): Theorem 3.1 explicitly quantifies ambient locally Lipschitz f: R^n -> R, not merely functions locally Lipschitz on the open body. Therefore compact-neighborhood Lipschitz control derives bounded derivative and finite Lp norms on the bounded body; no new integrability assumption is needed. The actual weak-gradient identity was reused from Mathlib's LipschitzWith.integral_lineDeriv_mul_eq, Rademacher, and LipschitzOnWith.extend_real near each compact test. A genuine W12 graph with actual f and gradient f representatives is now verified. Two full consumers and six standard-only reports passed. Frozen files:
- WeightedPoincareLocallyLipschitz: cc9eee073d42bac1a4cf9259827ed5028dd65b88f330b1c7e0fd986199ea8c1c
- WeightedPoincareLipschitzWeak: 402d1b701b627debaab0f6c313d02961e9c8b19a5152b77f9b6acbcc37e87f5f
- WeightedPoincareLipschitzGraph: 903d46cbff94e7ab4b0d6f706bbc4c0df2dffe3d1e0b845911b5a34034369390
- WeightedPoincareLipschitzChecks: 68d74129db0f828aaa4d8683df0e5d897e5d603f0684d18a31394b88353d0516
Evidence: corresponding Lake traces. L1 limit transfer and final median-minimality combination remain pending; these verified foundations alone do not complete the S07 class extension.

Full ambient locally-Lipschitz class transfer verified (2026-10-21 09:58 UTC): `locallyLipschitz_exists_center_bound_of_smooth` derives the same-constant weighted L1 center bound for every ambient locally-Lipschitz function from the smooth center bound on a bounded open convex domain with an inner ball at zero. There are no extra integrability or median hypotheses. Genuine W12 density, bounded boundary-distance multiplication, L2-to-L1 convergence, and the independently verified median-minimality theorem discharge them. One full imported consumer and four transitive standard-only reports passed. No radial frozen file was edited. Frozen hashes:
- WeightedPoincareLipschitzLimit: 7653ff142f256feae45d25521b841f56e2d4f712a9d4bba2cb73cc9864300e57
- WeightedPoincareLipschitzExtension: 6fb0b7fdbfc8e6563f4fefd83e7c3080060305653e08ceb14861c9180059bb75
- WeightedPoincareLipschitzExtensionChecks: aebf23e3b018e90e12b1709bdb34e2a8715c2ab6b8573f290710b526070d05a7
Evidence: corresponding Lake traces and /tmp/weighted-extension-build.log, /tmp/weighted-extension-audit.log. This closes the locally-Lipschitz class extension in the current normalized open-body framework, not S07 itself. The actual reverse-Buser ordinary L1 estimate remains missing. Final source wrappers must also account explicitly for arbitrary inner-ball center, Lebesgue rather than normalized measure, and convex-body boundary conventions; these are not silently counted as completed here.

Convex-body interior transport verified (2026-10-21 10:03:51 UTC): Mathlib's licensed `Convex.addHaar_frontier` yields body/interior a.e. equality and exact restricted Haar, Lebesgue, normalized-ambient and uniform-measure equality. For nonempty interior, convex closure-interior equality gives equal frontiers, hence boundary distances equal everywhere. `bodyInteriorDomain` constructs the actual bounded open interior without assuming the original body open. All admissible open-ball radii at arbitrary centers, and their supremum, are preserved. For a closed body, positive-radius closed-ball containment is equivalent to open-ball containment; no maximum-radius attainment is assumed. Three full imported consumers and seven standard-only transitive reports passed. Exact frozen hashes:
- ConvexBodyInterior: 89f793288349e6aefa702de6c4bddc6be11b320d138872ef7c0bfad0bf015332
- ConvexBodyInteriorDomain: 1d0987cc9e9ddb91c92858ca5be4785a3722e78d1c2201da2963bbd57b9cfdea
- ConvexBodyInteriorRadii: dc858dc9d423ba3b04fbb77244c6af4e640c4837d9510ec2a9ab4e2152e09821
- ConvexBodyInteriorChecks: 36c98ac65ee658c7c853ab362e123b6ec5f6e627fafb0bd6ceaa5749c1fc92d9
Evidence: corresponding Lake traces and /tmp/convex-body-interior.log, /tmp/convex-body-domain.log, /tmp/convex-body-audit.log. Translation/PI invariance belongs to the separate translation lane. These wrappers do not prove reverse Buser or complete S07/S08.
