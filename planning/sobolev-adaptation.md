# Selected Sobolev foundation adaptation

Upstream: Alejandro Soto Franco, EllipticPDE@ec784093f30308ef770ff855ce624725adf6f870. Exact selected paths, upstream git blob hashes, local SHA256, license and version pins are in HitAndRun/External/EllipticPDE/PROVENANCE.json. Copyright and Apache-2.0 license retained.

Scope: actual weak derivative graph and H01 closure, plus bounded-domain H01 Poincare. Eight Lean modules only; no upstream Challenge/Solution, README claims, compiled caches, or full environment copied. No pre-existing EllipticPDE subtree was found in local Dikin production sources. Namespaces remain EllipticPdes for source traceability; module imports are relocated to HitAndRun.External.EllipticPDE. No mathematical statement changed.

Initial source scan found no sorry/axiom/unsafe/admit tokens. Compilation and transitive axiom evidence are pending, not implied by that scan.

## Ready queue

1. Compile only the selected GraphBounded dependency closure against the existing final Lean4.35/Mathlib pin, once the shared compilation lane is available. Repair only compatibility details; document each difference and keep original hypotheses/conclusions.
2. Add a concrete bounded-domain H01 consumer checking graph membership, approximation, and the Poincare inequality.
3. Build gradient-only norm equivalence/completeness and finite-coordinate vector-field/divergence bridge required by source S03/S09/S10. Ordinary H01 Poincare is not the source's centered Neumann CPI, and does not prove weighted IPI.

No target numbered result is completed by importing this foundation.

## Verified first integration

2026-10-21: selected8-module upstream closure compiled against final Lean4.35 without proof edits. New Consumer.lean and GradientSpace.lean also compiled successfully via `lake build HitAndRun.External.EllipticPDE.GradientSpace`; no final warnings. Consumer proves actual H01 completeness/weak membership, graph-norm bound and gradient injectivity. GradientSpace uses the closed range of the genuine gradient map, inherits the L2 Hilbert structure, proves completeness from bounded-domain Poincare, and identifies it linearly with H01 with exact gradient norm. The range cannot contain arbitrary non-gradient fields.

A separately imported audit file queried12 endpoints, including upstream weak characterization, H01 inclusion/density/Poincare and every new bridge theorem. All transitive reports contained only propext, Classical.choice and Quot.sound. Actual command `lake env lean /tmp/har-sobolev-audit.lean` exited0. This is narrow foundation evidence, not whole-paper completion or full-source statement equivalence.

Initial project-only syntax/elaboration repairs: beta-reduce injectivity hypothesis before rewriting, place omit before doccomment, open NNReal notation. Upstream mathematical code was not changed.

Next: genuine finite-dimensional vector-field divergence on PiLp2 of gradientSpace, sqrt(n) bound, then zero-mean range via H01 approximation. Until the latter is proved, the divergence is explicitly uncentered and is not yet the paper's map into Q=L2_0.

## Actual divergence and centered range verified

2026-10-21 07:25 UTC: Sobolev/Divergence.lean and Sobolev/ZeroMean.lean compiled successfully. VectorField is PiLp2 of actual gradientSpace components over EuclideanSpace real (Fin n); divergence is the concrete sum of coordinate weak derivative projections. Proved ||div u||²≤n||u||² and ||div u||≤sqrt(n)||u||. MeanCLM equals the actual integral. Compactly supported test derivatives integrate to zero by weak integration by parts with the constant function1; H01 closed-graph density transfers this to every component. centeredDivergence is then the actual CLM restricted into the kernel of integration, not an assumed centered map.

Two imported full-statement consumers (sqrt-dimension bound and actual integral-zero conclusion) compiled. Nine endpoint axiom checks all report only propext/Classical.choice/Quot.sound; driver/log are /tmp/har-divergence-audit.lean and .log. Fresh12 foundation checks also passed after the two project bridge files were converted to Lean's module/public-section format. That formatting change reduced project module compilation from23–32seconds to3–4seconds and did not alter mathematical statements. The only remaining warning is unused section parameters on meanCLM_eq_integral.

Finite restricted measure is explicit in ZeroMean; bounded Haar domains supply it by isFiniteMeasure_restrict and Bornology.IsBounded.measure_lt_top. SourceDuality/UniformMeasure integration belongs to the separate Hilbert worker. No numbered source result is independently counted complete here.

## Curl energy derivation (consumer verification in progress)

The four CurlEnergy modules compile as of 2026-10-21 07:35 UTC. Mixed directional derivatives commute on the actual smooth compact test space. Two integrations by parts give the mixed derivative pairing identity; applying the defining H01 closed-graph density twice extends it to genuine zero-trace weak Sobolev functions. Finite-dimensional Parseval supplies every coordinate's L2 gradient energy. A separate matrix identity sums only i<j and discharges its cross-pairing premise with that proved H01 identity. The source-facing divergence_curl_energy theorem has no cross-identity or PDE premise.

CurlEnergyResidual proves the actual mean-zero residual and its pairing with divergence from the genuine Riesz equation, corresponding to B.4(i)/(iii). B.4(ii), the distributional row-divergence identity for the antisymmetric tensor, is a separate pending implementation, not implied by the algebra file. Root/index_hit_run_paper owns that part. At07:37UTC, the separately imported /tmp/har-curl-audit.lean completed with actual exit0: three full statements and11transitive axiom reports, all only propext/Classical.choice/Quot.sound. The short normalized-uniform/literal-H01 wrapper remains in compilation; source-wide completion remains separate.

At07:42:50UTC CurlUniform and its separately imported full literal-H01/uniform-domain consumer passed, with two further standard-only transitive axiom reports. The source B.3 upper-triangle energy identity is now independently checked. Total this slice: four full consumer examples, thirteen axiom reports. B.4 remains partial pending its distributional identity and source assembly. Root subsequently owns a semantics-preserving module-format modernization; update hashes after that change.

## Published checkpoint

The current milestone accepts S03, S09, S10, S11 and S12: 5/13 named results (38.5%). Earlier pending statements above are historical development notes. S11 and S12 source review is recorded in planning/curl-residual-source-review.md; verification/module-modernization.json and verification/residual-identities.json provide the corresponding fresh evidence. S13 and the main spectral-gap/mixing theorems remain open.
