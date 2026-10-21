# Independent sphere and actual-chord review

Reviewed 2026-10-21 08:19 UTC. Scope: source semantics plus inspection of existing compilation/consumer/axiom evidence; no compiler rerun by this reviewer. No source file was edited.

## Verdict

Pass for the limited foundations stated below. No extra named source result is completed by this review: the accepted source count remains 5/13. This is not a proof of stationarity, conditional-expectation identification, or the paper's HAR comparison proposition.

- `uniformSphere` is normalized Euclidean `volume.toSphere`, with nonzero finite normalization proved, not an arbitrary probability measure postulated to have desired moments. Orthogonal invariance is proved using the actual cone construction and Euclidean volume preservation.
- Coordinate covariance is exactly delta(i,j)/n. The reviewed fourth-moment results are exactly E(theta_i^4)=3/[n(n+2)] and E(theta_i^2 theta_j^2)=1/[n(n+2)] for i!=j. No isotropy or fourth-moment hypotheses are assumed. Integrability follows from compactness and continuity, so the integral identities do not exploit Lean's nonintegrable-integral default.
- Dimensions use `NeZero n`; denominators are proved nonzero. This validly includes n=1, whereas the main paper later assumes n>=2. The mixed theorem's distinct-index premise is impossible for n=1, as expected.
- Chords are the actual affine-line preimages of K under t -> x+t theta, normalized with one-dimensional Lebesgue measure and pushed forward. Unit theta makes this map an isometry. Open bounded K and x in K guarantee positive finite chord length. An explicit measurable pushforward formula is present.
- State and output carriers are the actual body subtype K; invalid outside-body states and zero directions are excluded in the kernels. The body restriction is justified by proved mass-one support, not a fallback branch.
- CHAR averages genuine coordinate chord kernels with inverse-cardinality weights. HAR composes an independent actual uniform-sphere direction with the actual chord step. The extra generality of bounded open nonconvex K yields uniform line intersections; on the source's convex bodies these are the intended chords.
- No pointwise Sobolev representative claims occur in these foundations. Later L2 conditional-expectation identities must still be a.e./equivalence-class statements.

## Source comparison and remaining gaps

Pinned `source/tex/main.tex`, SHA256 fdbcb45400d5abe4d390dff4bf9e9c2fe92c8e69a7ac431649aac1d21b8dae19: algorithm at lines 136-137; body assumptions at 372-375; sigma and conditional operators at 610-617; covariance/full fourth contraction at 644-650. The reviewed covariance and even moments agree exactly.

The full four-index tensor (including odd multiplicities) and general nonsymmetric-matrix contraction formula were NOT in the reviewed files. Newly appearing Tensor/Matrix/Hilbert files are drafts outside this review. Kernel stationarity, the identification of a fixed-direction chord kernel with the conditional expectation given orthogonal projection, reversibility/projection identities and source spectral-gap assembly remain separate obligations. No convex-chord-interval theorem or unoriented-line quotient equivalence was inspected; the implemented oriented-direction sampling directly matches the source's sphere formulation.

## Evidence inspected

- `verification/consumers/ActualAlgorithms.lean`: 3 full examples; `.local/algorithms-audit.log`: 7 transitive reports, each only propext, Classical.choice, Quot.sound. Log SHA256 d8fea28da953eb6907a21f0dce386c4af3249f6637e24a5e021d226d955d96f4.
- `HitAndRun/Geometry/SphereMomentsAudit.lean`: 4 full examples; `.local/sphere-moments-audit.log`: 7 transitive reports with the same allowed axioms. Log SHA256 0b73744a55b0d5c870dc3ee8ae10eb81f82829bd374d837451cd6bd97caad64b.
- Producer confirms sphere build session 17882 completed successfully at 08:15:10 UTC (2846 jobs), audit session 50544 exit 0 at 08:15:33 UTC, and the three sphere source hashes plus audit hash unchanged. Algorithms audit was run in session 6883 with its seven outputs observed 08:12:18 UTC. These execution claims are producer evidence, not independent compiler execution by this reviewer; plain logs themselves omit exit markers.
- `verification/chord-foundation.json` records exit-0 build and consumer with matching current ChordMeasure and ChordKernel hashes. Existing record's statement that HAR/CHAR averaging is not yet established is stale relative to the newly reviewed algorithm modules, not evidence against them.

## Reviewed source hashes

- `HitAndRun/Geometry/UniformSphere.lean`: `0fef0f4bcc5808f34e849606fe57a211f1603f9fd3a140baefb51d850a548ca1`
- `HitAndRun/Geometry/SphereMoments.lean`: `e3eec66e19d6a3b9c0cbd58167cff4d485b016a6f5170f91b29e182742692ec1`
- `HitAndRun/Geometry/SphereMomentsSecond.lean`: `dd809fd160ef8adfa6210ea3b7ef613e3ed42a7e748723f5285848aa13c66100`
- `HitAndRun/Geometry/SphereMomentsFourth.lean`: `b8962a601529bb965a654ce8e76ff4d17fd697f36b3729436770e0415e9d3bfe`
- `HitAndRun/Geometry/ChordMeasure.lean`: `a8499765129cf332472f9233fdb5a265239d514f7648d89c9752e84c6033c86a`
- `HitAndRun/Markov/ChordKernel.lean`: `cc7316dcbf23d67e05dc0261dd6cdfeb536d8a947134f68b6a29c8265360e11a`
- `HitAndRun/Markov/BodyChordKernel.lean`: `80f9a0eafc76d0e013c2062f83ddf23a70daf81f02725db3458f97ee5507d3eb`
- `HitAndRun/Markov/CoordinateKernel.lean`: `6054684dea91ee2a150d5b018f9dc4ff3163d9d2b22f90afa05785dae60fbe28`
- `HitAndRun/Markov/HitAndRunKernel.lean`: `a8bfdbc6d4b22ad40a669fe9dd0619b78449e1f676c3b33c91042087827b6408`
