# Source-indexed formalization plan

## Pinned source and scope

Target: *Spectral Gaps of Hit-and-Run and Coordinate Hit-and-Run*, Yunbum Kook and Santosh S. Vempala, arXiv:2608.16878v1. On 2026-10-21 the official abstract page listed only v1, submitted 2026-08-17 17:57:11 UTC. The PDF has 15 pages and its title-page date is August 18, 2026. Source and PDF bytes are pinned in `source/MANIFEST.json`; no source edits were made. The arXiv license link identifies CC BY 4.0. This is source attribution, not a license choice for new Lean code.

Main TeX SHA256: `fdbcb45400d5abe4d390dff4bf9e9c2fe92c8e69a7ac431649aac1d21b8dae19`.

There are **13 numbered proof-bearing source results**: 3 theorems, 2 corollaries, 2 propositions, 6 lemmas. All 13 are initially unproved in this project. Definitions, displayed identities, cited background, and helper lemmas are essential dependencies but do not add to this denominator. Each numbered result may receive several implementation tasks; partial tasks do not count as completion of that result. Initial baseline is retained here; the verified checkpoint below supersedes it.

## Verified checkpoint: 2026-10-21 08:43 UTC

**6/13 named source results accepted (46.2%): S03 / Lemma 1.3, S06 / Proposition 2.2,
S09 / Lemma B.1, S10 / Lemma B.2, S11 / Lemma B.3, S12 / Lemma B.4.** This is a named-statement fraction, not a difficulty-weighted estimate. The other seven remain open.

S06 proves the exact finite-CBA bound 1/(n*CBA) for the actual coordinate Hit-and-Run kernel. The body-valued normalized-chord finite mixture is identified almost everywhere with the conditional-projection operator through a proved surjective L2 isometry. Product-section disintegration, chord integrability, representative independence and integral-form stationarity are proved, not assumed. The gap is the literal nonempty Rayleigh infimum. Evidence: `verification/coordinate-kernel-complete.json` (three full imported examples, twelve standard-only transitive reports); independent source review: `planning/coordinate-source-review.md`.

The other five accepted results use actual zero-trace Sobolev gradient fields and centered L2 for uniform probability, with original source constants. Their evidence remains in `verification/uniform-source.json`, `verification/residual-identities.json`; actual curl validation is also retained in `planning/curl-verification.json`. S11/S12 first landed at `48c6b1abf4233b35b6cf198fefb7996f51a1dd02`. The algorithm and sphere foundation milestone landed at `64047f674756c0473ae85d47da339334848435e4`.

Domain hypotheses are bounded/open/nonempty and positive dimension; omitting convexity proves stronger intermediate results. Source n>=2 cases are covered. No helper or draft adds to this denominator. HAR comparison, the rough weighted residual estimate, main gap bounds and mixing corollary remain open.

Line references below are to the unmodified `source/tex/main.tex`.

## Common carriers and conventions

- Real Euclidean dimension `n`; main theorem explicitly `n ≥ 2`.
- Bounded open convex domain `K`, with an inscribed unit ball for the main results. Uniform probability `π = volume.restrict K / volume K`; prove positive finite volume from geometry rather than assume a different measure.
- `L²₀(π)` is the centered real L² subspace. Sobolev `H¹(K)` uses actual weak partial derivatives; `H¹₀(K)` is the H¹ closure of compactly supported smooth functions. Vector fields use the sum of all coordinate derivative squares.
- `δ(x) = dist(x, ∂K)`; distance to the boundary, not an arbitrary positive weight.
- `CPI` and `CIPI` are least constants for inequalities over actual H¹ test functions (lines 433–441); do not replace them by opaque parameters without a proved bridge.
- `CBA` is the supremum over nonzero centered f of the infimum of gradient energy over zero-trace divergence solutions (lines 537–545). Empty feasible sets need an extended-real infinity convention, not real `sInf ∅ = 0`.
- HAR chooses a uniform sphere direction and uniform point on the chord; CHAR chooses a coordinate uniformly and averages the corresponding chord. Actual measurable probability kernels and their L² actions must be linked to conditional expectations.
- Spectral gap is the infimum of Dirichlet-form/variance quotients over nonzero centered functions (lines 454–460), not a bare lower-bound predicate presented as the gap.
- The proof uses genuine (non-lazy) positive-semidefinite kernels, since they are averages of orthogonal conditional projections. Do not import a lazy Dikin chain endpoint and silently change the algorithm.

## Numbered-result ledger

### S01 — Theorem 1.1, Spectral gaps
- Label `thm:main`; statement lines 371–379, proof 586–597.
- n≥2; K bounded, open, convex, containing a unit ball; π uniform.
- Universal dimension-independent positive constants give λHR ≳ 1/(n² CPI) ≳ 1/(n² ‖cov π‖op log n), and λCHAR ≳ 1/(n³ CPI) ≳ 1/(n³ ‖cov π‖op log n).
- Both CPI and covariance/log endpoints belong to the result. Finishing only the CPI branch is meaningful partial progress, not the whole theorem.
- Dependencies: S04, S05, S06, S08; CPI≥‖cov‖op; inscribed-ball covariance lower bound ≳1/n; logarithmic KLS/Poincaré upper bound CPI≲‖cov‖op log n (Klartag 2023).

### S02 — Corollary 1.2, Mixing time
- Label `cor:mixing-har-char`; lines 381–397, proof 600–603.
- Same geometry, actual iterate laws from π₀. A single universal c>0 gives χ²(πNHR‖π)≤exp(−cN/(n²‖cov‖op log n))χ²(π₀‖π), with n³ for CHAR.
- Also ε-accuracy iteration upper bounds with the corresponding factor times log(χ²(π₀‖π)/ε).
- Dependencies: S01, actual-kernel positive semidefiniteness, spectral-gap-to-χ² formula (line 464), integer-time/log budget arithmetic.
- Source edge case: displayed time expression is negative when 0<M<ε and undefined at M=0; the rigorous integer budget requires a zero-step branch and a positive-part/ceiling convention. Record explicitly; do not change the original bytes. Finite-M theorem and extended-real M=∞ vacuity must be distinguished.

### S03 — Lemma 1.3, Attained divergence solver
- Label `lem:known-divergence`; lines 547–569.
- Assuming CBA(π)<∞, every centered f∈L² has u∈H¹₀(K;Rⁿ), div u=f and ‖∇u‖²≤CBA‖f‖².
- Dependencies: boundedness ‖div u‖≤√n‖∇u‖; zero mean of divergence; H¹₀ Poincaré equivalence of gradient norm and Sobolev norm; completeness; closed nonempty affine fibers; Hilbert nearest-point theorem; nonzero f inf/sup and separate f=0.
- Finiteness is not itself a Lean witness unless the actual extended infimum feasibility and attainment arguments are implemented.

### S04 — Theorem 1.4, Babuška–Aziz versus improved Poincaré
- Label `thm:BA_to_IPI`; lines 576–579, proof 1042–1059.
- For bounded convex domain in Rⁿ, CBA≤1+4 CIPI. Exact additive 1 and coefficient 4 must remain.
- Dependencies: S09–S13 and actual definitions. Infinite-CIPI case is trivial only under correct extended-real conventions; finite branch supplies finiteness of CBA.

### S05 — Proposition 2.1, HAR comparison
- Label `prop:HR-comparison`; lines 621–678.
- If CBA<∞, λHR≥(n+2)/(n(2+CBA)) ≳1/(1+CBA).
- Dependencies: S03; sphere second/fourth moments; chord-average annihilation of directional derivative of zero-trace fields; Fubini/Bochner measurability; dual Cauchy–Schwarz; symmetric-gradient identity.
- Certificate gθ(x)=n θᵀ∇u(x)θ, exact sphere probability measure. Fourth moment uses sym M for arbitrary matrices; replacing M by a symmetric-only matrix assumption weakens the proof.

### S06 — Proposition 2.2, CHAR comparison
- Label `prop:CHAR-comparison`; lines 683–707.
- If CBA<∞, λCHAR≥1/(n CBA).
- Dependencies: S03; coordinate chord annihilation; finite-product duality. Certificate gi=n∂iui and norm nΣ‖∂iui‖²≤n‖∇u‖².
- Preserve 1/n normalization and actual coordinate kernel, not an arbitrary family of projections without transport proof.

### S07 — Theorem 3.1, Weighted L¹ improved Poincaré
- Label `thm:l1-ipi`; lines 727–734, proof 771–798.
- Any locally Lipschitz f:Rⁿ→R; convex body K containing a radius-r ball; infz∫K|f−z|dx ≲ (n√CPI/r)∫K δ|∇f|dx, universal constant.
- Positive r and nonempty interior are implicit in “ball of radius r”; use n≥1 for this standalone claim, not unnecessary n≥2 unless documenting scope.
- Dependencies: translate ball center to 0; α=1−1/(2n); fundamental theorem on radial lines; volume change under dilation; gauge/inner-parallel geometry δ(y)≥r(1−gaugeK y); α^(−n)≤2; radius/diameter estimate from covariance; L¹/L² Poincaré equivalence for logconcave measures; scaling CPI(αK)=α²CPI(K).
- Source cites KLS95 Theorem4.1 for isotropic diameter. The origin is an inball center, not necessarily barycenter: the bound supK|x| must use diameter/center containment, not falsely identify these centers.

### S08 — Corollary 3.2, Improved Poincaré bound
- Label `cor:ipi-pi`; lines 737–767.
- Convex body with maximum inscribed radius r: CIPI≲n² CPI/r².
- Dependencies: S07; existence/optimality of medians for L¹ minimization; positive/negative parts and chain rule; median-zero square trick; Cauchy–Schwarz; smooth restriction density in H¹ on convex domain; bounded δ to pass weighted gradient energies to the limit.
- Need preserve maximum-inscribed-radius endpoint, not only any chosen smaller r (although a stronger any-inscribed-ball theorem is useful).

### S09 — Lemma B.1, Duality
- Label `lem:dual_BA`; lines 918–926, explanatory argument 928–932 (no separate proof block).
- For C>0, equivalence of uniformly bounded right-inverse witnesses for div:V→Q and ‖f‖²≤C(supv≠0 ⟨f,div v⟩/‖∇v‖)² for all f∈Q.
- V=H¹₀ with gradient Hilbert norm; Q=L²₀. Can first prove abstract bounded-linear Hilbert operator theorem, then instantiate actual divergence.
- Reverse implication needs closed-range/surjectivity/adjoint lower-bound argument; mere Cauchy–Schwarz proves only forward implication.

### S10 — Lemma B.2, Riesz vector field
- Label `lem:Riesz`; lines 936–955.
- Every f∈Q has unique u∈V with ⟨f,div v⟩Q=⟨u,v⟩V all v, and ‖∇u‖ equals the displayed nonzero-v supremum.
- Dependencies: Riesz representation, bounded divergence. Handle u=0 separately: source “setting v=u” is not allowed in nonzero-v supremum when u=0.

### S11 — Lemma B.3, Divergence/curl energy identity
- Label `lem:dual_matrix`; lines 960–977.
- For u∈V, Gij=∂jui−∂iuj, ‖G‖²=∫Σi<jGij², prove ‖∇u‖²=‖div u‖²+‖G‖².
- Dependencies: compact-smooth IBP twice, commuting classical derivatives, H¹₀ approximation, finite-sum matrix identity. Preserve upper-triangle norm; full Frobenius norm introduces factor2.

### S12 — Lemma B.4, Residual identities
- Label `lem:identities`; lines 981–1005.
- u from S10 and G from S11, h=f−div u: (i) ∫h=0, (ii) ∇h=div G distributionally, (iii) ⟨h,div u⟩=‖G‖².
- Dependencies: S10/S11, zero integral divergence, weak PDE Δu=∇f, distributional derivative commutation. f initially only L²; do not assert classical second derivatives of u or classical gradient of f/h without regularity proof.

### S13 — Lemma B.5, Weighted gradient estimate
- Label `lem:poincare_bound`; lines 1010–1039.
- Centered L² h and antisymmetric L² matrix field G with ∇h=div G (distributional interpretation), prove ‖δ∇h‖₂≤2‖G‖. Consequently finite CIPI gives ‖h‖²≤4 CIPI‖G‖².
- Dependencies: rigorous regularization preserving distributional PDE; weighted zero-boundary IBP; distance is 1-Lipschitz; Hessian-symmetric/skew-matrix cancellation; exterior-product identity; Cauchy–Schwarz; extension of IPI to the resulting weighted Sobolev class.
- **Highest-risk bridge:** original h is merely L², while CIPI was defined for H¹. Weighted gradient finiteness does not by itself give unweighted H¹. Must prove approximation/extension, not add H¹ to the theorem and call it source-complete. Source “standard regularization” compresses a substantive analytic argument.

## Required unnumbered/background obligations (not extra source-result credits)

H01. Weak derivative uniqueness, closure under L² limits, completeness of H¹; actual H¹₀ density and gradient norm equivalence.
H02. Uniform convex-body measure, mean-zero subspace, covariance norm; 0<volume K<∞.
H03. Conditional expectation as orthogonal projection, self-adjoint/idempotent, residual-energy identity.
H04. Measurable chord kernels, conditional-expectation identification, stationarity, reversibility, PSD for HAR/CHAR, actual iterate law transport.
H05. Centered positive self-adjoint Markov spectral gap → operator power contraction → χ² of measure iterates. Dikin is a reuse candidate, not yet certified applicable.
H06. Sphere probability, Eθθᵀ=I/n and fourth-coordinate moments; directional certificates measurable in θ and x.
H07. Zero chord integral of smooth directional derivatives and extension to H¹₀; keep all “a.e.” and conditional-expectation quotient issues explicit.
H08. Symmetric-gradient identity 2‖sym∇u‖²=‖∇u‖²+‖div u‖² (same IBP foundation as S11).
H09. Hilbert dual-certificate coercivity lemma; finite coordinate version and sphere-integral version.
H10. Convex gauge, inscribed-ball boundary-distance estimates, radial change of variables and differentiability a.e.
H11. L¹↔L² Poincaré comparison for logconcave measures (not arbitrary measures); covariance/diameter estimates, scaling and translation.
H12. Median truncations, Lipschitz chain rule and density passage for weighted energies.
H13. Klartag logarithmic KLS bound and inscribed-ball covariance lower bound. Literature citations alone are NOT Lean proofs.
H14. Weighted distributional regularization and passage to boundary; Lagrange/exterior-product finite-sum identity.
H15. Zero/infinite initial χ², integer N and ε≥M branch, explicit universal-constant quantifier order.

## Dependency DAG and parallel implementation plan, iteration 0

- Functional-analysis lane: H01/H02 → actual V,Q,div → S10 and S09 → S03.
- PDE lane: H01/H08 → S11 → S12; H14 → S13; S09+S10+S11+S12+S13 → S04.
- Geometry lane: H10+H11 → S07; H12+S07 → S08.
- Markov lane: H03/H04/H06/H07/H09+S03 → S05/S06; Dikin reuse assessment for H05.
- Assembly: S04+S05+S06+S08+H13 → S01; S01+H05+H15 → S02.

Start with disjoint abstract Hilbert duality and finite-matrix algebra while discovery assesses actual Sobolev/convex/conditional-expectation implementations. Prefer CHAR before HAR because finite averaging avoids initial sphere/Bochner integration burden. Preserve enough interface generality that both use the same divergence solver and weighted-boundary proof. Do not let easy abstract wrappers hide undischarged actual-domain premises.

Next discovery pass should search exact theorem-level APIs in pinned Mathlib, Dikin, convex-body Lean repositories, Sobolev/PDE repositories, and the existing sampling repository. For each reused declaration record repo, immutable commit, source path, license, precise statement, compatibility pin, imported closure, and compiled consumer. Then revise this plan rather than accumulating parallel incompatible carrier definitions.

## Source-fidelity issues to decide/prove, not silently patch

1. Main n≥2 handles log n positivity; preserve it. Separate standalone n≥1 geometry results if needed.
2. Infinite constants and empty feasible-set conventions must reflect mathematical infima, especially CBA and spectral gaps.
3. S02 time budget needs explicit M≤ε/zero branch and finite/infinite M distinction.
4. Uniform probability versus unnormalized volume factors must cancel consistently between L², V, and Q.
5. Appendix B's smooth manipulations must be extended to source weak regularity, particularly S13.
6. The theorem's covariance-log branch depends on a deep external theorem. If no verified formalization exists, report it as an open dependency; do not introduce an axiom, assumed bound, or omit branch without approval.
7. Proof universality: constants cannot secretly depend on K,n,r,f,π₀. Dimension/radius appear only in the printed rates.
8. No assumption-only module, `sorry`, custom axiom or README assertion counts as any of the 13 completions. Require source-faithful actual consumer compilation plus standard-only transitive axiom audit.
