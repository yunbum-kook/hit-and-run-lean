# Source-to-Lean map

## Fixed scope

This formalization covers all **13 named proof-bearing results** of *Spectral Gaps of Hit-and-Run and Coordinate Hit-and-Run*, Yunbum Kook and Santosh S. Vempala, [arXiv:2608.16878v1](https://arxiv.org/abs/2608.16878v1): three theorems, two corollaries, two propositions, and six lemmas. Definitions, cited background results, analytic foundations, and helper lemmas support this scope but do not inflate the count.

The original manuscript bytes are unchanged. All line ranges below refer to [source/tex/main.tex](../source/tex/main.tex), SHA256 `fdbcb45400d5abe4d390dff4bf9e9c2fe92c8e69a7ac431649aac1d21b8dae19`. [The source manifest](../source/MANIFEST.json) supplies complete attribution and checksums.

The accepted statements have actual importing-consumer checks and standard-only transitive axiom reports. The final integration used exact compiled-artifact reuse; the separate full normal source rebuild has not yet been certified. See [verification](../verification/README.md).

Machine-readable ledger: [verification/source-results.json](../verification/source-results.json). Semantic reviews: [verification/source-reviews/](../verification/source-reviews/README.md).

## Named results

The links point to the principal source declaration, a reproducible full-statement consumer, and its recorded verification evidence. S02 and S13 each have additional declarations noted below.

### S01: Theorem 1.1, Spectral gaps

- Manuscript lines: 371–379.
- Declaration: [`HitAndRun.Markov.mainSource_complete`](../vendor/ProjectAdapters/MainSourceComplete.lean#L10).
- [Importing consumer](../verification/consumers/MainSourceComplete.lean); [verification receipt](../verification/main-source-complete.json).

### S02: Corollary 1.2, Mixing time

- Manuscript lines: 381–397.
- Declaration: [`HitAndRun.Markov.mixingSource_complete`](../vendor/ProjectAdapters/MainSourceComplete.lean#L24).
- [Importing consumer](../verification/consumers/MainSourceComplete.lean); [verification receipt](../verification/main-source-complete.json).

### S03: Lemma 1.3, Attained divergence solver

- Manuscript lines: 547–569.
- Declaration: [`HitAndRun.Sobolev.BoundedOpenDomain.attained_graph_solver`](../HitAndRun/Sobolev/UniformSource.lean#L48).
- [Importing consumer](../verification/consumers/UniformSource.lean); [verification receipt](../verification/uniform-source.json).

### S04: Theorem 1.4, Babuška–Aziz versus improved Poincaré

- Manuscript lines: 576–579; proof 1042–1059.
- Declaration: [`HitAndRun.Sobolev.BoundedOpenDomain.babuskaAziz_le_one_add_four_improvedPoincare`](../HitAndRun/Sobolev/BabuskaAzizSource.lean#L68).
- [Importing consumer](../verification/consumers/BabuskaAzizSource.lean); [verification receipt](../verification/babuska-aziz-source.json).

### S05: Proposition 2.1, HAR comparison

- Manuscript lines: 621–678.
- Declaration: [`HitAndRun.Markov.hitAndRun_source_gap`](../HitAndRun/Markov/HitAndRunGap.lean#L33).
- [Importing consumer](../verification/consumers/HitAndRunGap.lean); [verification receipt](../verification/hit-and-run-gap.json).

### S06: Proposition 2.2, CHAR comparison

- Manuscript lines: 683–707.
- Declaration: [`HitAndRun.Markov.coordinateHitAndRun_source_gap`](../HitAndRun/Markov/CoordinateKernelIdentificationL2.lean#L120).
- [Importing consumer](../verification/consumers/CoordinateKernelComplete.lean); [verification receipt](../verification/coordinate-kernel-complete.json).

### S07: Theorem 3.1, Weighted L¹ improved Poincaré

- Manuscript lines: 727–734; proof 771–798.
- Declaration: [`HitAndRun.Geometry.reverseBuser_body_infimum_1036`](../HitAndRun/Geometry/ReverseBuserBody.lean#L59).
- [Importing consumer](../verification/consumers/ReverseBuser.lean); [verification receipt](../verification/reverse-buser-source.json).

### S08: Corollary 3.2, Improved Poincaré bound

- Manuscript lines: 737–767.
- Declaration: [`HitAndRun.Geometry.reverseBuser_body_maximum_IPI_4293184`](../HitAndRun/Geometry/ReverseBuserBody.lean#L74).
- [Importing consumer](../verification/consumers/ReverseBuser.lean); [verification receipt](../verification/reverse-buser-source.json).

### S09: Lemma B.1, Duality

- Manuscript lines: 918–926.
- Declaration: [`HitAndRun.Sobolev.BoundedOpenDomain.duality`](../HitAndRun/Sobolev/UniformSource.lean#L59).
- [Importing consumer](../verification/consumers/UniformSource.lean); [verification receipt](../verification/uniform-source.json).

### S10: Lemma B.2, Riesz vector field

- Manuscript lines: 936–955.
- Declaration: [`HitAndRun.Sobolev.BoundedOpenDomain.riesz_full`](../HitAndRun/Sobolev/UniformSource.lean#L74).
- [Importing consumer](../verification/consumers/UniformSource.lean); [verification receipt](../verification/uniform-source.json).

### S11: Lemma B.3, Divergence/curl energy identity

- Manuscript lines: 960–977.
- Declaration: [`HitAndRun.Sobolev.BoundedOpenDomain.graph_curl_energy`](../HitAndRun/Sobolev/CurlUniform.lean#L20).
- [Importing consumer](../verification/consumers/AcceptedMilestone.lean); [verification receipt](../verification/module-modernization.json).

### S12: Lemma B.4, Residual identities

- Manuscript lines: 981–1005.
- Declaration: [`HitAndRun.Sobolev.BoundedOpenDomain.residual_identities`](../HitAndRun/Sobolev/ResidualIdentities.lean#L24).
- [Importing consumer](../verification/consumers/ResidualIdentities.lean); [verification receipt](../verification/residual-identities.json).

### S13: Lemma B.5, Weighted gradient estimate

- Manuscript lines: 1010–1039.
- Declaration: [`HitAndRun.Sobolev.BoundedOpenDomain.rough_weighted_poincare`](../HitAndRun/Sobolev/RoughWeightedSource.lean#L121).
- [Importing consumer](../verification/consumers/RoughWeightedSource.lean); [verification receipt](../verification/rough-weighted-source.json).

S02 also includes `HitAndRun.Markov.mixingSource_HAR_accuracy_complete` and `mixingSource_CHAR_accuracy_complete` in `MainSourceComplete.lean`, and `mixingSource_budget_formula` in [MixingSourceBudget.lean](../vendor/ProjectAdapters/MixingSourceBudget.lean). The full consumer checks these statements as well as the exponential contraction.

S13 also includes `HitAndRun.Sobolev.BoundedOpenDomain.rough_weighted_gradient_norm` in [RoughWeightedSource.lean](../HitAndRun/Sobolev/RoughWeightedSource.lean#L97), which gives the factor-two norm estimate before the Poincaré consequence.

## Mathematical conventions and source-faithfulness

- **Domains and normalization.** Main S01/S02 statements use `n ≥ 2`, bounded open convex sets, and an inscribed unit ball at an arbitrary center. Uniform probability is the actual normalized restricted volume. Stronger intermediate results may omit convexity or use positive dimension; they still cover the manuscript's assumptions.
- **Actual algorithms.** HAR uses the uniform sphere direction and normalized chord law; CHAR uses the uniform coordinate mixture. These are the non-lazy algorithms in the paper, not substituted lazy chains. The conditional-expectation realizations, stationarity, positivity, and native iterate-law transport are proved.
- **Optimal constants.** Poincaré, improved-Poincaré, Babuška–Aziz, and spectral-gap quantities are the actual variational constants on the stated function spaces. Empty divergence fibers have extended-real value infinity. Finiteness is established before converting a constant to a real number.
- **Universal constants.** The constants in S01/S02 are quantified before dimension and geometry. The actual covariance and both Poincaré/covariance-log branches are retained. The KLS15 dependency proves the needed inequality; a Poincaré conclusion is not supplied as a theorem assumption.
- **Exact comparison coefficients.** S04 retains `CBA ≤ 1 + 4 CIPI`; S05 retains `(n+2)/(n(2+CBA))`; S06 retains `1/(n CBA)`.
- **S03/S09/S10.** The divergence acts on genuine zero-trace Sobolev fields. Minimum-energy attainment, both directions of duality, and uniqueness/norm equality for the same Riesz field are proved. Zero inputs are handled separately where a quotient excludes zero.
- **S07/S08.** The statements apply to the whole convex body and the source's locally Lipschitz class. S07 uses any positive inscribed-ball radius and center. S08 constructs the positive maximum inscribed radius and a maximizing center. Explicit sufficient constants are 1036 and 4293184; optimality is not claimed.
- **S11/S12.** Curl energy is the upper-triangle sum `i < j`, not the full Frobenius sum. The residual is built from the same Riesz field and satisfies the signed equation distributionally, without assuming a classical derivative of the original L² data.
- **S13.** Arbitrary L² skew data and the actual distributional equation yield the weighted weak gradient with coefficient 2 and squared coefficient 4. The Poincaré consequence uses a proved cutoff/density extension, not an extra global H¹ or smoothness assumption.

### S02: integer budgets and infinite initial error

Let `M` be the initial chi-square error, `ε > 0`, and let `c/d > 0` be the positive contraction parameter used by `mixingBudget`. The exact implemented budget is

```text
0                                      if M ≤ ε,
Nat.ceil (d * log(M/ε) / (2*c))          if M > ε.
```

For finite `M ≥ 0`, this is the zero/positive-part-and-ceiling interpretation of the manuscript's informal logarithmic bound. The zero branch handles `M = 0` without interpreting `log 0` as an iteration count. Natural-number rounding is explicit. The factor of two follows the squared-L²/chi-square contraction used by the budget proof; asymptotic universal constants do not denote a fixed optimal coefficient.

The exponential theorem accepts arbitrary initial probability laws and extended-real chi-square. When initial chi-square is infinite, its bound is extended-real and does **not** supply a finite accuracy budget. The finite-accuracy theorems expressly require finite initial chi-square and positive `ε`. No manuscript bytes are silently edited to impose these conventions.

## Scope of the evidence

A compilation receipt is not a source-faithfulness proof; an axiom report is not a completed clean build. These are distinct checks. Historical intermediate review labels are superseded by the accepted source map and current verification summary, without rewriting their original receipts. Private-source licensing is separately recorded in [LICENSES.md](LICENSES.md).
