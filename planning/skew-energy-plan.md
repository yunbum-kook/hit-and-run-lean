# B.5 weighted estimate: exact algebra and remaining analysis

Source target S13 is not yet completed. The source allows an L2 residual and antisymmetric L2 tensor related distributionally. It cannot be replaced by a globally smooth assumption.

## Reuse search

Pinned Mathlib's `Algebra/Order/BigOperators/Ring/Finset.lean`, `Finset.sum_mul_sq_le_sq_mul_sq`, is the squared finite Cauchy–Schwarz inequality. `Analysis/Real/Sqrt.lean`, `Real.sum_mul_le_sqrt_mul_sqrt`, is its real square-root form. These are imported library theorems, not copied code. A targeted search of the pinned Mathlib and local Dikin production source found no exact upper-triangle Lagrange identity. The new algebra reuses the already-proved CurlEnergyAlgebra symmetric zero-diagonal double-sum lemma.

## Disjoint slice

`Analysis/SkewEnergy.lean` proves finite real-coordinate identities: upper-triangle wedge energy, its bound when the first vector has energy at most1, symmetric/antisymmetric contraction zero, and the exact reduction of a skew contraction to i<j. Compiled and independently audited at2026-10-21 07:52UTC, together with the actual compact-cutoff test and weak integration identity. Two full examples and9transitive reports passed; only standard axioms were reported. See skew-verification.json. These preserve the crucial factor2 in B.5 rather than replacing upper-triangle energy by full Frobenius energy.

## Next concrete analytic lemma

For a genuine smooth compact cutoff eta supported inside the domain, use the weak derivative integration-by-parts theorem with test eta² times partial_i h. Expand its derivative; the Hessian/skew contraction cancels by the finite identity. The exact skew contraction identity reduces the remainder to upper-triangle entries. Apply the existing finite Cauchy–Schwarz inequality followed by integral Cauchy–Schwarz to obtain the cutoff weighted estimate.

This compact-cutoff lemma does not by itself justify testing with the nonsmooth boundary distance delta. Still required: distributional L2 harmonic regularity to H1_loc (or an alternate direct regularization argument), controlled compact cutoff approximation of delta, and passage to the weighted gradient limit. The external EllipticPDE interior smoothness theorem requires an H1/W12 input and cannot close the initial L2-to-H1_loc gap. Do not treat that theorem as a direct Weyl lemma or count an assumed weighted estimate as S13.
