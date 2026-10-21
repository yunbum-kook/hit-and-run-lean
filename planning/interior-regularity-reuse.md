# Targeted interior regularity discovery

Read-only source inspection, 2026-10-21, EllipticPDE commit ec784093f30308ef770ff855ce624725adf6f870. No files in this candidate closure imported or compiled here.

## Actual usable API shape

`lean/EllipticPdes/Regularity/Local/InteriorSmooth.lean` provides `EllipticPdes.Regularity.interior_smooth_global_W12`. On an open measurable subset of Euclidean dimension n+1, it takes an actual `FullEllipticOp`, C1 principal coefficients, all-order `IsWkInftyCoeff` and `IsWkInftyLower`, an `H1amb` element U, an L2 datum f with all-order weak derivatives and L2 bounds, and `IsLocalWeakSolution Op Ω U f`. It concludes an almost-everywhere equal smooth representative on Ω. No zero boundary condition is imposed.

Crucially, `Regularity/Local/WeakSolution.lean` defines `IsLocalWeakSolution` as U in W12 plus the actual bilinear weak equation against compact smooth test functions. Its plain-function constructor requires square-integrable u AND square-integrable weak gradient G and `HasWeakGradOn Ω u G`. This does not supply the initial weak gradient automatically.

`Existence/Harmonic.lean` has actual Laplacian/classical maximum-principle bridges, but those require C2 regularity already. It is not a distributional Weyl lemma.

## Consequence for Lemma B.5

The proposed distributional implication grad h = div(skew G) implies Laplacian h = 0 could open a harmonic regularity route. The discovered API does NOT directly accept an L2 distributionally harmonic h: one must first prove H1 local regularity (or find a genuine Weyl lemma), specialize coefficients to the identity and zero lower terms/datum, and bridge carriers. Weighted boundary approximation remains a separate obligation even after interior smoothness.

This is a targeted negative/partial result, not an exhaustive proof that no Weyl lemma exists anywhere in the repository. Keep the original source statement and do not assume H1 regularity or boundary approximation merely to use this API.

Links:
- https://github.com/alejandro-soto-franco/EllipticPDE/blob/ec784093f30308ef770ff855ce624725adf6f870/lean/EllipticPdes/Regularity/Local/InteriorSmooth.lean
- https://github.com/alejandro-soto-franco/EllipticPDE/blob/ec784093f30308ef770ff855ce624725adf6f870/lean/EllipticPdes/Regularity/Local/WeakSolution.lean
- https://github.com/alejandro-soto-franco/EllipticPDE/blob/ec784093f30308ef770ff855ce624725adf6f870/lean/EllipticPdes/Existence/Harmonic.lean
