# Source B.4 distributional residual

Source lines981–1005 fix f in centeredL2, its B.2 Riesz field u, and
Gij=∂j ui−∂i uj. The residual is h=f−divu. No classical derivatives of f
or h are assumed.

`ResidualDistribution.lean` (compiled) tests the Riesz equation against a genuine
compact smooth vector field with only its i-th component nonzero. L2
coordinate polarization expands its gradient pairing. The already proved
H01 mixed-gradient integration-by-parts identity exchanges ∂j uj paired
with ∂iφ into ∂i uj paired with ∂jφ. Subtracting yields exactly
∫h∂iφ = Σj ∫Gij∂jφ. These equalities express ∂ih=Σj∂jGij because the two
sides each have the same distributional minus sign.

`ResidualIdentities.lean` (compiled) chooses the actual adjoint field on the
normalized uniform-domain carrier and proves its Riesz equation, rather than
assuming it as an added source premise. It combines the distributional
identity with the parallel CurlEnergyResidual results: actual mean zero and
inner(h,divu)=Σi<j norm(Gij)^2. All three conclusions refer to the same h,u,G.

All three modules (including GraphEnergyConstant) compiled with exit 0.
The actual imported consumer checks the full three-conclusion B.4 statement
and literal graph-source CBA definition (2 examples, exit 0). Ten transitive
axiom reports contain only propext, Classical.choice and Quot.sound. Evidence:
verification/residual-identities.json. Independent source review remains the
acceptance gate before the source-result ledger is incremented.

## Published checkpoint

The current milestone accepts S03, S09, S10, S11 and S12: 5/13 named results (38.5%). Earlier pending statements above are historical development notes. S11 and S12 source review is recorded in planning/curl-residual-source-review.md; verification/module-modernization.json and verification/residual-identities.json provide the corresponding fresh evidence. S13 and the main spectral-gap/mixing theorems remain open.
