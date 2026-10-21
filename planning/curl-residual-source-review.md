# Independent source review: S11 and S12

2026-10-21. Pinned arXiv:2608.16878v1, source/tex/main.tex lines 960–1018. This note is semantic review, not a substitute for the separate compilation receipts.

## S11: Lemma B.3

CurlEnergyIBP derives the cross-term identity by two integrations by parts on compact smooth tests and two H01 closure limits. No cross-term identity is assumed. CurlEnergyAlgebra uses the exact upper-triangle i<j convention: G_ij = partial_j u_i - partial_i u_j. CurlEnergy and CurlUniform prove the full gradient-energy decomposition for actual H01 vector graphs. The Haar identity applies to volume; normalizing uniform volume scales every term equally. There is no factor-two loss or extra regularity premise.

## S12: Lemma B.4

ResidualIdentities uses the same actual Riesz field adjoint(div) f in all three conclusions. The residual is f minus div u. Its mean is zero by the actual centered divergence and centered target. ResidualDistribution proves the distributional gradient identity against every compact smooth test, with the signs consistent with G_ij = partial_j u_i - partial_i u_j. It does not assume a classical derivative of f or the residual. The final pairing is exactly the upper-triangle skew energy.

GraphEnergyConstant additionally identifies the optimal divergence constant with the original H01 graph-fiber supremum/infimum. Both directions use the actual graph inverse and preserve the energy and norm quotient; no feasibility or finite-infimum premise is inserted into the definition.

## Evidence distinction

S11 has the original curl consumers plus fresh post-header-modernization consumers recorded separately. Historical byte hashes remain historical and are related to current files by verification/module-modernization.json. S12 has verification/residual-identities.json: five recorded file hashes checked, two full importing examples, and ten standard-only transitive axiom reports. Source acceptance remains the coordinator's ledger decision. This review does not cover S13/B.5 or any main spectral-gap endpoint.
