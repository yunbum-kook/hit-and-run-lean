# Private reverse-Buser integration review

2026-10-21 15:36 UTC. Review in progress; source count remains 9/13. This is not a successful build or endpoint-acceptance receipt.

## Exact scope and source status

Candidate is the 45-module MilmanPoincare closure at chewisinho/cvx_body_lean commit 41678c03373f8d3ac9d95bab31bcc17022d85bec, comprising 29 authored modules and 16 separately attributed external modules. The user directed private-project reuse. This direction is recorded as private reuse, not an invented upstream license or public redistribution grant. Preserve original notices and component-specific licenses; public release of authored reused code remains a separate permission question.

The proposed import closure is recorded in .local/reverse-buser-publication-plan.json. The port worker maintains the authoritative exact source map at .local/reverse-buser-port/publication-source-map.json. No full KLS15 endpoint or its experimental build closure belongs in this milestone. Only three previously checked shared modules are needed: CvxBody.External.OAI.KLS.Model, CvxBody.External.TauCeti.Analysis.Calculus.Rademacher, and CvxBody.External.TauCeti.Analysis.Convex.Measure. Their own imports close within those modules plus pinned Mathlib. Later KLS integration must reuse the same definitions rather than redeclare them.

## Independent mathematical review so far

Read the actual source statements and proof compositions, not just README claims:

- Needle existence takes actual measurable nonnegative logconcave density, probability and first moment, plus a measurable set of mass strictly between zero and one. It constructs a probability-kernel disintegration with logconcave line densities, unit directions, guide alignment and mass balance. It does not assume Cheeger or a desired decomposition.
- The needle-to-Cheeger theorem requires positive scale s and the actual integrable 1-Lipschitz guide's mean absolute deviation at most s. Its coefficient is 1/(256*s). The proposed uniform adapter supplies s=sqrt(actual optimal CPI), with finiteness and positivity discharged by existing convex-domain results.
- The proposed median L1 adapter applies Cheeger to positive and negative median parts. Exact derivative norms have disjoint strict-sign supports, including zero derivative at the truncation minimum, so summing does not double the coefficient. Integrability follows from bounded global Lipschitz tests.
- Ambient C1 test functions are multiplied by a compact smooth bump equal to one on a neighborhood of the entire bounded closure. Both function values and derivative germs are preserved there. Thus the ordinary C1 input does not add compact support or global Lipschitz restrictions to its final test class.
- The ordinary input coefficient256 would instantiate the already verified body wrappers with universal weighted coefficient1036 (=12+4*256). The existing IPI squared bound has universal coefficient4,293,184 (=4*1036^2). These are legitimate explicit witnesses for the manuscript's implicit universal constants, not claims about sharp constants.
- Existing body wrappers retain all ambient locally Lipschitz functions, arbitrary inscribed-ball center, Lebesgue/body integrals, actual boundary distance and actual weak-Sobolev optimal constants. The maximum inscribed radius is constructed, not assumed attained.

## Gates still required

1. Finish exact-source port and median/uniform adapters; collect compatibility diffs and final hashes.
2. Register the allowlisted CvxBody source root as a dedicated Lean library in the normal Lake project without changing Lean4.35 or Mathlib56a005 pins.
3. Obtain actual normal Lake compilation and separately importing full source-form S07/S08 consumers with no remaining reverse-Buser premise; isolated raw Lean compilation alone is insufficient for portable integration acceptance.
4. Require standard-only transitive axiom reports for the final consumers, exact compiled-byte identity and complete dependency closure.
5. Freeze one coherent private snapshot including notices/provenance, minimal shared modules and source-form wrappers, excluding all unverified KLS endpoint and experimental artifacts. Update source counts only after independent final review and coordinator acceptance.

## Isolated exact-source gate reviewed (2026-10-21 15:49 UTC)

All 45 source hashes independently match the producer's frozen publication-source-map (SHA256 e5bf7a22b84f35e515bbdb888b36eddb1f3d37dc2016b7f68136c931582daab8). All five relocated adapter/consumer source hashes match final-build-receipt.json; each recorded command exited zero on Lean4.35. The actual ReverseBuserChecks log has fourteen transitive reports containing only propext, Classical.choice and Quot.sound. Read all eight full examples, the complete printed property definitions and explicit exported signatures. No reverse-Buser supplier, finite-CPI premise, test-class restriction, or assumed maximum-radius attainment remains in the final body endpoints.

One compatibility proof edit in RayShift replaces a pointwise simplification of a local continuous-linear-map identity by operator-level module normalization. The exact local equality and exported theorem statement are unchanged; the corrected file actually compiled. Source module headers are adapted as recorded by the producer. External source bytes and exact scoped notices remain mapped separately.

Proposed final added files: 45 CvxBody modules, four HitAndRun.Geometry.ReverseBuser proof modules, and the full importing Checks consumer. No KLS15 endpoint. The existing production Lake configuration has only HitAndRun; a dedicated CvxBody library with scoped original autoImplicit=true is required. Keep HitAndRun/adapters autoImplicit=false. Actual normal-Lake integration/consumer acceptance remains pending, so this review does not change the 9/13 source count or authorize claiming a portable successful build.

## Production acceptance (2026-10-21 15:53 UTC)

Actual normal configured Lake Checks build, aggregate HitAndRun build and separate `lake env lean -DautoImplicit=false verification/consumers/ReverseBuser.lean` each exited zero. Eight full examples and fourteen standard-only transitive reports passed. Exact final source bytes match the frozen isolated gate. Scoped original autoImplicit=true applies only to CvxBody; project adapters remain false. No additional source changes were needed. S07 and S08 are now independently accepted, bringing the named-source total to11/13. Only S01/S02 remain open.
