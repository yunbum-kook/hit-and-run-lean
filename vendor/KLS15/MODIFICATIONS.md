# Local KLS15 backport modifications

This is the source backport for the CvxBody Lean repository, taken from
KLS15 revision `fe59199e9c039a79a436daa939f79662df2596da`. It targets the existing
Lean 4.34.1 / Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` environment.
Local compilation and mathematical acceptance are recorded separately in
`../../docs/part2/KLS15-FULL-BACKPORT.md`.

The original `NOTICE`, copyright headers, and all supplied component license
files are retained. The original notices may describe directories outside this
selected public-endpoint import closure; retaining a notice does not claim that
all upstream directories have been copied or imported. `IMPORT-CLOSURE.txt`
lists the exact local closure. The original source manifest is retained as
`upstream-source-manifest.json`.

* `OpenAIKLSBridge.lean` imports the repository's existing
  `CvxBody.External.OAI.KLS.Model` instead of `OAI.Analysis.KLS.Model` to avoid
  duplicate declarations under `OAI.LeanBlast.KLS`. The declaration body from
  `namespace OAI` onward is byte-identical. The original OAI Model source is
  retained for provenance but is not imported by the local endpoint.
* `DifferentialGeometry.Analysis.Calculus.Rademacher` imports the existing
  `CvxBody.External.TauCeti.Analysis.Calculus.Rademacher` and omits its duplicate
  `LocallyLipschitzOn.ae_differentiableWithinAt_of_mem` declaration. Independent
  comparison confirmed the imported theorem has exactly the original statement
  and full generality. The other three vendor theorem statements and proofs are
  retained verbatim. This reviewed declaration reuse avoids a global-name
  collision when the endpoint is imported alongside `CvxBody`.
* The missing Mathlib process modules are provided under the local
  `KLS15Compat.Probability.Process` module paths. Brownian auxiliary imports
  select those paths. Their provenance, exact patches, and independent
  compatibility/audit evidence are recorded in `KLS15Compat/` and
  `../../docs/part2/KLS15-PROCESS-BACKPORT.md`.
* Indicator proofs use the pinned measurable-set APIs instead of newer
  null-measurable-set APIs. Qualified references to quasi-measure-preserving
  maps use the pinned `MeasureTheory.Measure` namespace.
* Deprecated import paths and theorem aliases are replaced by the identical
  current exports. Proof-only linter repairs remove unused simp arguments,
  use sequential tactics for a single goal, or replace proof-local `letI` by
  `let`. Source theorem binders remain unchanged. Where the older pinned linter
  rejects an unused source binder, a declaration-scoped setting preserves that
  exact binder rather than changing the source statement. One probability
  instance also retains its original proof body under a declaration-scoped
  instance-style linter setting.

* Product-map equalities in `KLS.GaussianSmoothingMoments` and
  `KLS.GaussianAdditiveStein` are proved directly using measurable-set
  extensionality, product evaluation, and measurable integrals. The older
  convenience theorem requires an extra finiteness instance, while these direct
  proofs preserve the original arbitrary-measure statements. Only the fixed
  Gaussian right factor needs the existing probability instance.
* Several declarations use declaration-scoped
  `synthInstance.maxHeartbeats = 200000` to resolve the unchanged
  `ContinuousSMul` instance on the original `Space n` or tensor Euclidean space;
  this changes only the
  elaboration budget. Exact sites are listed in the source inventory.

* `LevyStochCalc.Ito.PicardSelfMap` locally seals two process constructors
  during proof elaboration. Its projection theorem names existing implicit
  parameters explicitly and unfolds those constructors before `rfl`. Independent
  review confirmed the same original parameters, statement, and definition
  bodies. This avoids repeated expansion and allows the original proof to check
  under the unchanged 8 GiB cap.

* In `OrderedOneFormKernel.symmetricOrderedOneFormLIE`, one `invFun`
  membership certificate changes from `by simpa using u.property` to `by simp`
  to satisfy the still-enabled unnecessary-simpa check. The data expression,
  map fields and complete type are unchanged; independent review approved this
  proof-irrelevant Prop-field exception. `KLS.WeightedL2Indicator` likewise
  changes only the private Lp representative certificate, preserving the same
  represented function. These are not claims of byte-identical proof fields.
* At the frozen boundary after 1,402 selected modules had compiled, the remaining
  252 selected source files received a file-local compatibility profile disabling
  exactly six cosmetic checks: unused section variables, unused variables,
  unnecessary sequence focus, unused tactics, unreachable tactics and unused simp
  arguments. Those diagnostics are consequently unavailable throughout the listed
  files. The exact module list, option names, inserted block and before/after
  hashes are in `COSMETIC-LINTER-POLICY.json`. Erasing the block restores each
  insertion-time source byte-for-byte; the compiled prefix was untouched.
  Independent positive/negative import probes confirm registration and that the
  options do not propagate to importers. Warning-as-error handling, deprecated
  API diagnostics, all kernel/elaboration/axiom checks, pins and global flags
  remain enabled and unchanged.

The final source/hash inventory is in `BACKPORT-MANIFEST.json` and the complete
source patch in `BACKPORT.patch`. All 1,654 selected modules passed a complete
source-stable strict normal Lake invocation. The independent exhaustive audit
passed for all 20,749 declarations, including private declarations, with only
`propext`, `Classical.choice` and `Quot.sound` allowed. Portable build and audit
receipts are in `../../docs/part2/evidence/KLS15-FullBuild.json` and
`KLS15-FullAxiomAudit.json`. CvxBody integration and the covariance-bound root
have separate checks. No new axiom, missing-proof marker or additional source
assumption is introduced by this backport.
