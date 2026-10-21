# Production-pin port modifications

This is an adapted import closure, not unchanged upstream. Original source identity and final source bytes are recorded per file in PRODUCTION-PROVENANCE.json. Original upstream notices and modification records are preserved alongside this file.

The closure uses Lean 4.35.0 and Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679. Existing canonical CvxBody Model, Measure and Rademacher modules are reused rather than duplicated. Six EllipticPdes import shims reuse the project's existing compatible EllipticPDE declarations; ConvolutionCompatibility preserves eight historical signatures with direct wrappers. No old Mathlib source or artifact shadows the pinned dependency.

Ports include module/public-import/expose headers; explicit source-equivalent type annotations and imports; NullMeasurableSet coercions; updated Pi-family ContDiff component arguments; two obsolete grw-generated side-goal branches removed; and explicit qualification of the original mollifier. Two original stochastic compatibility modules are retained. An unused experimental rfl helper that failed was not included. No sorry, custom axiom, skipped-kernel setting, changed endpoint hypothesis, changed conclusion or changed numeric constant is accepted.

All 1,657 source modules passed the isolated production-pin gate. The exact ordinary-import density/admissible-law endpoint consumer reports only propext, Classical.choice and Quot.sound transitively. Actual normalized uniform, whitening and weak-Sobolev adapters are separate project proofs, not added assumptions of this vendor theorem.

The current integration reuses hash-verified compiled artifacts in the project-owned build directory and tests ordinary imports through lake env. This is not a clean Lake rebuild. No fabricated Lake traces, .ilean or C artifacts were created. A portable full source rebuild is `lake build HitAndRun`; dependencies are pinned in the root manifest. Build caches and compilation artifacts are not part of the release source.
