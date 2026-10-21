# Isolated KLS15 verification feasibility (source inspection only)

2026-10-21. No new KLS dependency imported into the project and no KLS compilation started.

## Checked inventory

The existing sampling environment already contains Lean4.34.1 and Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612, exactly the CvxBody backport pins. Its Mathlib cache currently has3,673 oleans. Do not copy those dependencies or change this project's Lean4.35.0 pins. The selected pinned source closure has now been saved in a quarantined, ignored inspection directory, without any compiled artifacts.

At CvxBody commit0e96a41441c2a3878dd0a4e5ea5dc5590eaf4fcf the vendor tree contains1,655 Lean files totaling12,631,906 source bytes. IMPORT-CLOSURE.txt lists1,654 names; BACKPORT-MANIFEST.json marks1,654 imported modules; every corresponding path exists in the Git tree and their Git-reported sizes sum to12,629,469bytes. A subsequent comment-aware recursive import traversal independently reconstructed 1,654 reachable vendor modules totaling 12,629,469 bytes. All 1,655 fetched vendor files were checked against their pinned Git blob SHA. Three required CvxBody bridge modules were also read. This is source verification, not compilation or a semantic endorsement of the endpoint.

The backport manifest records481 changed/added Lean files. MODIFICATIONS.md identifies extra CvxBody OAI-model and Rademacher imports, selected process backports, and proof/linter compatibility changes. A vendor-only source copy is therefore insufficient. Apache/component notices must accompany selected files; the CvxBody-owned bridge licensing question remains separate.

## Economical execution plan, awaiting a separate go-ahead

1. Completed for the Lean source: fetch only the pinned source package (about12.6MB Lean source plus notices/manifest), not compiled archives or a new Mathlib environment. Verify every source Git blob against the frozen tree. Never execute upstream scripts.
2. Completed for vendor and CvxBody module roots: parse imports recursively from KLS15 and the covariance endpoint, resolving all module roots and CvxBody dependencies. Distinguish project modules from existing Mathlib dependencies. This produces the actual reachable closure, detects missing aliases, and replaces the unverified imported-list claim.
3. Check expected dependency pins and availability against the existing4.34.1 cache; stage a separate verification-only workspace with shared dependency links and isolated build output. Preserve new project's4.35 pins.
4. Estimate artifact growth from a small representative closure and inspect disk before any full build. Source size alone does not predict compiled storage or elapsed build time; no reliable total estimate is established yet. Reported upstream10,586jobs is not an independently measured budget.
5. If justified, compile the exact consumer and audit transitive axioms, plus definitions/statement equivalence and481 backport changes. Compile success alone does not prove paper correspondence. A verified4.34 result cannot be imported as an olean into4.35; source port/recompile remains necessary before production reuse.

No compilation has been authorized or performed for this candidate. Continue bounded semantic review only; an execution decision must follow the disk and artifact estimate. KLS15 remains quarantined; no S01 completion credit.
