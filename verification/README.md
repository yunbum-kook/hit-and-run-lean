# Verification evidence

Receipts record actual module compilation and separate importing consumers with the pinned Lean/Mathlib versions. The compact consumer sources in `consumers/` reproduce declaration checks and transitive `#print axioms` queries. Original receipt paths under `.local/` identify the invocation locations; the published consumer copies retain those exact bytes.

After `lake build`, run each consumer with `lake env lean verification/consumers/<file>.lean`. Only standard axioms (`propext`, `Classical.choice`, `Quot.sound`) may occur for accepted declarations. A helper audit is not a proof of source-statement faithfulness or a completed paper endpoint. Large build outputs and transient logs are not distributed.

Header-only module modernization is recorded in `module-modernization.json`, with explicit old/new SHA256 mappings and fresh aggregate/consumer validation. Historical receipts retain their original compiled hashes; use this mapping rather than interpreting a historical hash as a new compilation. Later endpoint and helper receipts record their own exact bytes. The current umbrella includes these individually compiled modules; no fresh checkout-wide build is claimed.
