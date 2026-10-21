# Verification evidence

Receipts record actual module compilation and separate importing consumers with the pinned Lean/Mathlib versions. The compact consumer sources in `consumers/` reproduce declaration checks and transitive `#print axioms` queries. Original receipt paths under `.local/` identify the invocation locations; the published consumer copies retain those exact bytes.

After `lake build`, run each consumer with `lake env lean verification/consumers/<file>.lean`. Only standard axioms (`propext`, `Classical.choice`, `Quot.sound`) may occur for accepted declarations. A helper audit is not a proof of source-statement faithfulness or a completed paper endpoint. Large build outputs and transient logs are not distributed.
