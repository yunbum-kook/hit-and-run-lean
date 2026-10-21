# Historical helper receipts

These five compact receipts preserve original hashes, invocation paths, successful exits, and axiom results for earlier helper checkpoints. Their historical pending/remaining fields describe those checkpoints, not the current accepted source scope. They are not instructions to rerun transient paths, nor a substitute for the later source-result receipts.

- [Curl](curl-verification.json): original S11 uniform-domain/curl check; later header mapping is in [module-modernization.json](../module-modernization.json).
- [Cutoff estimate](cutoff-estimate-verification.json).
- [Distance cutoff](distance-cutoff-verification.json).
- [Rough bridge](rough-bridge-verification.json).
- [Skew algebra](skew-verification.json).

Current source status is [source-results.json](../source-results.json); reproducible consumer sources are under `verification/consumers/`. Source/file hashes and original invocation paths in these five receipts are unchanged by their relocation.
