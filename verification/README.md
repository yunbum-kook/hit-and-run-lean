# Verification

## What has passed

The 13 named manuscript results have accepted source-faithfulness reviews and actual importing consumers. Their transitive axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`. The source correspondence and exact consumer paths are in [docs/SOURCE_MAP.md](../docs/SOURCE_MAP.md).

The final S01/S02 integration passed ordinary registered `lake env lean` consumers using hash-verified compiled artifacts. [main-source-complete.json](main-source-complete.json) records five full-statement examples, four main-source axiom reports, and the separate eleven-report KLS endpoint audit.

**The full ordinary pinned Lake build and post-build consumer sweep passed on 2026-10-21.** There were 1,950 distinct successful module commands (1,667 regenerated, 283 legitimately trace-reused), 73 consumer commands, and 601 standard-only named axiom reports covering every primary source endpoint. This is not an empty-cache clean-room build. The [final receipt](normal-lake-build.md) binds the proof/configuration inputs to source commit `648a33434d74c574ef5884430195831f8d50cebb`. Historical artifact-reuse receipts remain unchanged.

## Reproduce

Use the root `lean-toolchain`, `lakefile.toml`, and committed `lake-manifest.json` without repinning. From the repository root:

```sh
lake build HitAndRun

env -u LEAN_PATH lake env lean \
  -DautoImplicit=false -DmaxSynthPendingDepth=3 \
  verification/consumers/MainSourceComplete.lean
```

The main consumer checks exact spectral-gap, native-law contraction, finite-accuracy, and integer-budget signatures. To check all accepted source results and the external endpoint, run these consumers after the build:

```sh
for consumer in \
  MainSourceComplete KLS15Endpoint UniformSource BabuskaAzizSource \
  HitAndRunGap CoordinateKernelComplete ReverseBuser \
  AcceptedMilestone ResidualIdentities RoughWeightedSource SupplementalBudgetFormula
do
  env -u LEAN_PATH lake env lean \
    -DautoImplicit=false -DmaxSynthPendingDepth=3 \
    "verification/consumers/$consumer.lean" || exit 1
done
```

`AcceptedMilestone` includes the complete S11 curl-energy consumer. The other compact consumers and helper receipts remain available for narrower regression checks. Resource-limited environments may serialize the build, but must not change theorem statements, skip the kernel, substitute old Mathlib artifacts, or manufacture Lake traces.

The `#print axioms` output is evidence to inspect, not by itself a script-enforced whitelist. Reject any claimed source-result closure containing `sorryAx` or an additional custom axiom. Successful compilation alone also does not establish correspondence with the manuscript; that is why the source map and reviews are separate.

The [source-result ledger](source-results.json) and [semantic source reviews](source-reviews/README.md) are the maintained entry points. Older hash-bound helper receipts are retained in [historical/](historical/README.md).

## Receipts and historical evidence

JSON receipts preserve exact source hashes, successful invocation/consumer results, and compact axiom reports. Paths under `.local/` or `/tmp/` are historical invocation locations, not release dependencies. The reproducible sources are the files in `consumers/`; transient logs and cached objects are not distributed.

[module-modernization.json](module-modernization.json) maps historical source hashes to the header-modernized bytes and records fresh validation of that change. Do not relabel an old hash or successful build as a check of later source bytes. Later endpoint receipts have their own exact hashes.

The [normal-build receipt](normal-lake-build.json) identifies the verified source snapshot and pins, exact successful aggregate command, retained cache/trace scope, post-build consumer results, and integrity checks. Module and audit counts measure verification coverage, not additional paper results. Historical receipts retain their original scope and status.
