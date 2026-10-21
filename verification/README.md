# Verification

## What has passed

The 13 named manuscript results have accepted source-faithfulness reviews and actual importing consumers. Their transitive axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`. The source correspondence and exact consumer paths are in [docs/SOURCE_MAP.md](../docs/SOURCE_MAP.md).

The final S01/S02 integration passed ordinary registered `lake env lean` consumers using hash-verified compiled artifacts. [main-source-complete.json](main-source-complete.json) records five full-statement examples, four main-source axiom reports, and the separate eleven-report KLS endpoint audit.

**A full normal Lake source rebuild has not yet been certified.** Artifact-reuse import success is not a clean-build claim. Historical vendor build statements refer to their recorded source snapshots, not automatically to the current project.

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
  AcceptedMilestone ResidualIdentities RoughWeightedSource
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

Any eventual full-build receipt must identify the release snapshot and dependency pins, the exact command and successful exit, whether prior project build artifacts were absent, and the post-build consumer/axiom results. Update the current summary only after those checks finish; preserve historical receipts unchanged.
