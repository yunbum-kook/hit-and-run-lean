# Normal Lake build and final audit: PASS

Completed 2026-10-21 at 23:17:55 UTC. The checked source snapshot is [648a3343](https://github.com/yunbum-kook/hit-and-run-lean/commit/648a33434d74c574ef5884430195831f8d50cebb). The intervening commit `3c1f766dc5dfd7600d67d4a392174aea44e58dc9` changed only the README introduction; its edit is preserved. This evidence update changes no production Lean source, build configuration, or dependency pin.

## Results

- 1,950 distinct module commands succeeded: 1,667 actual regenerations and 283 legitimate trace reuses.
- The final ordinary `lake --no-cache --no-ansi --fail-fast build HitAndRun` exited 0 at 22:23:18 UTC and reported 6,049 Lake jobs. The preceding ordinary `--no-build` guard also exited 0. Job counts are not distinct theorem or module counts.
- 72 published importing consumers plus the [supplementary exact budget-formula consumer](consumers/SupplementalBudgetFormula.lean) succeeded: 73 commands in total.
- 601 named transitive axiom reports were reconciled, including all 13 primary source-result endpoints and additional mixing declarations. Only `propext`, `Classical.choice`, and `Quot.sound` occurred; no `sorryAx` or unexpected axiom was reported.
- Final source/configuration/pin/consumer bindings and completed artifact hashes matched. The terminal audit exited 0 with no mismatches or pending evidence. All 148,278 shared-dependency size/mtime metadata entries were unchanged; that check is not a complete content-hash audit of dependencies.

These verification counts do not increase mathematical progress beyond 13/13 named paper results. The axiom claim covers the explicitly audited declaration closures, not every declaration in every imported library.

## Reproduce

Use the committed Lean4.35.0 toolchain and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, without `lake update`:

```sh
lake --no-cache --no-ansi --fail-fast build HitAndRun

env -u LEAN_PATH lake env lean \
  -DautoImplicit=false -DmaxSynthPendingDepth=3 \
  verification/consumers/MainSourceComplete.lean

env -u LEAN_PATH lake env lean \
  -DautoImplicit=false -DmaxSynthPendingDepth=3 \
  verification/consumers/SupplementalBudgetFormula.lean
```

See [verification instructions](README.md) for the other paper endpoints and retained consumer files. Inspect the named axiom outputs and reject `sorryAx` or unexpected custom axioms.

## Scope and evidence

This is an ordinary pinned Lake build using legitimate dependency caches and project traces, not an empty-cache clean-room checkout. No fabricated Lake traces or proof artifacts were used. The previously approved two-line Lake registration correction is already included in the bound source commit. Resource-limited module compilation was serialized; the final aggregate used the unchanged published configuration.

The exact compact [machine-readable receipt](normal-lake-build.json) preserves successful command/log hashes, source binding, cache/trace scope and terminal reconciliation hashes. Its `.local/` references identify retained historical execution records, not dependencies required to build the repository. Earlier receipts remain unchanged rather than being relabeled as later executions.

Distribution remains private: successful verification does not grant public redistribution rights. See [component licenses](../docs/LICENSES.md).
