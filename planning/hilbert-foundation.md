# Hilbert foundation reuse

Pinned Mathlib commit: 56a005855ea17e0b0958f73ec801ae140b0a1679, Lean 4.35.0.

## Discovery before implementation

- `Mathlib/Analysis/InnerProductSpace/Adjoint.lean`: `ContinuousLinearMap.adjoint` and `adjoint_inner_left` already provide the Riesz representing vector of f ↦ inner(f,Dv) for a bounded linear D between real Hilbert spaces. Reusing adjoint avoids rebuilding Riesz representation.
- `Mathlib/Analysis/InnerProductSpace/Basic.lean`: `ext_inner_right`, `real_inner_le_norm`, `real_inner_self_eq_norm_sq` supply uniqueness and the quotient bound.
- `Mathlib/Order/ConditionallyCompleteLattice/Basic.lean`: `IsLUB.csSup_eq` turns the explicit least-upper-bound argument into the source's real supremum.
- `Mathlib/Analysis/InnerProductSpace/Projection/Minimal.lean`: `exists_norm_eq_iInf_of_complete_convex` is the nearest-point theorem for the minimum-norm preimage supporting Lemma 1.3.

## Implemented scope (compiled and audited)

`HitAndRun/Analysis/AdjointRiesz.lean` contains abstract representing-vector existence/uniqueness and the signed nonzero-vector quotient supremum. Unlike the source's shorthand “set v=u”, its norm proof handles u=0 separately. The norm supremum assumes a nontrivial test space; existence/uniqueness does not.

This is not completion of Lemma B.2: the actual H¹₀ gradient-norm Hilbert space, its completeness, actual weak divergence into centered L², and boundedness must still be built and supplied. No source predicates or source conclusions are assumed as proof substitutes.

No new external code was copied: implementation uses the pinned Mathlib APIs. The coordinator granted the serial compiler lane. Both modules compiled successfully on 2026-10-21; four actual imported full-statement consumer examples compiled; all five declarations report only `propext`, `Classical.choice`, and `Quot.sound`. Receipt: `verification/hilbert-foundation.json`. No paper result is counted complete.

`MinimumNormPreimage.lean` instantiates the existing closed-convex nearest-point theorem on the actual fiber of an arbitrary bounded linear map, proves minimal norm and squared energy, and explicitly requires nonempty fiber. The future Sobolev application still has to derive feasibility from the extended CBA definition.
