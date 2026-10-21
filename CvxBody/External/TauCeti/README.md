# Vendored: Tau Ceti (subset)

Source: https://github.com/TauCetiProject/TauCeti, commit
`bab6e39bcc08efc89140619387bfe20d3c8797e1` (branch `main`, 2026-10-18), Apache License 2.0
(copy in `docs/third-party/TauCeti-LICENSE`). Each file retains its original copyright and author header.

Initially copied: the import closure inside Tau Ceti of
`TauCeti.MeasureTheory.OptimalTransport.Duality.Attainment` (17 modules, 5853 lines here).
Upstream targets Lean `v4.36.0-rc1` with a newer Mathlib and uses the `module` system; this
repository pins Lean 4.34.1 and an older Mathlib. The Lean namespace `TauCeti` is unchanged; module
`TauCeti.X.Y` is `CvxBody.External.TauCeti.X.Y`, at `CvxBody/External/TauCeti/X/Y.lean`.

P10 adds 51 modules from the same fixed revision for Brenier optimal transport,
Alexandrov differentiability and Monge–Ampère identities. The combined subset
contains 68 modules. The original 17 files below remain unchanged. See the
[P10 transport record](../../../docs/part1/P10-TRANSPORT.md) for the exact new
import closure, five compatibility repairs, source statements and independent
proof/axiom review; the new module hashes are in the
[P10 manifest](../../../docs/part1/P10-MODULES.sha256).

## Initial duality modules (all under `CvxBody/External/TauCeti/`)

- `Data/EReal/Operations`
- `Topology/Semicontinuity/Approximation`
- `MeasureTheory/Integral/Bochner/Basic`
- `MeasureTheory/Measure/Dirac`
- `MeasureTheory/Measure/LowerSemicontinuousLintegral`
- `MeasureTheory/Measure/ProbabilityMeasure/Map`
- `MeasureTheory/OptimalTransport/Coupling`
- `MeasureTheory/OptimalTransport/GraphPlan/Basic`
- `MeasureTheory/OptimalTransport/Cost/Basic`
- `MeasureTheory/OptimalTransport/Cost/CyclicalMonotonicity`
- `MeasureTheory/OptimalTransport/CTransform/Basic`
- `MeasureTheory/OptimalTransport/CTransform/CyclicalMonotonicity`
- `MeasureTheory/OptimalTransport/Compactness`
- `MeasureTheory/OptimalTransport/Duality/Basic`
- `MeasureTheory/OptimalTransport/Duality/Certificate`
- `MeasureTheory/OptimalTransport/Existence/Basic`
- `MeasureTheory/OptimalTransport/Duality/Attainment`

## Initial duality port changes from upstream

No statement and no proof was changed. Every module builds under
`lake --wfail build CvxBody.External.TauCeti.<module>` with no warning, and no `set_option` was
added.

- Removed the `module` keyword; `public import X` became `import X`; imports of `TauCeti.*` were
  renamed to `CvxBody.External.TauCeti.*`.
- `public section` became `section` (so that the matching `end` still closes it).
- `Cost/CyclicalMonotonicity.lean`, line 160: `open MeasureTheory` became
  `open _root_.MeasureTheory`. Inside `namespace TauCeti` that line was resolved to the namespace
  `TauCeti.MeasureTheory` (created by `Measure/Dirac.lean`), instead of to Mathlib's
  `MeasureTheory`; this resolution is specific to the Lean version in this repository.
- Mathlib adaptations: none were needed (all Mathlib imports exist in the pin).

## What the headline theorems say (module `Duality/Attainment`)

For `X`, `Y` Polish Borel spaces, `μ`, `ν` probability measures, `c : X × Y → ℝ` continuous,
nonnegative and bounded:

- `TauCeti.isGreatest_kantorovichDualValue_integrable`: the transport cost
  `(transportCost (fun z ↦ ENNReal.ofReal (c z)) μ ν).toReal` is the greatest element of
  `{r | ∃ φ ψ, Integrable φ μ ∧ Integrable ψ ν ∧ (∀ x y, φ x + ψ y ≤ c (x, y)) ∧
  kantorovichDualValue μ ν φ ψ = r}` (strong duality with dual attainment).
- `TauCeti.exists_isDualCertificate_of_continuous`: there are a coupling `π` and `c`-conjugate
  integrable potentials `φ`, `ψ` forming an `IsDualCertificate` (`π` is concentrated on the contact set).
- `TauCeti.IsOptimalCoupling.exists_isDualCertificate_of_continuous`: every optimal coupling `π` of
  `μ`, `ν` admits such potentials (hypotheses: `OpensMeasurableSpace` on `X`, `Y`, `X × Y`,
  `HereditarilyLindelofSpace (X × Y)`, `IsProbabilityMeasure μ`).

`#print axioms` for all three reports only `propext`, `Classical.choice`, `Quot.sound`.
