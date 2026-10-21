module
/-
Ported from https://github.com/openai/math, revision
1581d4cbdd69a0faf34b2089614fe2a814316a6a,
file `lean/OAI/Analysis/KLS/Model.lean`.

Copyright OpenAI.  Licensed under the Apache License, Version 2.0; see
`CvxBody/External/OAI/README.md` in this repository for the licence and
the full provenance record.

Changes made in this port, and only these, both confined to the import block in the diffusion project, and the module path was renamed again
when vendored here (`DiffusionLower.External.KLS.*` became `CvxBody.External.OAI.KLS.*`):
* the module path `OAI.Analysis.KLS.*` became `CvxBody.External.OAI.KLS.*`,
  and the `import` lines were rewritten to match;
* upstream `Model.lean` used `import Mathlib`; it now names the modules it
  needs, and the four derivative modules that `import Mathlib` had been
  supplying transitively were added to `Spectral/BrascampLiebMoments.lean`
  where they are used.  This keeps the repository's focused Mathlib cache
  sufficient.
No statement, proof, declaration name or namespace was touched: the Lean and
Mathlib pins of `openai/math` at that revision are identical to this
repository's, and the upstream namespace `OAI.LeanBlast.KLS` is preserved.
-/
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Topology.Algebra.Support

@[expose] public section

namespace OAI

noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace LeanBlast.KLS

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The ordinary Lebesgue-density measure. -/
def densityMeasure {n : ℕ} (ρ : Space n → ℝ) : Measure (Space n) :=
  volume.withDensity (fun x => ENNReal.ofReal (ρ x))

/-- Probability-density and log-concavity conditions.
`ConcaveOn` includes convexity of the positive support. -/
structure IsLogConcaveDensity {n : ℕ} (ρ : Space n → ℝ) : Prop where
  nonnegative : ∀ x, 0 ≤ ρ x
  measurable : Measurable ρ
  probability : IsProbabilityMeasure (densityMeasure ρ)
  log_concave : ConcaveOn ℝ {x | 0 < ρ x} (fun x => Real.log (ρ x))

/-- Zero mean and identity covariance, with all moment integrability explicit. -/
structure IsIsotropic {n : ℕ} (μ : Measure (Space n)) : Prop where
  integrable_coordinate : ∀ i : Fin n, Integrable (fun x : Space n => x i) μ
  integrable_product : ∀ i j : Fin n, Integrable (fun x : Space n => x i * x j) μ
  mean_zero : ∀ i : Fin n, (∫ x : Space n, x i ∂μ) = 0
  second_moment : ∀ i j : Fin n,
    (∫ x : Space n, x i * x j ∂μ) = if i = j then 1 else 0

def expectation {n : ℕ} (μ : Measure (Space n)) (f : Space n → ℝ) : ℝ :=
  ∫ x, f x ∂μ

def variance {n : ℕ} (μ : Measure (Space n)) (f : Space n → ℝ) : ℝ :=
  ∫ x, (f x - expectation μ f) ^ 2 ∂μ

def dirichletEnergy {n : ℕ} (μ : Measure (Space n)) (f : Space n → ℝ) : ℝ :=
  ∫ x, ‖gradient f x‖ ^ 2 ∂μ

/-- The exact compactly supported smooth real test-function class. -/
def IsTestFunction {n : ℕ} (f : Space n → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ HasCompactSupport f

/-- Direct Poincare inequality, avoiding an infimum convention for the constant. -/
def PoincareBound {n : ℕ} (μ : Measure (Space n)) (C : ℝ) : Prop :=
  ∀ f : Space n → ℝ, IsTestFunction f → variance μ f ≤ C * dirichletEnergy μ f

/-- The full dimension-free statement: one constant works for every dimension,
every isotropic log-concave density, and every smooth compactly supported test. -/
def KLSStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
    ∀ ρ : Space n → ℝ, IsLogConcaveDensity ρ → IsIsotropic (densityMeasure ρ) →
      PoincareBound (densityMeasure ρ) C

abbrev FullStatement := KLSStatement

end LeanBlast.KLS

end

end OAI
