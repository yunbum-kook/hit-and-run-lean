module
public import CvxBody.External.TauCeti.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.Compactness.Lindelof

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {μ : Measure E} [μ.IsAddHaarMeasure]

theorem LocallyLipschitzOn.ae_differentiableWithinAt
    {f : E → F} {Ω : Set E} (hf : LocallyLipschitzOn Ω f) (hΩ : MeasurableSet Ω) :
    ∀ᵐ x ∂μ.restrict Ω, DifferentiableWithinAt ℝ f Ω x :=
  (ae_restrict_iff' hΩ).mpr hf.ae_differentiableWithinAt_of_mem

theorem LocallyLipschitzOn.ae_differentiableAt
    {f : E → F} {Ω : Set E} (hf : LocallyLipschitzOn Ω f) (hΩ : IsOpen Ω) :
    ∀ᵐ x ∂μ.restrict Ω, DifferentiableAt ℝ f x := by
  filter_upwards [hf.ae_differentiableWithinAt hΩ.measurableSet,
    ae_restrict_mem hΩ.measurableSet] with x hx hxΩ
  exact hx.differentiableAt (hΩ.mem_nhds hxΩ)

noncomputable section

theorem LocallyLipschitzOn.ae_differentiableAt_of_isOpen
    {f : E → F} {s : Set E} (hf : LocallyLipschitzOn s f) (hs : IsOpen s) :
    ∀ᵐ x ∂μ, x ∈ s → DifferentiableAt ℝ f x := by
  filter_upwards [hf.ae_differentiableWithinAt_of_mem (μ := μ)] with x hx
  intro hxs
  exact (hx hxs).differentiableAt (hs.mem_nhds hxs)

end
