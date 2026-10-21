module
public import HitAndRun.Geometry.WeightedPoincareMedianApproximation
@[expose] public section
open MeasureTheory Filter Set HitAndRun.Geometry
open scoped Topology
example
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure E} [μ.IsAddHaarMeasure] [μ.Regular]
    {K : Set E} [IsFiniteMeasure (μ.restrict K)]
    {f : E → F} {g : ℕ → E → F} (hf : MemLp f 2 μ) (hg : ∀ k, MemLp (g k) 2 μ)
    (hgf : Tendsto (fun k => ∫ x, ‖g k x - f x‖ ^ 2 ∂μ) atTop (𝓝 0))
    {a : ℕ → ℝ} (ha0 : ∀ k, 0 < a k) (ha : Tendsto a atTop (𝓝 1)) :
    Tendsto (fun k => ∫ x in K, ‖g k (a k • x) - f x‖ ^ 2 ∂μ) atTop (𝓝 0) :=
  integral_sq_approx_dilation_sub_tendsto hf hg hgf ha0 ha
#print axioms HitAndRun.Geometry.integral_sq_approx_dilation_sub_tendsto
