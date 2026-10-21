module
public import HitAndRun.Geometry.WeightedPoincareMedianH1Density
@[expose] public section
open MeasureTheory EllipticPdes EllipticPdes.H1Graph HitAndRun.Geometry Set Filter
open scoped Topology
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] [μ.Regular] {Ω : Set E}
    [IsFiniteMeasure (μ.restrict Ω)] (ho : IsOpen Ω) (hc : Convex ℝ Ω)
    {r : ℝ} (hr : 0 < r) (hball : Metric.ball (0 : E) r ⊆ Ω) (U : W12 μ Ω) :
    ∃ f : ℕ → E → ℝ, (∀ k, ContDiff ℝ (⊤ : ℕ∞) (f k)) ∧
      Tendsto (fun k => ∫ x in Ω, ‖f k x - fnL U.val x‖^2 ∂μ) atTop (𝓝 0) ∧
      Tendsto (fun k => ∫ x in Ω, ‖gradient (f k) x - gradL U.val x‖^2 ∂μ) atTop (𝓝 0) :=
  exists_smooth_W12_approximation ho hc hr hball U
#print axioms HitAndRun.Geometry.exists_smooth_W12_component_approximation
#print axioms HitAndRun.Geometry.exists_smooth_W12_approximation
