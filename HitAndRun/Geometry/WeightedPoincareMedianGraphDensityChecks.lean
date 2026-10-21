module
public import HitAndRun.Geometry.WeightedPoincareMedianGraphDensity
@[expose] public section
open MeasureTheory EllipticPdes EllipticPdes.H1Graph HitAndRun.Sobolev HitAndRun.Geometry Set Filter
open scoped Topology
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] [μ.Regular] {Ω : Set E}
    (hb : Bornology.IsBounded Ω) (ho : IsOpen Ω) (hc : Convex ℝ Ω)
    {r : ℝ} (hr : 0 < r) (hball : Metric.ball (0 : E) r ⊆ Ω) (U : W12 μ Ω) :
    ∃ (f : ℕ → E → ℝ) (hf : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (f k)),
      Tendsto (fun k => smoothGraph hb ho (f k) (hf k)) atTop (𝓝 U.val) :=
  exists_smoothGraph_tendsto_W12 hb ho hc hr hball U
#print axioms HitAndRun.Geometry.norm_sq_Lp_sub_eq_integral
#print axioms HitAndRun.Geometry.norm_sq_smoothGraph_sub
#print axioms HitAndRun.Geometry.exists_smoothGraph_tendsto_W12
