module
public import HitAndRun.Geometry.WeightedPoincareRadialBound
@[expose] public section
open MeasureTheory Set HitAndRun.Geometry
open scoped Pointwise
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : Set E} (hb : Bornology.IsBounded K) (hc : Convex ℝ K) (ho : IsOpen K)
    (hfront : (frontier K).Nonempty) {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball (0 : E) r ⊆ K)
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) {a R : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hR : ∀ x ∈ K, ‖x‖ ≤ R) :
    (∫ x in K, ‖f x - f (a • x)‖ ∂μ) ≤
      R * (a ^ Module.finrank ℝ E)⁻¹ / r *
        ∫ x in K, Metric.infDist x (frontier K) * ‖fderiv ℝ f x‖ ∂μ :=
  integral_radial_difference_le_boundary μ hb hc ho hfront hr hball f hf ha0 ha1 hR
#print axioms HitAndRun.Geometry.continuous_integrableOn_bounded
#print axioms HitAndRun.Geometry.integral_radial_difference_le
#print axioms HitAndRun.Geometry.integrable_radial_slices
#print axioms HitAndRun.Geometry.integrable_dilated_body_slices
#print axioms HitAndRun.Geometry.integral_radial_difference_le_boundary
