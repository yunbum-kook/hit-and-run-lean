module
public import HitAndRun.Geometry.WeightedPoincareAssembly
@[expose] public section
open MeasureTheory Set Filter HitAndRun.Geometry
open scoped Pointwise Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
example (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : Set E} (hb : Bornology.IsBounded K) (hc : Convex ℝ K) (ho : IsOpen K)
    (hfront : (frontier K).Nonempty) {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball (0 : E) r ⊆ K) {a R B : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (hB : 0 ≤ B) (hR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hL1 : ∀ g : E → ℝ, ContDiff ℝ 1 g → ∃ z : ℝ,
      (∫ x in K, ‖g x - z‖ ∂μ) ≤ B * ∫ x in K, ‖fderiv ℝ g x‖ ∂μ)
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) :
    ∃ z : ℝ, (∫ x in K, ‖f x - z‖ ∂μ) ≤
      (R * (a ^ Module.finrank ℝ E)⁻¹ / r +
        B * a * (a ^ Module.finrank ℝ E)⁻¹ / ((1 - a) * r)) *
        ∫ x in K, Metric.infDist x (frontier K) * ‖fderiv ℝ f x‖ ∂μ :=
  exists_weighted_center_of_ordinaryL1 μ hb hc ho hfront hr hball ha0 ha1 hB hR hL1 f hf
#print axioms HitAndRun.Geometry.integral_contraction_le_boundary
#print axioms HitAndRun.Geometry.exists_weighted_center_of_ordinaryL1
