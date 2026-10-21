module
public import HitAndRun.Geometry.WeightedPoincareMedianSmooth
@[expose] public section
open MeasureTheory EllipticPdes EllipticPdes.H1Graph HitAndRun.Geometry Set
open scoped Convolution
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Set E}
    (ho : IsOpen Ω) (hc : Convex ℝ Ω)
    {r a : ℝ} (hball : Metric.ball (0 : E) r ⊆ Ω)
    (ha : 0 ≤ a) (ha1 : a < 1) (rho : ContDiffBump (0 : E))
    (hrho : rho.rOut < (1 - a) * r) (U : W12 μ Ω) {x : E} (hx : x ∈ Ω) :
    gradient (fun y =>
      (Ω.indicator (fnL U.val) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] rho.normed μ) (a • y)) x =
      a • (rho.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] Ω.indicator (gradL U.val)) (a • x) :=
  gradient_inward_mollified_W12 ho hc hball ha ha1 rho hrho U hx
#print axioms HitAndRun.Geometry.inner_mollification
#print axioms HitAndRun.Geometry.gradient_mollified_of_weak_gradient
#print axioms HitAndRun.Geometry.closedBall_subset_at_contraction
#print axioms HitAndRun.Geometry.weak_graph_zero_extension_identity
#print axioms HitAndRun.Geometry.gradient_comp_dilation
#print axioms HitAndRun.Geometry.gradient_inward_mollified_W12
