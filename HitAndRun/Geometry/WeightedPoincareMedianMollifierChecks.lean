module
public import HitAndRun.Geometry.WeightedPoincareMedianMollifier
@[expose] public section
open MeasureTheory Filter Set HitAndRun.Geometry
open scoped Topology Convolution
example {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {μ : Measure E} [μ.IsAddHaarMeasure] [μ.Regular]
    {K : Set E} [IsFiniteMeasure (μ.restrict K)] (hK : MeasurableSet K)
    {f : E → F} (hf : MemLp f 2 (μ.restrict K))
    {rho : ℕ → ContDiffBump (0 : E)}
    (hr : Tendsto (fun k => (rho k).rOut) atTop (𝓝 0))
    {a : ℕ → ℝ} (ha0 : ∀ k, 0 < a k) (ha : Tendsto a atTop (𝓝 1)) :
    Tendsto (fun k => ∫ x in K,
      ‖((rho k).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] K.indicator f) (a k • x) - f x‖ ^ 2 ∂μ)
      atTop (𝓝 0) :=
  integral_sq_zeroExtension_mollification_dilation_sub_tendsto hK hf hr ha0 ha
#print axioms HitAndRun.Geometry.integral_norm_sq_eq_eLpNorm_toReal_sq
#print axioms HitAndRun.Geometry.memLp_mollification_two
#print axioms HitAndRun.Geometry.integral_sq_mollification_sub_tendsto
#print axioms HitAndRun.Geometry.integral_sq_mollification_dilation_sub_tendsto
#print axioms HitAndRun.Geometry.integral_sq_smul_approx_sub_tendsto
#print axioms HitAndRun.Geometry.integral_sq_zeroExtension_mollification_dilation_sub_tendsto
