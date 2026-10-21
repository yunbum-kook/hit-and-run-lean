module
public import HitAndRun.Geometry.WeightedPoincareMedianDensity
@[expose] public section
open MeasureTheory Filter Set HitAndRun.Geometry
open scoped Topology
example {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure E} [μ.IsAddHaarMeasure] [μ.Regular]
    {K : Set E} [IsFiniteMeasure (μ.restrict K)]
    {f : E → F} (hf : MemLp f 2 μ) {a : ℕ → ℝ}
    (ha0 : ∀ k, 0 < a k) (ha : Tendsto a atTop (𝓝 1)) :
    Tendsto (fun k => ∫ x in K, ‖f (a k • x) - f x‖ ^ 2 ∂μ) atTop (𝓝 0) :=
  integral_sq_dilation_sub_tendsto hf ha0 ha
#print axioms HitAndRun.Geometry.integral_sq_dilation_sub_tendsto
#print axioms HitAndRun.Geometry.integral_sq_dilation_sub_tendsto_of_bounded
#print axioms HitAndRun.Geometry.memLp_comp_dilation
#print axioms HitAndRun.Geometry.integral_sq_dilation
#print axioms HitAndRun.Geometry.dilation_error_sq_le

example
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure E} [μ.IsAddHaarMeasure] [μ.Regular]
    {K : Set E} [IsFiniteMeasure (μ.restrict K)] (hK : MeasurableSet K)
    (hconv : Convex ℝ K) (hzero : (0 : E) ∈ K)
    {f : E → F} (hf : MemLp f 2 (μ.restrict K)) {a : ℕ → ℝ}
    (ha0 : ∀ k, 0 < a k) (ha1 : ∀ k, a k ≤ 1) (ha : Tendsto a atTop (𝓝 1)) :
    Tendsto (fun k => ∫ x in K, ‖f (a k • x) - f x‖ ^ 2 ∂μ) atTop (𝓝 0) :=
  integral_sq_dilation_sub_tendsto_restrict hK hf ha0 ha
    (fun k x hx => hconv.smul_mem_of_zero_mem hzero hx ⟨(ha0 k).le, ha1 k⟩)

#print axioms HitAndRun.Geometry.integral_sq_dilation_sub_tendsto_restrict
#print axioms HitAndRun.Geometry.integral_sq_inward_dilation_sub_tendsto
