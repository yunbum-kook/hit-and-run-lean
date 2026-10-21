module
public import HitAndRun.Sobolev.MollifiedTestPairing
@[expose] public section
open MeasureTheory HitAndRun.Sobolev EllipticPdes EllipticPdes.H1Graph Filter
open scoped Convolution Topology
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure]
    (rho : ℕ → ContDiffBump (0 : E))
    (hr : Tendsto (fun i => (rho i).rOut) atTop (𝓝 0))
    {h : E → ℝ} (hh : MemLp h 2 μ) {Ω : Set E} (φ : testFunctions Ω) (v : E) :
    Tendsto (fun i => ∫ x, (h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] (rho i).normed μ) x *
      fderiv ℝ (φ : E → ℝ) x v ∂μ) atTop
      (𝓝 (∫ x, h x * fderiv ℝ (φ : E → ℝ) x v ∂μ)) :=
  tendsto_mollified_test_pairing rho hr hh φ v
#print axioms HitAndRun.Sobolev.tendsto_mollified_integral_mul
#print axioms HitAndRun.Sobolev.tendsto_mollified_test_pairing
#print axioms HitAndRun.Sobolev.tendsto_mollified_finite_test_pairing
