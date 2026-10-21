module
import HitAndRun.Sobolev.WeakDerivativeMollifier
open MeasureTheory EllipticPdes
open scoped Convolution
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Set E}
    (rho : ContDiffBump (0 : E)) (x : E) (hs : Metric.closedBall x rho.rOut ⊆ Ω)
    (h g : E → ℝ) (v : E) (hh : LocallyIntegrable h μ)
    (hrel : ∀ φ : testFunctions Ω,
      (∫ y, h y * fderiv ℝ (φ : E → ℝ) y v ∂μ) = -(∫ y, g y * (φ : E → ℝ) y ∂μ)) :
    fderiv ℝ (h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] rho.normed μ) x v =
      (g ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] rho.normed μ) x :=
  HitAndRun.Sobolev.fderiv_mollified_of_weak_partial rho x hs h g v hh hrel
#print axioms HitAndRun.Sobolev.fderiv_mollified_of_weak_partial
