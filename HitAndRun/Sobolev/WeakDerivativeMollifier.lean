module
public import HitAndRun.Sobolev.DistributionMollifier

/-! Interior differentiation of mollified genuine weak derivatives. The input
relation is required only for compact tests inside the original domain. -/
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev
open MeasureTheory EllipticPdes EllipticPdes.H1Graph
open scoped Convolution
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Set E}

theorem fderiv_mollified_of_weak_partial
    (rho : ContDiffBump (0 : E)) (x : E)
    (hs : Metric.closedBall x rho.rOut ⊆ Ω)
    (h g : E → ℝ) (v : E) (hh : LocallyIntegrable h μ)
    (hrel : ∀ φ : testFunctions Ω,
      (∫ y, h y * fderiv ℝ (φ : E → ℝ) y v ∂μ) =
        -(∫ y, g y * (φ : E → ℝ) y ∂μ)) :
    fderiv ℝ (h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] rho.normed μ) x v =
      (g ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] rho.normed μ) x := by
  have hr := hrel (translatedNormedTest (μ := μ) rho x hs)
  simp only [fderiv_translatedNormedTest, mul_neg, integral_neg] at hr
  have he := neg_injective hr
  rw [fderiv_convolution_normed_apply rho hh]
  exact he
end HitAndRun.Sobolev
