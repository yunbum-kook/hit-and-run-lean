module
public import HitAndRun.Geometry.WeightedPoincareLipschitzGraph
@[expose] public section
open MeasureTheory EllipticPdes EllipticPdes.H1Graph HitAndRun.Geometry
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {f φ : E → ℝ} (hf : LocallyLipschitz f)
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ) (v : E) :
    (∫ x, f x * fderiv ℝ φ x v ∂μ) = -(∫ x, fderiv ℝ f x v * φ x ∂μ) :=
  locallyLipschitz_integral_fderiv_test μ hf hφ hcφ v
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Set E}
    (hb : Bornology.IsBounded Ω) (hΩ : IsOpen Ω) (f : E → ℝ) (hf : LocallyLipschitz f) :
    locallyLipschitzGraph (μ := μ) hb hΩ f hf ∈ W12 μ Ω :=
  locallyLipschitzGraph_mem_W12 hb hΩ f hf
#print axioms HitAndRun.Geometry.locallyLipschitz_fderiv_bounded
#print axioms HitAndRun.Geometry.locallyLipschitz_ae_differentiableOn
#print axioms HitAndRun.Geometry.locallyLipschitz_fderiv_memLp
#print axioms HitAndRun.Geometry.locallyLipschitz_integral_fderiv_test
#print axioms HitAndRun.Geometry.locallyLipschitz_hasWeakFDerivOn
#print axioms HitAndRun.Geometry.locallyLipschitzGraph_mem_W12
