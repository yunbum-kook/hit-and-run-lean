module
import HitAndRun.Sobolev.DistributionMollifier
import HitAndRun.Sobolev.WeakGraphLimit
import HitAndRun.Analysis.MollifiedL2
open MeasureTheory Metric Set EllipticPdes EllipticPdes.H1Graph HitAndRun.Sobolev HitAndRun.Analysis
open scoped Convolution BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Set E}
example {ι : Type*} [Fintype ι]
    (rho : ContDiffBump (0 : E)) (x : E) (hs : closedBall x rho.rOut ⊆ Ω)
    (h : E → ℝ) (G : ι → E → ℝ) (v : E) (b : ι → E)
    (hh : LocallyIntegrable h μ) (hG : ∀ j, LocallyIntegrable (G j) μ)
    (hrel : ∀ φ : testFunctions Ω,
      (∫ y, h y * fderiv ℝ (φ : E → ℝ) y v ∂μ) =
        ∑ j, ∫ y, G j y * fderiv ℝ (φ : E → ℝ) y (b j) ∂μ) :
    fderiv ℝ (h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] rho.normed μ) x v =
      ∑ j, fderiv ℝ (G j ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] rho.normed μ) x (b j) := mollified_distribution_pointwise rho x hs h G v b hh hG hrel
example (u : ℕ → W12 μ Ω) (f : Lp ℝ 2 (μ.restrict Ω)) {R : ℝ}
    (hR : 0 ≤ R) (hu : ∀ k, ‖u k‖ ≤ R)
    (hf : Filter.Tendsto (fun k => fnL (u k : H1Graph μ Ω)) Filter.atTop (nhds f)) :
    ∃ U : W12 μ Ω, fnL (U : H1Graph μ Ω) = f ∧ ‖U‖ ≤ R :=
  exists_weak_graph_of_bounded_l2_limit u f hR hu hf
#print axioms translatedNormedTest
#print axioms mollified_distribution_pointwise
#print axioms closedBall_subset_of_lt_interiorDistance
#print axioms exists_weak_graph_of_bounded_l2_limit
#print axioms weak_graph_fn_injective
#print axioms weak_graph_norm_le_of_bounded_l2_limit
#print axioms memLp_normed_convolution_two
#print axioms tendsto_mollifiedL2
