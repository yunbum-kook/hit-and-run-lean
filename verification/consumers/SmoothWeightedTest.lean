module
import HitAndRun.Sobolev.SmoothGraph
import HitAndRun.Sobolev.SmoothDistribution
import HitAndRun.Geometry.InnerDomain
import HitAndRun.Analysis.BoundedTestFunctional
import HitAndRun.Sobolev.BoundaryTest
open MeasureTheory EllipticPdes EllipticPdes.H1Graph
open HitAndRun.Sobolev HitAndRun.Geometry HitAndRun.Analysis
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Set E}
    (hb : Bornology.IsBounded Ω) (hΩ : IsOpen Ω)
    (f : E → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ∃ U : W12 μ Ω, (fnL (U : H1Graph μ Ω) : E → ℝ) =ᵐ[μ.restrict Ω] f :=
  ⟨smoothH1 hb hΩ f hf, smoothGraph_fn hb hΩ f hf⟩
example {V X : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [AddCommGroup X] [Module ℝ X]
    (A : X →ₗ[ℝ] V) (g : X →ₗ[ℝ] ℝ) {R : ℝ} (hR : 0 ≤ R)
    (hb : ∀ z, |g z| ≤ R * ‖A z‖) :
    ∃ v : V, (∀ z, inner ℝ v (A z) = g z) ∧ ‖v‖ ≤ R :=
  exists_riesz_of_test_bound A g hR hb
#print axioms HitAndRun.Sobolev.smoothGraph_mem_W12
#print axioms HitAndRun.Sobolev.norm_sq_smoothGraph
#print axioms HitAndRun.Sobolev.smooth_distribution_of_pointwise
#print axioms HitAndRun.Sobolev.mollified_distribution_on_inner
#print axioms HitAndRun.Geometry.innerDomain_distance_lower
#print axioms HitAndRun.Analysis.exists_riesz_of_test_bound
#print axioms HitAndRun.Sobolev.boundaryTest_continuous
#print axioms HitAndRun.Sobolev.boundaryTest_memLp
