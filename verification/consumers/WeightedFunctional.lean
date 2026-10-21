module
import HitAndRun.Sobolev.BoundaryTestLimit
import HitAndRun.Sobolev.SmoothWeightedTest
import HitAndRun.Sobolev.MollifiedSkewEnergy
open MeasureTheory EllipticPdes EllipticPdes.H1Graph HitAndRun.Sobolev HitAndRun.Geometry
open Filter Topology
open scoped Convolution
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Set E}
    (hb : Bornology.IsBounded Ω) (ho : IsOpen Ω) (hc : Ωᶜ.Nonempty)
    (h : E → ℝ) (hh : ContDiff ℝ (⊤ : ℕ∞) h) (φ : testFunctions Ω) (v : E) :
    inner ℝ (smoothWeightedGradientOn (μ := μ) hb h hh) (boundaryFieldClass ho hc φ v) =
      -inner ℝ (fnL (smoothGraph (μ := μ) hb ho h hh)) (partialCls μ Ω φ v) :=
  smooth_weighted_test_pairing hb ho hc h hh φ v
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Set E}
    (hc : Ωᶜ.Nonempty) (φ : testFunctions Ω) {e : ℝ} (he : 0 < e)
    (hm : ∀ x ∈ tsupport (φ : E → ℝ), e ≤ interiorDistance Ω x)
    {r : ℕ → ℝ} (hr : ∀ k, 0 ≤ r k) (hb : ∀ k, r k ≤ e/2) (ht : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, ‖(φ : E → ℝ) x / interiorDistance (innerDomain Ω (r k)) x -
      boundaryTest φ x‖ ^ 2 ∂μ) atTop (𝓝 0) :=
  boundaryTest_inner_sq_tendsto hc φ he hm hr hb ht
#print axioms HitAndRun.Sobolev.boundaryFieldLinear
#print axioms HitAndRun.Sobolev.exists_weighted_gradient_of_test_bound
#print axioms HitAndRun.Sobolev.smoothWeightedGradient_energy_le
#print axioms HitAndRun.Analysis.integral_sq_quotient_sub_tendsto
#print axioms HitAndRun.Sobolev.test_support_distance_pos
#print axioms HitAndRun.Sobolev.boundaryTest_inner_sq_tendsto
#print axioms HitAndRun.Sobolev.smooth_weighted_test_pairing
#print axioms HitAndRun.Sobolev.mollified_memLp
#print axioms HitAndRun.Sobolev.mollified_sq_integral_le
#print axioms HitAndRun.Sobolev.mollified_skew
#print axioms HitAndRun.Sobolev.mollified_upper_energy_le

#print axioms HitAndRun.Sobolev.smooth_weighted_vector_pairing
#print axioms HitAndRun.Sobolev.smooth_weighted_vector_bound
