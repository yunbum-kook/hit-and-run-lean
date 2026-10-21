module
import HitAndRun.Sobolev.CutoffEstimate
import HitAndRun.Geometry.DistanceCutoff
import HitAndRun.Analysis.MollifierLipschitz
open HitAndRun.Sobolev HitAndRun.Analysis HitAndRun.Geometry
open scoped NNReal Convolution
open MeasureTheory EllipticPdes EllipticPdes.H1Graph
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {Ω : Set E} {μ : Measure E} [μ.IsAddHaarMeasure]

example {n : ℕ}
    (eta : testFunctions Ω) (h : E → ℝ) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (b : Fin n → E) (G : Fin n → Fin n → E → ℝ)
    (hGc : ∀ i j, Continuous (G i j))
    (hG : ∀ x i j, G i j x = -G j i x)
    (hGi : Integrable (fun x => ∑ i, ∑ j, if i < j then G i j x ^ 2 else 0) μ)
    (heta : ∀ x, (∑ i, (fderiv ℝ (eta : E → ℝ) x (b i)) ^ 2) ≤ 1)
    (hrel : ∀ i, ∀ φ : testFunctions Ω,
      (∫ x, h x * fderiv ℝ (φ : E → ℝ) x (b i) ∂μ) =
        ∑ j, ∫ x, G i j x * fderiv ℝ (φ : E → ℝ) x (b j) ∂μ) :
    (∫ x, (eta : E → ℝ) x ^ 2 * ∑ i, (fderiv ℝ h x (b i)) ^ 2 ∂μ) ≤
      4 * ∫ x, ∑ i, ∑ j, if i < j then G i j x ^ 2 else 0 ∂μ := cutoff_energy_le eta h hh b G hGc hG hGi heta hrel

example [HasContDiffBump E] (rho : ContDiffBump (0 : E))
    {f : E → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    LipschitzWith K (rho.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) :=
  lipschitz_normed_convolution rho hf
example (ho : IsOpen Ω) (hne : Ω ≠ Set.univ) {x : E} (hx : x ∈ Ω) :
    interiorDistance Ω x = Metric.infDist x (frontier Ω) :=
  interiorDistance_eq_frontier ho hne hx
#print axioms cutoff_energy_le
#print axioms weighted_skew_young
#print axioms lipschitz_normed_convolution
#print axioms interiorDistance_eq_frontier
#print axioms truncatedDistance_lipschitz
#print axioms tsupport_truncatedDistance_subset
#print axioms tsupport_truncatedDistance_subset_domain
#print axioms hasCompactSupport_truncatedDistance
