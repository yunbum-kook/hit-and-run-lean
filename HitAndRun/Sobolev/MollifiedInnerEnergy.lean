module
public import HitAndRun.Sobolev.MollifiedSkewEnergy
public import HitAndRun.Sobolev.SmoothDistribution
public import HitAndRun.Sobolev.SmoothVectorEnergy

/-! Actual smoothing of rough distributional data on inner parallel domains. -/
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev
open MeasureTheory EllipticPdes EllipticPdes.H1Graph EllipticPdes.Embedding HitAndRun.Geometry
open scoped BigOperators Convolution
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {μ : Measure (EuclideanSpace ℝ (Fin n))} [μ.IsAddHaarMeasure]

theorem mollified_inner_weighted_energy_le (hb : Bornology.IsBounded Ω)
    (rho : ContDiffBump (0 : EuclideanSpace ℝ (Fin n))) {r : ℝ} (hr : 0 ≤ r)
    (hrr : rho.rOut ≤ r)
    (h : EuclideanSpace ℝ (Fin n) → ℝ) (hh : MemLp h 2 μ)
    (G : Fin n → Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (hG : ∀ i j, MemLp (G i j) 2 μ)
    (hskew : ∀ x i j, G i j x = -G j i x)
    (hrel : ∀ i, ∀ φ : testFunctions Ω,
      (∫ x, h x * fderiv ℝ (φ : EuclideanSpace ℝ (Fin n) → ℝ) x
        (EuclideanSpace.basisFun (Fin n) ℝ i) ∂μ) =
        ∑ j, ∫ x, G i j x * fderiv ℝ (φ : EuclideanSpace ℝ (Fin n) → ℝ) x
          (EuclideanSpace.basisFun (Fin n) ℝ j) ∂μ) :
    ‖smoothWeightedGradient (μ := μ) (innerDomain_bounded hb hr)
      (h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] rho.normed μ)
      (contDiff_convolution_normed rho (hh.locallyIntegrable (by norm_num)))‖ ^ 2 ≤
      4 * ∫ x, ∑ i, ∑ j, if i < j then G i j x ^ 2 else 0 ∂μ := by
  have hgsm i j := contDiff_convolution_normed rho ((hG i j).locallyIntegrable (by norm_num))
  have hgi : Integrable (fun x => ∑ i, ∑ j, if i < j then
      (G i j ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] rho.normed μ) x ^ 2 else 0) μ := by
    apply integrable_finsetSum
    intro i _
    apply integrable_finsetSum
    intro j _
    split_ifs
    · exact (mollified_memLp rho (hG i j)).integrable_sq
    · exact integrable_zero _ _ _
  apply (smoothWeightedGradient_energy_le (innerDomain_bounded hb hr) _ _ _
    (fun i j => (hgsm i j).continuous) (mollified_skew rho G hskew) hgi ?_).trans
  · exact mul_le_mul_of_nonneg_left (mollified_upper_energy_le rho G hG) (by norm_num)
  · intro i φ
    apply mollified_distribution_on_inner rho _ h (G i) _ _
      (hh.locallyIntegrable (by norm_num))
      (fun j => (hG i j).locallyIntegrable (by norm_num)) (hrel i) φ
    intro x hx
    exact closedBall_subset_of_lt_interiorDistance x (hrr.trans_lt hx)
end HitAndRun.Sobolev
