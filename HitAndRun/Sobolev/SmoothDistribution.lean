module
public import HitAndRun.Sobolev.CutoffEnergy
public import HitAndRun.Sobolev.DistributionMollifier

/-! Recover the genuine test-function relation from a classical equality only
on the test domain. No relation is required outside the domain. -/
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev
open MeasureTheory EllipticPdes EllipticPdes.H1Graph
open scoped BigOperators Convolution
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Set E}

theorem smooth_distribution_of_pointwise {ι : Type*} [Fintype ι]
    (h : E → ℝ) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (G : ι → E → ℝ) (hG : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (G j))
    (v : E) (b : ι → E)
    (he : ∀ x ∈ Ω, fderiv ℝ h x v = ∑ j, fderiv ℝ (G j) x (b j))
    (φ : testFunctions Ω) :
    (∫ x, h x * fderiv ℝ (φ : E → ℝ) x v ∂μ) =
      ∑ j, ∫ x, G j x * fderiv ℝ (φ : E → ℝ) x (b j) ∂μ := by
  have ih (f : E → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (w : E) :
      (∫ x, f x * fderiv ℝ (φ : E → ℝ) x w ∂μ) =
        -(∫ x, (φ : E → ℝ) x * fderiv ℝ f x w ∂μ) := by
    have hw := (hasWeakFDerivOn_fderiv (μ := μ) (Ω := ⊤)
      (hf.of_le (by simp)).contDiffOn w).integral_eq φ.2.1 φ.2.2.1 (Set.subset_univ _)
    simpa only [smul_eq_mul, mul_comm] using hw
  rw [ih h hh v]
  simp_rw [ih _ (hG _) _]
  rw [Finset.sum_neg_distrib]
  congr 1
  rw [← integral_finsetSum _ (fun j _ => integrable_cutoff_mul φ
    (contDiff_directional (hG j) (b j)).continuous)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    by_cases hx : x ∈ Ω
    · rw [he x hx, Finset.mul_sum]
    · have hzero : (φ : E → ℝ) x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hs => hx (φ.2.2.2 hs))
      simp [hzero]
/-- A rough distributional relation becomes a genuine smooth test relation on
any inner region where the mollifier fits. -/
theorem mollified_distribution_on_inner {ι : Type*} [Fintype ι]
    (rho : ContDiffBump (0 : E)) {U : Set E}
    (hs : ∀ x ∈ U, Metric.closedBall x rho.rOut ⊆ Ω)
    (h : E → ℝ) (G : ι → E → ℝ) (v : E) (b : ι → E)
    (hh : LocallyIntegrable h μ) (hG : ∀ j, LocallyIntegrable (G j) μ)
    (hrel : ∀ φ : testFunctions Ω,
      (∫ y, h y * fderiv ℝ (φ : E → ℝ) y v ∂μ) =
        ∑ j, ∫ y, G j y * fderiv ℝ (φ : E → ℝ) y (b j) ∂μ)
    (φ : testFunctions U) :
    (∫ x, (h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] rho.normed μ) x *
      fderiv ℝ (φ : E → ℝ) x v ∂μ) =
    ∑ j, ∫ x, (G j ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] rho.normed μ) x *
      fderiv ℝ (φ : E → ℝ) x (b j) ∂μ := by
  apply smooth_distribution_of_pointwise _
    (EllipticPdes.Embedding.contDiff_convolution_normed rho hh) _
    (fun j => EllipticPdes.Embedding.contDiff_convolution_normed rho (hG j)) v b _ φ
  intro x hx
  exact mollified_distribution_pointwise rho x (hs x hx) h G v b hh hG hrel

end HitAndRun.Sobolev
