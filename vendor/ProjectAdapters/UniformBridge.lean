module
public import CvxBody.External.OAI.KLS.Model
public import HitAndRun.Geometry.UniformConvexDensity
public import HitAndRun.Geometry.CovarianceAffineTransportIsotropy
public import HitAndRun.Geometry.CompactSmoothPoincareTransferConvex
public import HitAndRun.Sobolev.LinearImagePoincareWhitening
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev.BoundedOpenDomain
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n : ℕ} [NeZero n]

/-- Exact eligibility for the licensed density model, on the actual uniform density. -/
theorem uniformDensity_oai_logConcave (K : BoundedOpenDomain n)
    (hc : Convex ℝ K.carrier) :
    OAI.LeanBlast.KLS.IsLogConcaveDensity K.uniformDensity :=
  ⟨K.uniformDensity_nonnegative, K.uniformDensity_measurable,
    K.uniformDensity_probability, K.uniformDensity_log_concave hc⟩

/-- Isotropy is proved by the actual covariance inverse square root, not assumed. -/
theorem whitened_uniformDensity_oai_isotropic (K : BoundedOpenDomain n) :
    OAI.LeanBlast.KLS.IsIsotropic
      (OAI.LeanBlast.KLS.densityMeasure K.whitenedDomain.uniformDensity) := by
  rw [OAI.LeanBlast.KLS.densityMeasure, K.whitenedDomain.uniformDensity_withDensity]
  exact ⟨K.whitenedDomain.uniform_integrable_coordinate,
    K.whitenedDomain.uniform_integrable_coordinate_product,
    K.whitenedDomain_coordinate_mean, K.whitenedDomain_coordinate_secondMoment⟩

/-- The model's gradient has exactly the operator norm of the Fréchet derivative. -/
theorem oai_gradient_norm (f : EuclideanSpace ℝ (Fin n) → ℝ) (x) :
    ‖gradient f x‖ = ‖fderiv ℝ f x‖ := by
  exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.norm_map _

/-- Explicit adapter only: the external PI inequality remains an input. -/
theorem compactSmoothPoincareBound_of_oai (K : BoundedOpenDomain n) {C : ℝ}
    (h : OAI.LeanBlast.KLS.PoincareBound
      (OAI.LeanBlast.KLS.densityMeasure K.uniformDensity) C) :
    K.CompactSmoothPoincareBound C := by
  intro f hf hfc
  have hh := h f ⟨hf, hfc⟩
  rw [OAI.LeanBlast.KLS.densityMeasure, K.uniformDensity_withDensity,
    ← K.measure_eq_uniform] at hh
  simpa only [OAI.LeanBlast.KLS.variance, OAI.LeanBlast.KLS.expectation,
    OAI.LeanBlast.KLS.dirichletEnergy, oai_gradient_norm,
    variance_eq_integral hf.continuous.measurable.aemeasurable] using hh

/-- Actual least Sobolev PI transfer from a supplied whitened model bound. -/
theorem poincareConstant_le_covariance_of_oai (K : BoundedOpenDomain n)
    (hc : Convex ℝ K.carrier) {C : ℝ} (hC : 0 ≤ C)
    (h : OAI.LeanBlast.KLS.PoincareBound
      (OAI.LeanBlast.KLS.densityMeasure K.whitenedDomain.uniformDensity) C) :
    K.poincareConstant ≤ ENNReal.ofReal (C * ‖K.centeredCovarianceOperator‖) := by
  have hw := (K.whitenedDomain.compactSmoothPoincareBound_of_oai h).poincareConstant_le
    hC (K.whitenedDomain_convex hc)
  calc
    K.poincareConstant ≤ ENNReal.ofReal ‖K.centeredCovarianceOperator‖ *
        K.whitenedDomain.poincareConstant := K.poincareConstant_le_whitened_convex hc
    _ ≤ ENNReal.ofReal ‖K.centeredCovarianceOperator‖ * ENNReal.ofReal C := by gcongr
    _ = ENNReal.ofReal (C * ‖K.centeredCovarianceOperator‖) := by
      rw [← ENNReal.ofReal_mul (norm_nonneg _), mul_comm]

/-- The requested numerical adapter; it does not assert the KLS endpoint. -/
theorem poincareConstant_le_fifteen_covariance_of_oai (K : BoundedOpenDomain n)
    (hc : Convex ℝ K.carrier)
    (h : OAI.LeanBlast.KLS.PoincareBound
      (OAI.LeanBlast.KLS.densityMeasure K.whitenedDomain.uniformDensity) 15) :
    K.poincareConstant ≤ ENNReal.ofReal (15 * ‖K.centeredCovarianceOperator‖) :=
  K.poincareConstant_le_covariance_of_oai hc (by norm_num) h

/-- Real least-constant version, with finiteness proved by the same bound. -/
theorem poincareConstant_toReal_le_fifteen_covariance_of_oai (K : BoundedOpenDomain n)
    (hc : Convex ℝ K.carrier)
    (h : OAI.LeanBlast.KLS.PoincareBound
      (OAI.LeanBlast.KLS.densityMeasure K.whitenedDomain.uniformDensity) 15) :
    K.poincareConstant.toReal ≤ 15 * ‖K.centeredCovarianceOperator‖ := by
  have he := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (K.poincareConstant_le_fifteen_covariance_of_oai hc h)
  have hnonneg : 0 ≤ (15 : ℝ) * ‖K.centeredCovarianceOperator‖ := by positivity
  simpa only [ENNReal.toReal_ofReal hnonneg] using he
end HitAndRun.Sobolev.BoundedOpenDomain
