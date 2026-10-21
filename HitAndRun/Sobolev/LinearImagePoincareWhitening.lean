module
public import HitAndRun.Sobolev.LinearImagePoincare
public import HitAndRun.Geometry.CovarianceAffineTransportNorm
public import HitAndRun.Geometry.ConvexPoincareFinite
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev.BoundedOpenDomain
open MeasureTheory
open scoped ENNReal
variable {n : ℕ} [NeZero n]

theorem poincareConstant_le_whitened (K : BoundedOpenDomain n)
    (hfin : K.whitenedDomain.poincareConstant < ⊤) :
    K.poincareConstant ≤ ENNReal.ofReal ‖K.centeredCovarianceOperator‖ *
      K.whitenedDomain.poincareConstant := by
  have h := (K.translate (-(∫ x, x ∂uniformMeasure K.carrier))).poincareConstant_le_linearImage
    K.covarianceWhiteningContinuousEquiv hfin
  rw [K.poincareConstant_translate, K.covarianceWhitening_inverse_norm_sq] at h
  exact h
theorem whitenedDomain_convex (K : BoundedOpenDomain n) (hc : Convex ℝ K.carrier) :
    Convex ℝ K.whitenedDomain.carrier :=
  (hc.translate _).linear_image K.covarianceWhiteningContinuousEquiv.toLinearEquiv.toLinearMap

theorem poincareConstant_le_whitened_convex (K : BoundedOpenDomain n)
    (hc : Convex ℝ K.carrier) :
    K.poincareConstant ≤ ENNReal.ofReal ‖K.centeredCovarianceOperator‖ *
      K.whitenedDomain.poincareConstant :=
  K.poincareConstant_le_whitened (K.whitenedDomain.poincareConstant_lt_top_convex
    (K.whitenedDomain_convex hc))

end HitAndRun.Sobolev.BoundedOpenDomain
