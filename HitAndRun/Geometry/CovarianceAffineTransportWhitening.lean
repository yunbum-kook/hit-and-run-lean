module
public import HitAndRun.Geometry.CovarianceAffineTransport
public import HitAndRun.Geometry.CovarianceWhitening
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev.BoundedOpenDomain
open MeasureTheory
variable {n : ℕ} [NeZero n]

/-- Actual normalized-uniform domain obtained by centering and inverse-square-root whitening. -/
def whitenedDomain (K : BoundedOpenDomain n) : BoundedOpenDomain n :=
  (K.translate (-(∫ x, x ∂uniformMeasure K.carrier))).linearImage K.covarianceWhiteningContinuousEquiv

theorem whitenedDomain_mean (K : BoundedOpenDomain n) :
    (∫ x, x ∂uniformMeasure K.whitenedDomain.carrier) = 0 := by
  rw [whitenedDomain, linearImage_mean, translate_mean, neg_add_cancel, map_zero]

theorem whitenedDomain_covariance (K : BoundedOpenDomain n) :
    K.whitenedDomain.centeredCovarianceOperator = ContinuousLinearMap.id ℝ _ := by
  rw [whitenedDomain, linearImage_centeredCovarianceOperator, translate_centeredCovarianceOperator]
  apply ContinuousLinearMap.ext
  intro x
  have h := congrArg (fun A => A x) K.covarianceWhiteningEquiv_identity
  exact h

end HitAndRun.Sobolev.BoundedOpenDomain
