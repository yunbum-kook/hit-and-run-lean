import HitAndRun.Geometry.CovarianceAffineTransportWhitening
noncomputable section
open MeasureTheory ProbabilityTheory HitAndRun.Sobolev
open HitAndRun.Sobolev.BoundedOpenDomain
variable {n : ℕ} [NeZero n]
example (K : BoundedOpenDomain n) (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    (uniformMeasure K.carrier).map L = uniformMeasure (K.linearImage L).carrier :=
  K.linearImage_uniform_map L
example (K : BoundedOpenDomain n) (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    (∫ x, x ∂uniformMeasure (K.linearImage L).carrier) = L (∫ x, x ∂uniformMeasure K.carrier) :=
  K.linearImage_mean L
example (K : BoundedOpenDomain n) (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    (K.linearImage L).centeredCovarianceOperator = L.toContinuousLinearMap.comp
      (K.centeredCovarianceOperator.comp L.toContinuousLinearMap.adjoint) :=
  K.linearImage_centeredCovarianceOperator L
example (K : BoundedOpenDomain n) (c : EuclideanSpace ℝ (Fin n)) :
    (K.translate c).centeredCovarianceOperator = K.centeredCovarianceOperator :=
  K.translate_centeredCovarianceOperator c
#print axioms linearImage_map_volume
#print axioms linearImage_volume_factor
#print axioms linearImage_uniform_map
#print axioms linearImage_measurePreserving
#print axioms linearImage_mean
#print axioms linearImage_covarianceBilin
#print axioms linearImage_centeredCovarianceOperator
#print axioms translate_uniform_map
#print axioms translate_mean
#print axioms translate_covarianceBilin
#print axioms translate_centeredCovarianceOperator

example (K : BoundedOpenDomain n) :
    (∫ x, x ∂uniformMeasure K.whitenedDomain.carrier) = 0 := K.whitenedDomain_mean
example (K : BoundedOpenDomain n) :
    K.whitenedDomain.centeredCovarianceOperator = ContinuousLinearMap.id ℝ _ :=
  K.whitenedDomain_covariance
#print axioms whitenedDomain_mean
#print axioms whitenedDomain_covariance
