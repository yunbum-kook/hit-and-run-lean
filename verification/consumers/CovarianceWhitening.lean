module
import HitAndRun.Geometry.CovarianceWhitening
open HitAndRun.Sobolev

example {n : ℕ} [NeZero n] (K : BoundedOpenDomain n) :
    K.centeredCovarianceMatrix.PosDef := K.centeredCovarianceMatrix_posDef

example {n : ℕ} [NeZero n] (K : BoundedOpenDomain n) :
    K.covarianceWhiteningMatrix * K.centeredCovarianceMatrix *
      K.covarianceWhiteningMatrix.transpose = 1 := K.covarianceWhiteningMatrix_identity

example {n : ℕ} [NeZero n] (K : BoundedOpenDomain n) :
    K.covarianceWhiteningEquiv.toLinearMap ∘ₗ K.centeredCovarianceOperator.toLinearMap ∘ₗ
      K.covarianceWhiteningEquiv.toLinearMap.adjoint = LinearMap.id :=
  K.covarianceWhiteningEquiv_identity

example {n : ℕ} [NeZero n] (K : BoundedOpenDomain n)
    (v : EuclideanSpace ℝ (Fin n)) :
    K.covarianceWhiteningEquiv.symm (K.covarianceWhiteningEquiv v) = v :=
  K.covarianceWhiteningEquiv.symm_apply_apply v

#print axioms BoundedOpenDomain.centeredCovarianceMatrix
#print axioms BoundedOpenDomain.toEuclideanLin_centeredCovarianceMatrix
#print axioms BoundedOpenDomain.centeredCovarianceMatrix_posDef
#print axioms BoundedOpenDomain.covarianceSqrtMatrix
#print axioms BoundedOpenDomain.covarianceSqrtMatrix_mul_self
#print axioms BoundedOpenDomain.covarianceSqrtMatrix_isUnit
#print axioms BoundedOpenDomain.covarianceWhiteningMatrix
#print axioms BoundedOpenDomain.covarianceWhiteningMatrix_transpose
#print axioms BoundedOpenDomain.covarianceWhiteningMatrix_mul_sqrt
#print axioms BoundedOpenDomain.covarianceSqrtMatrix_mul_whitening
#print axioms BoundedOpenDomain.covarianceWhiteningMatrix_identity
#print axioms BoundedOpenDomain.covarianceWhiteningEquiv
#print axioms BoundedOpenDomain.covarianceWhiteningEquiv_toLinearMap
#print axioms BoundedOpenDomain.covarianceWhiteningEquiv_identity

#print axioms BoundedOpenDomain.covarianceWhiteningContinuousEquiv
#print axioms BoundedOpenDomain.covarianceWhiteningContinuousEquiv_toLinearMap
