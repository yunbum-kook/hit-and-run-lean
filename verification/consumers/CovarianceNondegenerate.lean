module
import HitAndRun.Geometry.CovarianceNondegenerate
open HitAndRun.Sobolev

example {n : ℕ} [NeZero n] (K : BoundedOpenDomain n)
    (v : EuclideanSpace ℝ (Fin n)) (hv : v ≠ 0) :
    0 < inner ℝ (K.centeredCovarianceOperator v) v :=
  K.centeredCovarianceOperator_inner_pos v hv

example {n : ℕ} [NeZero n] (K : BoundedOpenDomain n) :
    LinearMap.ker K.centeredCovarianceOperator.toLinearMap = ⊥ :=
  K.centeredCovarianceOperator_ker

example {n : ℕ} [NeZero n] (K : BoundedOpenDomain n)
    (v : EuclideanSpace ℝ (Fin n)) :
    K.centeredCovarianceEquiv.symm (K.centeredCovarianceOperator v) = v :=
  K.centeredCovarianceEquiv.symm_apply_apply v

#print axioms BoundedOpenDomain.inner_eq_mean_of_centeredCovarianceOperator_eq_zero
#print axioms BoundedOpenDomain.centeredCovarianceOperator_inner_pos
#print axioms BoundedOpenDomain.centeredCovarianceOperator_ker
#print axioms BoundedOpenDomain.centeredCovarianceOperator_bijective
#print axioms BoundedOpenDomain.centeredCovarianceEquiv
#print axioms BoundedOpenDomain.centeredCovarianceEquiv_apply
