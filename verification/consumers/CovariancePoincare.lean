module
import HitAndRun.Geometry.CovariancePoincare
open MeasureTheory ProbabilityTheory HitAndRun.Sobolev
open scoped ENNReal
example {n : ℕ} [NeZero n] (K : BoundedOpenDomain n)
    (h : K.poincareConstant < ⊤) :
    ‖K.centeredCovarianceOperator‖ ≤ K.poincareConstant.toReal :=
  K.norm_centeredCovarianceOperator_le h
example {n : ℕ} [NeZero n] (K : BoundedOpenDomain n) :
    MemLp id 2 (uniformMeasure K.carrier) := K.uniform_memLp_id
#print axioms BoundedOpenDomain.uniform_memLp_id
#print axioms BoundedOpenDomain.linearH1
#print axioms BoundedOpenDomain.linearH1_fn
#print axioms BoundedOpenDomain.linearH1_grad
#print axioms BoundedOpenDomain.linearH1_gradientEnergy
#print axioms BoundedOpenDomain.centeredCovarianceOperator_positive
#print axioms BoundedOpenDomain.linearH1_varianceEnergy
#print axioms BoundedOpenDomain.centeredCovarianceOperator_quadratic_le
#print axioms BoundedOpenDomain.norm_centeredCovarianceOperator_le
