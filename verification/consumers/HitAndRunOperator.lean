import HitAndRun.Markov.HitAndRunOperatorEnergy
open MeasureTheory ProbabilityTheory HitAndRun.Sobolev HitAndRun.Markov HitAndRun.Geometry
open scoped ENNReal ProbabilityTheory RealInnerProductSpace
variable {n : ℕ} [NeZero n] (K : BoundedOpenDomain n)
example (f : Lp ℝ 2 (K.ambient.restrict K.carrier)) :
    MemLp (directionalResidual K f) 2 (uniformSphere n) := directionalResidual_memLp K f
example : hitAndRun K.carrier K.isOpen K.isBounded ∘ₘ K.bodyUniform = K.bodyUniform :=
  hitAndRun_stationary K
example (f : Lp ℝ 2 (K.ambient.restrict K.carrier)) :
    K.bodyL2Isometry (hitAndRunOperator K f) = hitAndRunNativeOperator K (K.bodyL2Isometry f) :=
  hitAndRunOperator_body K f
example (f : Lp ℝ 2 (K.ambient.restrict K.carrier)) :
    inner ℝ f (f - hitAndRunOperator K f) =
      ∫ θ, ‖directionalResidual K f θ‖ ^ 2 ∂uniformSphere n := hitAndRunOperator_energy K f
#print axioms measurable_of_measurable_dist
#print axioms stronglyMeasurable_L2_of_representatives
#print axioms directionalBodyAction_stronglyMeasurable
#print axioms directionalProjection_stronglyMeasurable
#print axioms conditionalProjection_residual_norm_le
#print axioms directionalResidual_memLp
#print axioms directionalKernel_stationary
#print axioms hitAndRun_stationary
#print axioms hitAndRun_integral_direction
#print axioms memLp_joint_of_L2_representatives
#print axioms integral_inner_L2_representatives
#print axioms directionalBodyProjection_representative
#print axioms hitAndRunNativeOperator_inner_average
#print axioms hitAndRunOperator_body
#print axioms hitAndRunOperator_inner_average
#print axioms hitAndRunOperator_energy
