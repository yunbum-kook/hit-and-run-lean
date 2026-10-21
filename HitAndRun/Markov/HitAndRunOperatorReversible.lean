module
public import HitAndRun.Markov.HitAndRunOperatorEnergy
@[expose] public section
namespace HitAndRun.Markov
open MeasureTheory ProbabilityTheory HitAndRun.Sobolev
open scoped RealInnerProductSpace
variable {n : ℕ} [NeZero n] (K : BoundedOpenDomain n)
local instance : IsMarkovKernel (hitAndRun K.carrier K.isOpen K.isBounded) :=
  hitAndRun_markov K.isOpen K.isBounded

theorem hitAndRunNativeOperator_symmetric : (hitAndRunNativeOperator K).IsSymmetric := by
  intro f g
  obtain ⟨u, rfl⟩ := K.bodyL2Isometry_surjective f
  obtain ⟨v, rfl⟩ := K.bodyL2Isometry_surjective g
  change inner ℝ (hitAndRunNativeOperator K (K.bodyL2Isometry u)) (K.bodyL2Isometry v) =
    inner ℝ (K.bodyL2Isometry u) (hitAndRunNativeOperator K (K.bodyL2Isometry v))
  rw [real_inner_comm, hitAndRunNativeOperator_inner_average, hitAndRunNativeOperator_inner_average]
  apply integral_congr_ae
  filter_upwards with θ
  rw [← conditionalProjection_symmetric, real_inner_comm]

theorem hitAndRunNativeOperator_positive : (hitAndRunNativeOperator K).IsPositive := by
  refine ⟨hitAndRunNativeOperator_symmetric K, ?_⟩
  intro f
  obtain ⟨u, rfl⟩ := K.bodyL2Isometry_surjective f
  change 0 ≤ inner ℝ (hitAndRunNativeOperator K (K.bodyL2Isometry u)) (K.bodyL2Isometry u)
  rw [real_inner_comm, hitAndRunNativeOperator_inner_average]
  exact integral_nonneg (fun θ => conditionalProjection_positive _ u)

theorem hitAndRun_jointReversible :
    DikinD2.ReversibleSupport.JointReversible (hitAndRun K.carrier K.isOpen K.isBounded) K.bodyUniform :=
  jointReversible_of_native_symmetric _ _ (hitAndRun_stationary K) (hitAndRunNativeOperator_symmetric K)
end HitAndRun.Markov
