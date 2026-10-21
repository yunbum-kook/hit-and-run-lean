module
public import HitAndRun.Markov.CoordinateKernelIdentificationStationary
public import HitAndRun.Markov.ChiSquareContraction
@[expose] public section

namespace HitAndRun.Markov
open MeasureTheory ProbabilityTheory HitAndRun.Sobolev
open scoped ENNReal ProbabilityTheory RealInnerProductSpace
variable {n : ℕ} [NeZero n] (K : BoundedOpenDomain n)

local instance : IsMarkovKernel (coordinateHitAndRun K.carrier K.isOpen.measurableSet) :=
  coordinateHitAndRun_markov K.isOpen K.isBounded

/-- The native L2 operator is defined from the actual kernel integral. -/
noncomputable def coordinateNativeOperator : Lp ℝ 2 K.bodyUniform →L[ℝ] Lp ℝ 2 K.bodyUniform :=
  DikinD2.NativeL2.operator (coordinateHitAndRun K.carrier K.isOpen.measurableSet)
    K.bodyUniform (coordinateHitAndRun_stationary K)

/-- Exact conjugacy, including the null-set transport needed inside kernel integrals. -/
theorem coordinateNativeOperator_conjugate (f : Lp ℝ 2 (K.ambient.restrict K.carrier)) :
    coordinateNativeOperator K (K.bodyL2Isometry f) = K.bodyL2Isometry (coordinateHeatBath K f) := by
  apply Lp.ext
  have hn := DikinD2.NativeL2.operator_ae (coordinateHitAndRun_stationary K) (K.bodyL2Isometry f)
  have he := MarkovProcess.kernelIntegral_congr_ae (coordinateHitAndRun_stationary K).le
    (K.bodyL2Isometry_coe f)
  exact hn.trans (he.trans (coordinateHeatBath_bodyKernel_ae K f).symm)

theorem coordinateNativeOperator_symmetric : (coordinateNativeOperator K).IsSymmetric := by
  intro f g
  obtain ⟨u, rfl⟩ := K.bodyL2Isometry_surjective f
  obtain ⟨v, rfl⟩ := K.bodyL2Isometry_surjective g
  change inner ℝ (coordinateNativeOperator K (K.bodyL2Isometry u)) (K.bodyL2Isometry v) =
    inner ℝ (K.bodyL2Isometry u) (coordinateNativeOperator K (K.bodyL2Isometry v))
  rw [coordinateNativeOperator_conjugate, coordinateNativeOperator_conjugate,
    K.bodyL2Isometry.inner_map_map, K.bodyL2Isometry.inner_map_map]
  exact coordinateAverage_symmetric coordinateSigma coordinateSigma_le u v

theorem coordinateNativeOperator_positive : (coordinateNativeOperator K).IsPositive := by
  refine ⟨coordinateNativeOperator_symmetric K, ?_⟩
  intro f
  obtain ⟨u, rfl⟩ := K.bodyL2Isometry_surjective f
  change 0 ≤ inner ℝ (coordinateNativeOperator K (K.bodyL2Isometry u)) (K.bodyL2Isometry u)
  rw [real_inner_comm, coordinateNativeOperator_conjugate, K.bodyL2Isometry.inner_map_map]
  exact coordinateAverage_positive coordinateSigma coordinateSigma_le u

end HitAndRun.Markov
