module
public import HitAndRun.Markov.HitAndRunOperatorNative
@[expose] public section
namespace HitAndRun.Markov
open MeasureTheory HitAndRun.Geometry HitAndRun.Sobolev
open scoped RealInnerProductSpace
variable {n : ℕ} [NeZero n] (K : BoundedOpenDomain n)

/-- The actual native HAR operator transported to the paper's ambient uniform L2 carrier. -/
noncomputable def hitAndRunOperator :
    Lp ℝ 2 (K.ambient.restrict K.carrier) →L[ℝ] Lp ℝ 2 (K.ambient.restrict K.carrier) :=
  K.bodyL2Equiv.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((hitAndRunNativeOperator K).comp K.bodyL2Equiv.toContinuousLinearEquiv.toContinuousLinearMap)

theorem hitAndRunOperator_body (f : Lp ℝ 2 (K.ambient.restrict K.carrier)) :
    K.bodyL2Isometry (hitAndRunOperator K f) = hitAndRunNativeOperator K (K.bodyL2Isometry f) := by
  change K.bodyL2Equiv (K.bodyL2Equiv.symm _) = _
  exact K.bodyL2Equiv.apply_symm_apply _

theorem hitAndRunOperator_inner_average (f g : Lp ℝ 2 (K.ambient.restrict K.carrier)) :
    inner ℝ f (hitAndRunOperator K g) =
      ∫ θ, inner ℝ f (conditionalProjection (directionalSigma_le θ) g) ∂uniformSphere n := by
  rw [← K.bodyL2Isometry.inner_map_map, hitAndRunOperator_body]
  exact hitAndRunNativeOperator_inner_average K f g

/-- Exact Dirichlet energy of the actual kernel is averaged squared directional residual energy. -/
theorem hitAndRunOperator_energy (f : Lp ℝ 2 (K.ambient.restrict K.carrier)) :
    inner ℝ f (f - hitAndRunOperator K f) =
      ∫ θ, ‖directionalResidual K f θ‖ ^ 2 ∂uniformSphere n := by
  letI := uniformSphere_probability n
  have hp : Integrable (fun θ : UnitDirection n => conditionalProjection (directionalSigma_le θ) f)
      (uniformSphere n) := by
    apply (integrable_const ‖f‖).mono' (directionalProjection_stronglyMeasurable K f).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun θ => norm_condExpL2_le (directionalSigma_le θ) f)
  rw [inner_sub_right, hitAndRunOperator_inner_average]
  calc
    _ = ∫ θ : UnitDirection n, inner ℝ f f - inner ℝ f (conditionalProjection (directionalSigma_le θ) f)
        ∂uniformSphere n := by
      rw [integral_sub (integrable_const _) (hp.const_inner f), integral_const]
      simp
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with θ
      rw [← inner_sub_right]
      exact conditionalProjection_residual_energy (directionalSigma_le θ) f
end HitAndRun.Markov
