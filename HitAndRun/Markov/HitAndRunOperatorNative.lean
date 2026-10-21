module
public import HitAndRun.Markov.HitAndRunOperatorFamily
public import HitAndRun.Markov.HitAndRunOperatorStationary
public import HitAndRun.Markov.HitAndRunOperatorFubini
public import HitAndRun.Markov.CoordinateKernelIdentificationReversible
@[expose] public section
namespace HitAndRun.Markov
open MeasureTheory ProbabilityTheory HitAndRun.Geometry HitAndRun.Sobolev
open scoped ENNReal ProbabilityTheory RealInnerProductSpace
variable {n : ℕ} [NeZero n] (K : BoundedOpenDomain n)
local instance : IsMarkovKernel (hitAndRun K.carrier K.isOpen K.isBounded) :=
  hitAndRun_markov K.isOpen K.isBounded

noncomputable def hitAndRunNativeOperator : Lp ℝ 2 K.bodyUniform →L[ℝ] Lp ℝ 2 K.bodyUniform :=
  DikinD2.NativeL2.operator (hitAndRun K.carrier K.isOpen K.isBounded) K.bodyUniform (hitAndRun_stationary K)

theorem directionalBodyProjection_representative
    (g : Lp ℝ 2 (K.ambient.restrict K.carrier)) (θ : UnitDirection n) :
    K.bodyL2Isometry (conditionalProjection (directionalSigma_le θ) g) =ᵐ[K.bodyUniform]
      fun x => ∫ y, K.bodyL2Isometry g y ∂randomDirectionKernel K.carrier K.isOpen.measurableSet (x, θ) := by
  have he := MarkovProcess.kernelIntegral_congr_ae (directionalKernel_stationary K θ).le
    (K.bodyL2Isometry_coe g)
  exact (directionalProjection_bodyKernel_ae K θ g).trans he.symm

/-- The native integral operator is exactly spherical averaging of genuine directional projections. -/
theorem hitAndRunNativeOperator_inner_average
    (f g : Lp ℝ 2 (K.ambient.restrict K.carrier)) :
    inner ℝ (K.bodyL2Isometry f) (hitAndRunNativeOperator K (K.bodyL2Isometry g)) =
      ∫ θ, inner ℝ f (conditionalProjection (directionalSigma_le θ) g) ∂uniformSphere n := by
  letI := uniformSphere_probability n
  let v := fun θ : UnitDirection n => K.bodyL2Isometry (conditionalProjection (directionalSigma_le θ) g)
  let a := fun p : UnitDirection n × K.carrier =>
    ∫ y, K.bodyL2Isometry g y ∂randomDirectionKernel K.carrier K.isOpen.measurableSet (p.2, p.1)
  have ha : StronglyMeasurable a :=
    ((Lp.stronglyMeasurable (K.bodyL2Isometry g)).integral_kernel
      (κ := randomDirectionKernel K.carrier K.isOpen.measurableSet)).comp_measurable measurable_swap
  have hb (θ : UnitDirection n) : ‖v θ‖ ≤ ‖g‖ := by
    rw [show v θ = K.bodyL2Isometry (conditionalProjection (directionalSigma_le θ) g) from rfl,
      K.bodyL2Isometry.norm_map]
    exact norm_condExpL2_le (directionalSigma_le θ) g
  have hav := integral_inner_L2_representatives (uniformSphere n) K.bodyUniform v a ha
    (directionalBodyProjection_representative K g) ‖g‖ hb (K.bodyL2Isometry f)
  have hi : Integrable (K.bodyL2Isometry g) (hitAndRun K.carrier K.isOpen K.isBounded ∘ₘ K.bodyUniform) := by
    rw [hitAndRun_stationary]
    exact (Lp.memLp (K.bodyL2Isometry g)).integrable (by norm_num)
  have hia := Measure.ae_integrable_of_integrable_comp hi
  have hn := DikinD2.NativeL2.operator_ae (hitAndRun_stationary K) (K.bodyL2Isometry g)
  calc
    _ = ∫ x, K.bodyL2Isometry f x * (∫ θ, a (θ, x) ∂uniformSphere n) ∂K.bodyUniform := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hn, hia] with x hx hix
      rw [Real.inner_apply, hitAndRunNativeOperator, hx, hitAndRun_integral_direction K x _ hix]
    _ = ∫ θ, inner ℝ (K.bodyL2Isometry f) (v θ) ∂uniformSphere n := hav.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with θ
      exact K.bodyL2Isometry.inner_map_map f _
end HitAndRun.Markov
