module
public import HitAndRun.Markov.HitAndRunOperatorMeasurable
public import HitAndRun.Markov.DirectionalKernelIdentificationL2
public import HitAndRun.Markov.HitAndRunKernel
public import HitAndRun.Markov.SphereCertificateEnergy
public import Mathlib.Probability.Kernel.MeasurableIntegral
@[expose] public section

namespace HitAndRun.Markov
open MeasureTheory ProbabilityTheory HitAndRun.Geometry HitAndRun.Sobolev
open scoped ENNReal RealInnerProductSpace
variable {n : ℕ} [NeZero n] (K : BoundedOpenDomain n)

/-- The actual chord integral is jointly strongly measurable in direction and body point. -/
theorem directionalBodyAction_stronglyMeasurable
    (f : Lp ℝ 2 (K.ambient.restrict K.carrier)) :
    StronglyMeasurable (fun p : UnitDirection n × K.carrier =>
      ∫ y : K.carrier, f y.val ∂randomDirectionKernel K.carrier K.isOpen.measurableSet (p.2, p.1)) := by
  have hf := (Lp.stronglyMeasurable f).comp_measurable
    (measurable_subtype_coe : Measurable (Subtype.val : K.carrier → EuclideanSpace ℝ (Fin n)))
  exact (hf.integral_kernel (κ := randomDirectionKernel K.carrier K.isOpen.measurableSet)).comp_measurable
    measurable_swap

/-- The genuine directional conditional projections form a strongly measurable L2 family. -/
theorem directionalProjection_stronglyMeasurable
    (f : Lp ℝ 2 (K.ambient.restrict K.carrier)) :
    StronglyMeasurable (fun θ : UnitDirection n => conditionalProjection (directionalSigma_le θ) f) := by
  have hb : StronglyMeasurable (fun θ : UnitDirection n =>
      K.bodyL2Isometry (conditionalProjection (directionalSigma_le θ) f)) := by
    apply stronglyMeasurable_L2_of_representatives K.bodyUniform _ _
      (directionalBodyAction_stronglyMeasurable K f)
    intro θ
    exact directionalProjection_bodyKernel_ae K θ f
  have he := K.bodyL2Equiv.symm.continuous.comp_stronglyMeasurable hb
  simpa only [← BoundedOpenDomain.bodyL2Equiv_apply, LinearIsometryEquiv.symm_apply_apply] using he

/-- Projection residuals are contractive, with no measurability assumption. -/
theorem conditionalProjection_residual_norm_le {A : Type*} {m m0 : MeasurableSpace A}
    {μ : @Measure A m0} (hm : m ≤ m0) (f : Lp ℝ 2 μ) :
    ‖f - conditionalProjection hm f‖ ≤ ‖f‖ := by
  have he := conditionalProjection_residual_energy hm f
  have hp := conditionalProjection_positive hm f
  rw [inner_sub_right, real_inner_self_eq_norm_sq] at he
  nlinarith [norm_nonneg (f - conditionalProjection hm f), norm_nonneg f]

/-- Discharges the L2-family premise in the analytic HAR certificate theorem. -/
theorem directionalResidual_memLp (f : Lp ℝ 2 (K.ambient.restrict K.carrier)) :
    MemLp (directionalResidual K f) 2 (uniformSphere n) := by
  letI := uniformSphere_probability n
  have hs : StronglyMeasurable (directionalResidual K f) :=
    stronglyMeasurable_const.sub (directionalProjection_stronglyMeasurable K f)
  exact (memLp_top_of_bound hs.aestronglyMeasurable ‖f‖
    (Filter.Eventually.of_forall (fun θ => conditionalProjection_residual_norm_le (directionalSigma_le θ) f))).mono_exponent le_top

end HitAndRun.Markov
