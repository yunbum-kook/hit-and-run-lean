module
public import HitAndRun.Markov.CoordinateKernelIdentificationStationary
public import HitAndRun.Markov.DirectionalKernelIdentificationL2
public import HitAndRun.Markov.HitAndRunKernel
@[expose] public section
namespace HitAndRun.Markov
open Set MeasureTheory ProbabilityTheory HitAndRun.Geometry HitAndRun.Sobolev
open scoped ENNReal ProbabilityTheory
variable {n : ℕ} [NeZero n] (K : BoundedOpenDomain n)
/-- Each genuine fixed-direction transition preserves the actual subtype uniform probability. -/
theorem directionalKernel_stationary (θ : UnitDirection n) :
    directionKernel K.carrier K.isOpen.measurableSet
      θ
      (by simpa only [Metric.mem_sphere, dist_zero_right] using θ.property) ∘ₘ K.bodyUniform = K.bodyUniform := by
  let κ := directionKernel K.carrier K.isOpen.measurableSet
    θ
    (by simpa only [Metric.mem_sphere, dist_zero_right] using θ.property)
  letI : IsMarkovKernel κ := directionKernel_markov K.isOpen K.isBounded _ _
  letI := uniformMeasure_isProbabilityMeasure K.isOpen K.nonempty K.isBounded
  let emb := MeasurableEmbedding.subtype_coe K.isOpen.measurableSet
  apply emb.map_injective
  rw [K.bodyUniform_map]
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [emb.integral_map]
  have hf : Integrable (fun y : K.carrier => f y.val) (κ ∘ₘ K.bodyUniform) :=
    emb.integrable_map_iff.1 (f.integrable ((κ ∘ₘ K.bodyUniform).map Subtype.val))
  rw [integral_measure_kernel_comp K.bodyUniform κ _ hf]
  dsimp only [κ]
  simp_rw [directionKernel_integral_subtype K.isOpen K.isBounded]
  have hmp : MeasurePreserving (Subtype.val : K.carrier → EuclideanSpace ℝ (Fin n))
      K.bodyUniform (uniformMeasure K.carrier) :=
    ⟨measurable_subtype_coe, K.bodyUniform_map⟩
  rw [hmp.integral_comp emb (fun x => ∫ y, f y ∂chordLaw K.carrier x
    θ)]
  exact directionalChord_integral_preserved K θ f (f.integrable _)


/-- The real random-direction transition preserves the real uniform law. -/
theorem hitAndRun_stationary :
    hitAndRun K.carrier K.isOpen K.isBounded ∘ₘ K.bodyUniform = K.bodyUniform := by
  letI := uniformSphere_probability n
  letI := randomDirectionKernel_markov K.isOpen K.isBounded
  rw [hitAndRun, ← Measure.comp_assoc, ← Measure.compProd_eq_comp_prod, Measure.compProd_const]
  ext S hS
  rw [Measure.bind_apply hS (randomDirectionKernel K.carrier K.isOpen.measurableSet).aemeasurable]
  rw [lintegral_prod_symm' _ ((randomDirectionKernel K.carrier K.isOpen.measurableSet).measurable_coe hS)]
  have hi (θ : UnitDirection n) :
      (∫⁻ x, randomDirectionKernel K.carrier K.isOpen.measurableSet (x, θ) S ∂K.bodyUniform) = K.bodyUniform S := by
    have hs := congrArg (fun μ : Measure K.carrier => μ S) (directionalKernel_stationary K θ)
    rw [Measure.bind_apply hS (directionKernel K.carrier K.isOpen.measurableSet θ _).aemeasurable] at hs
    exact hs
  simp_rw [hi]
  simp

/-- The kernel definition is exactly a mixture of actual fixed-direction laws. -/
theorem hitAndRun_integral_direction (x : K.carrier) (f : K.carrier → ℝ)
    (hf : Integrable f (hitAndRun K.carrier K.isOpen K.isBounded x)) :
    (∫ y, f y ∂hitAndRun K.carrier K.isOpen K.isBounded x) =
      ∫ θ, (∫ y, f y ∂randomDirectionKernel K.carrier K.isOpen.measurableSet (x, θ))
        ∂uniformSphere n := by
  letI := uniformSphere_probability n
  letI := randomDirectionKernel_markov K.isOpen K.isBounded
  let κ := (randomDirectionKernel K.carrier K.isOpen.measurableSet).comap
    (fun θ : UnitDirection n => (x, θ)) measurable_prodMk_left
  have he : hitAndRun K.carrier K.isOpen K.isBounded x = κ ∘ₘ uniformSphere n := by
    ext S hS
    rw [hitAndRun, Kernel.comp_apply' _ _ _ hS,
      Kernel.lintegral_id_prod ((randomDirectionKernel K.carrier K.isOpen.measurableSet).measurable_coe hS),
      Measure.bind_apply hS κ.aemeasurable]
    rfl
  rw [he] at hf ⊢
  exact integral_measure_kernel_comp (uniformSphere n) κ f hf
end HitAndRun.Markov
