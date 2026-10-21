module
public import HitAndRun.Markov.DirectionalKernelIdentificationTransport
@[expose] public section

namespace HitAndRun.Markov
open Set MeasureTheory ProbabilityTheory HitAndRun.Geometry HitAndRun.Sobolev
open scoped ENNReal ProbabilityTheory
variable {n : ℕ} [NeZero n] (θ : UnitDirection n)

/-- Actual uniform-chord transitions integrate every globally integrable function almost everywhere. -/
theorem integrable_directionalChord_ae {K : Set (EuclideanSpace ℝ (Fin n))}
    (ho : IsOpen K) (hne : K.Nonempty) (hb : Bornology.IsBounded K)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Integrable f (uniformMeasure K)) :
    ∀ᵐ x ∂uniformMeasure K,
      Integrable f (chordLaw K x θ) := by
  letI := uniformMeasure_isProbabilityMeasure ho hne hb
  let X : EuclideanSpace ℝ (Fin n) → OtherCoordinates (0 : Fin n) := fun x => (directionalChart θ x).1
  let Y : EuclideanSpace ℝ (Fin n) → ℝ := fun x => (directionalChart θ x).2
  have hX : Measurable X := measurable_fst.comp (directionalChart θ).measurable
  have hY : Measurable Y := measurable_snd.comp (directionalChart θ).measurable
  have hpair : (fun x => (X x, Y x)) = directionalChart θ := rfl
  have hfi : Integrable (fun z => f (directionalInsert θ z))
      ((uniformMeasure K).map (fun x => (X x, Y x))) := by
    rw [hpair, integrable_map_equiv]
    simpa only [Function.comp_def, ← directionalChart_symm, MeasurableEquiv.symm_apply_apply] using hf
  have hi := hfi.condDistrib_ae hX.aemeasurable hY.aemeasurable
  have hk := condDistrib_eq_normalizedSection
    ((volume K)⁻¹ • (volume : Measure (OtherCoordinates (0 : Fin n)))) (volume : Measure ℝ)
    (uniformMeasure K) X Y hX hY (directionalBody θ K) (directionalBody_measurable θ ho.measurableSet)
    (by simpa only [hpair] using directionalChart_uniform θ K)
    (directionalBody_finite_sections θ hb)
  have hk' := ae_of_ae_map hX.aemeasurable hk
  filter_upwards [hi, hk'] with x hix hkx
  rw [hkx] at hix
  rw [chordLaw_eq_directionalSliceLaw,
    (directionRotation θ).isometry.isClosedEmbedding.measurableEmbedding.integrable_map_iff,
    coordinateSliceLaw,
    (coordinateFiber_isometry (0 : Fin n) (directionalChart θ x).1).isClosedEmbedding.measurableEmbedding.integrable_map_iff]
  exact hix

end HitAndRun.Markov
