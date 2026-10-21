module
public import HitAndRun.Markov.CoordinateKernelIdentificationTransport
@[expose] public section

namespace HitAndRun.Markov
open Set MeasureTheory ProbabilityTheory HitAndRun.Geometry HitAndRun.Sobolev
open scoped ENNReal ProbabilityTheory
variable {n : ℕ} (i : Fin n)

/-- Actual uniform-chord transitions integrate every globally integrable function almost everywhere. -/
theorem integrable_coordinateChord_ae {K : Set (EuclideanSpace ℝ (Fin n))}
    (ho : IsOpen K) (hne : K.Nonempty) (hb : Bornology.IsBounded K)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Integrable f (uniformMeasure K)) :
    ∀ᵐ x ∂uniformMeasure K,
      Integrable f (chordLaw K x (EuclideanSpace.basisFun (Fin n) ℝ i)) := by
  letI := uniformMeasure_isProbabilityMeasure ho hne hb
  let X : EuclideanSpace ℝ (Fin n) → OtherCoordinates i := fun x => (coordinateChart i x).1
  let Y : EuclideanSpace ℝ (Fin n) → ℝ := fun x => (coordinateChart i x).2
  have hX : Measurable X := measurable_fst.comp (coordinateChart i).measurable
  have hY : Measurable Y := measurable_snd.comp (coordinateChart i).measurable
  have hpair : (fun x => (X x, Y x)) = coordinateChart i := rfl
  have hfi : Integrable (fun z => f (coordinateInsert i z))
      ((uniformMeasure K).map (fun x => (X x, Y x))) := by
    rw [hpair, integrable_map_equiv]
    simpa only [Function.comp_def, coordinateInsert_apply, MeasurableEquiv.symm_apply_apply] using hf
  have hi := hfi.condDistrib_ae hX.aemeasurable hY.aemeasurable
  have hk := condDistrib_eq_normalizedSection
    ((volume K)⁻¹ • (volume : Measure (OtherCoordinates i))) (volume : Measure ℝ)
    (uniformMeasure K) X Y hX hY (coordinateBody i K) (coordinateBody_measurable i ho.measurableSet)
    (by simpa only [hpair] using coordinateChart_uniform i K)
    (coordinateBody_finite_sections i hb)
  have hk' := ae_of_ae_map hX.aemeasurable hk
  filter_upwards [hi, hk'] with x hix hkx
  rw [hkx] at hix
  rw [chordLaw_eq_coordinateSliceLaw, coordinateSliceLaw,
    (coordinateFiber_isometry i (coordinateChart i x).1).isClosedEmbedding.measurableEmbedding.integrable_map_iff]
  exact hix

end HitAndRun.Markov
