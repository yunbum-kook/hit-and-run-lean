module
public import HitAndRun.Markov.DirectionalKernelIdentification
public import HitAndRun.Markov.DirectionalAnnihilationCertificate
@[expose] public section

namespace HitAndRun.Markov
open Set MeasureTheory ProbabilityTheory HitAndRun.Geometry HitAndRun.Sobolev
open scoped ENNReal ProbabilityTheory
variable {n : ℕ} [NeZero n] (θ : UnitDirection n)

/-- On the actual uniform body law, every directional chord average is conditional
expectation onto the actual orthogonal projection to θ-perpendicular. -/
theorem condExp_eq_directionalChord {K : Set (EuclideanSpace ℝ (Fin n))}
    (ho : IsOpen K) (hne : K.Nonempty) (hb : Bornology.IsBounded K)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Integrable f (uniformMeasure K)) :
    (uniformMeasure K)[f | directionalSigma θ] =ᵐ[uniformMeasure K]
      fun x => ∫ y, f y ∂chordLaw K x θ := by
  letI := uniformMeasure_isProbabilityMeasure ho hne hb
  let X : EuclideanSpace ℝ (Fin n) → OtherCoordinates (0 : Fin n) :=
    fun x => (directionalChart θ x).1
  let Y : EuclideanSpace ℝ (Fin n) → ℝ := fun x => (directionalChart θ x).2
  have hX : Measurable X := measurable_fst.comp (directionalChart θ).measurable
  have hY : Measurable Y := measurable_snd.comp (directionalChart θ).measurable
  have hpair : (fun x => (X x, Y x)) = directionalChart θ := rfl
  have hfi : Integrable (fun z => f (directionalInsert θ z))
      ((uniformMeasure K).map (fun x => (X x, Y x))) := by
    rw [hpair, integrable_map_equiv]
    simpa only [Function.comp_def, ← directionalChart_symm, MeasurableEquiv.symm_apply_apply] using hf
  have hc := condExp_eq_normalizedSection
    ((volume K)⁻¹ • (volume : Measure (OtherCoordinates (0 : Fin n)))) (volume : Measure ℝ)
    (uniformMeasure K) X Y hX hY (directionalBody θ K) (directionalBody_measurable θ ho.measurableSet)
    (by simpa only [hpair] using directionalChart_uniform θ K)
    (directionalBody_finite_sections θ hb) (fun z => f (directionalInsert θ z)) hfi
  have hleft : (fun x => f (directionalInsert θ (X x, Y x))) = f := by
    funext x
    change f ((directionalChart θ).symm (directionalChart θ x)) = f x
    rw [MeasurableEquiv.symm_apply_apply]
  rw [hleft] at hc
  change (uniformMeasure K)[f | MeasurableSpace.comap (fun x => (directionalChart θ x).1) _] =ᵐ[uniformMeasure K] _ at hc
  rw [← directionalChart_sigma θ]
  refine hc.trans (Filter.Eventually.of_forall (fun x => ?_))
  dsimp only
  rw [chordLaw_eq_directionalSliceLaw,
    (directionRotation θ).isometry.isClosedEmbedding.measurableEmbedding.integral_map,
    coordinateSliceLaw,
    (coordinateFiber_isometry (0 : Fin n) (directionalChart θ x).1).isClosedEmbedding.measurableEmbedding.integral_map]
  rfl

end HitAndRun.Markov
