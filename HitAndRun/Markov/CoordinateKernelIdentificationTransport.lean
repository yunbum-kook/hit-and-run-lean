module
public import HitAndRun.Markov.CoordinateKernelIdentification
public import HitAndRun.Markov.CoordinateKernelIdentificationDisintegration
public import HitAndRun.Sobolev.UniformMeasure
@[expose] public section

namespace HitAndRun.Markov
open Set MeasureTheory ProbabilityTheory HitAndRun.Geometry HitAndRun.Sobolev
open scoped ENNReal ProbabilityTheory
variable {n : ℕ} (i : Fin n)

/-- The body's literal pullback to coordinate-product space. -/
def coordinateBody (K : Set (EuclideanSpace ℝ (Fin n))) : Set (OtherCoordinates i × ℝ) :=
  (coordinateInsert i) ⁻¹' K

theorem coordinateBody_measurable {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) : MeasurableSet (coordinateBody i K) :=
  hK.preimage (coordinateInsert i).continuous.measurable

theorem coordinateChart_preimage_body (K : Set (EuclideanSpace ℝ (Fin n))) :
    (coordinateChart i) ⁻¹' coordinateBody i K = K := by
  ext x
  simp [coordinateBody]

/-- The uniform body law becomes exactly restricted product volume in the verified chart. -/
theorem coordinateChart_uniform (K : Set (EuclideanSpace ℝ (Fin n))) :
    (uniformMeasure K).map (coordinateChart i) =
      (((volume K)⁻¹ • (volume : Measure (OtherCoordinates i))).prod volume).restrict
        (coordinateBody i K) := by
  rw [uniformMeasure, Measure.map_smul, Measure.prod_smul_left, Measure.restrict_smul]
  congr 1
  have hm := (coordinateChart_volume i).map_eq
  rw [← hm, (coordinateChart i).restrict_map, coordinateChart_preimage_body]
  exact (coordinateChart i).measurable.aemeasurable

theorem coordinateBody_finite_sections {K : Set (EuclideanSpace ℝ (Fin n))}
    (hb : Bornology.IsBounded K) (a : OtherCoordinates i) :
    volume (Prod.mk a ⁻¹' coordinateBody i K) ≠ ⊤ := by
  let x := coordinateInsert i (a, 0)
  have h := (lineChord_bounded hb x (EuclideanSpace.basisFun (Fin n) ℝ i)
    ((EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one i)).measure_lt_top (μ := volume)
  rw [lineChord_volume_eq_coordinateSlice i K x] at h
  change volume (coordinateSlice i K a) ≠ ⊤
  simpa only [x, coordinateInsert_apply, MeasurableEquiv.apply_symm_apply] using ne_of_lt h

theorem coordinateFiber_isometry (a : OtherCoordinates i) :
    Isometry (fun t : ℝ => coordinateInsert i (a, t)) := by
  have he : (fun t : ℝ => coordinateInsert i (a, t)) =
      (fun t => coordinateInsert i (a, 0) + t • EuclideanSpace.basisFun (Fin n) ℝ i) := by
    funext t
    have h := coordinateInsert_line i (coordinateInsert i (a, 0)) t
    rw [coordinateInsert_at, zero_add] at h
    simpa only [coordinateInsert_apply, MeasurableEquiv.apply_symm_apply] using h
  rw [he]
  exact line_isometry _ _ ((EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one i)

/-- On the actual uniform body law, coordinate chord integration is conditional expectation. -/
theorem condExp_eq_coordinateChord {K : Set (EuclideanSpace ℝ (Fin n))}
    (ho : IsOpen K) (hne : K.Nonempty) (hb : Bornology.IsBounded K)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Integrable f (uniformMeasure K)) :
    (uniformMeasure K)[f | coordinateSigma i] =ᵐ[uniformMeasure K]
      fun x => ∫ y, f y ∂chordLaw K x (EuclideanSpace.basisFun (Fin n) ℝ i) := by
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
  have hc := condExp_eq_normalizedSection
    ((volume K)⁻¹ • (volume : Measure (OtherCoordinates i))) (volume : Measure ℝ)
    (uniformMeasure K) X Y hX hY (coordinateBody i K) (coordinateBody_measurable i ho.measurableSet)
    (by simpa only [hpair] using coordinateChart_uniform i K)
    (coordinateBody_finite_sections i hb) (fun z => f (coordinateInsert i z)) hfi
  have hleft : (fun x => f (coordinateInsert i (X x, Y x))) = f := by
    funext x
    change f ((coordinateChart i).symm (coordinateChart i x)) = f x
    rw [MeasurableEquiv.symm_apply_apply]
  rw [hleft] at hc
  change (uniformMeasure K)[f | coordinateSigma i] =ᵐ[uniformMeasure K] _ at hc
  refine hc.trans (Filter.Eventually.of_forall (fun x => ?_))
  dsimp only
  rw [chordLaw_eq_coordinateSliceLaw, coordinateSliceLaw]
  rw [(coordinateFiber_isometry i (coordinateChart i x).1).isClosedEmbedding.measurableEmbedding.integral_map]
  rfl

end HitAndRun.Markov
