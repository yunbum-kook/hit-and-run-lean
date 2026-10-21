module
public import HitAndRun.Markov.CoordinateKernel
public import HitAndRun.Markov.CoordinateAnnihilationTest
public import Mathlib.MeasureTheory.Group.Measure
@[expose] public section

/-! Exact coordinate disintegration of the actual chord law. -/
namespace HitAndRun.Markov
open Set MeasureTheory HitAndRun.Geometry
open scoped ENNReal
variable {n : ℕ} (i : Fin n)

/-- An absolute-coordinate slice, as opposed to a displacement from the current point. -/
def coordinateSlice (K : Set (EuclideanSpace ℝ (Fin n))) (a : OtherCoordinates i) : Set ℝ :=
  {t | coordinateInsert i (a, t) ∈ K}

noncomputable def coordinateSliceLaw (K : Set (EuclideanSpace ℝ (Fin n)))
    (a : OtherCoordinates i) : Measure (EuclideanSpace ℝ (Fin n)) :=
  ((volume (coordinateSlice i K a))⁻¹ • volume.restrict (coordinateSlice i K a)).map
    (fun t => coordinateInsert i (a, t))

theorem coordinateInsert_line (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    coordinateInsert i ((coordinateChart i x).1, x i + t) =
      x + t • EuclideanSpace.basisFun (Fin n) ℝ i := by
  apply PiLp.ext
  intro j
  by_cases hj : j = i
  · subst j
    calc
      _ = x i + t := coordinateInsert_at i ((coordinateChart i x).1, x i + t)
      _ = _ := by simp [EuclideanSpace.basisFun_apply]
  · have h := coordinateInsert_other i ((coordinateChart i x).1, x i + t) ⟨j, hj⟩
    simpa [EuclideanSpace.basisFun_apply, hj, PiLp.add_apply, PiLp.smul_apply] using h

theorem lineChord_eq_coordinateSlice_preimage (K : Set (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) :
    lineChord K x (EuclideanSpace.basisFun (Fin n) ℝ i) =
      (fun t : ℝ => x i + t) ⁻¹' coordinateSlice i K (coordinateChart i x).1 := by
  ext t
  simp only [mem_preimage, coordinateSlice, mem_ofPred_eq, coordinateInsert_line, lineChord]

theorem lineChord_volume_eq_coordinateSlice (K : Set (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) :
    volume (lineChord K x (EuclideanSpace.basisFun (Fin n) ℝ i)) =
      volume (coordinateSlice i K (coordinateChart i x).1) := by
  rw [lineChord_eq_coordinateSlice_preimage]
  exact measure_preimage_add volume (x i) _

theorem coordinateSliceLaw_apply (K : Set (EuclideanSpace ℝ (Fin n)))
    (a : OtherCoordinates i) {A : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A) :
    coordinateSliceLaw i K a A = (volume (coordinateSlice i K a))⁻¹ *
      volume ((fun t => coordinateInsert i (a, t)) ⁻¹' A ∩ coordinateSlice i K a) := by
  have hm : Measurable (fun t : ℝ => coordinateInsert i (a, t)) :=
    (coordinateInsert i).continuous.measurable.comp (measurable_const.prodMk measurable_id)
  rw [coordinateSliceLaw, Measure.map_apply hm hA, Measure.smul_apply,
    Measure.restrict_apply (hA.preimage hm)]
  rfl

/-- Translation invariance removes the current i-th coordinate from the actual transition law. -/
theorem chordLaw_eq_coordinateSliceLaw (K : Set (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) :
    chordLaw K x (EuclideanSpace.basisFun (Fin n) ℝ i) =
      coordinateSliceLaw i K (coordinateChart i x).1 := by
  ext A hA
  rw [chordLaw_apply _ _ _ hA, coordinateSliceLaw_apply _ _ _ hA,
    lineChord_volume_eq_coordinateSlice]
  congr 1
  rw [lineChord_eq_coordinateSlice_preimage]
  have he : (fun t : ℝ => x + t • EuclideanSpace.basisFun (Fin n) ℝ i) ⁻¹' A ∩
      (fun t : ℝ => x i + t) ⁻¹' coordinateSlice i K (coordinateChart i x).1 =
      (fun t : ℝ => x i + t) ⁻¹'
        ((fun t => coordinateInsert i ((coordinateChart i x).1, t)) ⁻¹' A ∩
          coordinateSlice i K (coordinateChart i x).1) := by
    ext t
    simp only [mem_inter_iff, mem_preimage, coordinateInsert_line]
  rw [he, measure_preimage_add]

end HitAndRun.Markov
