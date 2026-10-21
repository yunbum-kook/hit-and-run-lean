module
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.Normed.Module.FiniteDimension
@[expose] public section

/-! Volume-preserving deletion of one Euclidean coordinate. -/
namespace HitAndRun.Markov
open MeasureTheory

abbrev OtherCoordinates {n : ℕ} (i : Fin n) := {j : Fin n // j ≠ i} → ℝ

instance remainingUnique {n : ℕ} (i : Fin n) :
    Unique {j : Fin n // ¬ j ≠ i} where
  default := ⟨i, by simp⟩
  uniq j := Subtype.ext (Classical.not_not.mp j.property)

/-- The first component retains precisely every coordinate other than i. -/
noncomputable def coordinateChart {n : ℕ} (i : Fin n) :
    EuclideanSpace ℝ (Fin n) ≃ᵐ OtherCoordinates i × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm |>.trans
    ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ) (fun j => j ≠ i)).trans
      ((MeasurableEquiv.refl _).prodCongr
        (MeasurableEquiv.funUnique {j : Fin n // ¬ j ≠ i} ℝ)))

@[simp] theorem coordinateChart_fst {n : ℕ} (i : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) (j : {j : Fin n // j ≠ i}) :
    (coordinateChart i x).1 j = x j := rfl

@[simp] theorem coordinateChart_snd {n : ℕ} (i : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) : (coordinateChart i x).2 = x i := rfl

/-- No Jacobian constant is lost when deleting a coordinate. -/
theorem coordinateChart_volume {n : ℕ} (i : Fin n) :
    MeasurePreserving (coordinateChart i) volume (volume.prod volume) := by
  apply (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n)).trans
  apply (volume_preserving_piEquivPiSubtypeProd (fun _ : Fin n => ℝ) (fun j => j ≠ i)).trans
  convert (MeasurePreserving.id (volume : Measure (OtherCoordinates i))).prod
    (volume_preserving_funUnique {j : Fin n // ¬ j ≠ i} ℝ) using 1
  · rfl
  · simp only [Measure.volume_eq_prod]
    congr 3
    exact Subsingleton.elim _ _

/-- Insertion is a genuine continuous linear map, hence smooth. -/
noncomputable def coordinateInsert {n : ℕ} (i : Fin n) :
    OtherCoordinates i × ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearMap.toContinuousLinearMap
    { toFun := (coordinateChart i).symm
      map_add' := by
        intro x y
        apply PiLp.ext
        intro j
        by_cases h : j = i
        · subst j
          simp [coordinateChart, MeasurableEquiv.piEquivPiSubtypeProd,
            Equiv.piEquivPiSubtypeProd, MeasurableEquiv.prodCongr,
            MeasurableEquiv.funUnique, MeasurableEquiv.piUnique]
        · simp [coordinateChart, MeasurableEquiv.piEquivPiSubtypeProd,
            Equiv.piEquivPiSubtypeProd, MeasurableEquiv.prodCongr,
            MeasurableEquiv.funUnique, MeasurableEquiv.piUnique, h]
      map_smul' := by
        intro c x
        apply PiLp.ext
        intro j
        by_cases h : j = i
        · subst j
          simp [coordinateChart, MeasurableEquiv.piEquivPiSubtypeProd,
            Equiv.piEquivPiSubtypeProd, MeasurableEquiv.prodCongr,
            MeasurableEquiv.funUnique, MeasurableEquiv.piUnique]
        · simp [coordinateChart, MeasurableEquiv.piEquivPiSubtypeProd,
            Equiv.piEquivPiSubtypeProd, MeasurableEquiv.prodCongr,
            MeasurableEquiv.funUnique, MeasurableEquiv.piUnique, h] }

@[simp] theorem coordinateInsert_apply {n : ℕ} (i : Fin n) (z : OtherCoordinates i × ℝ) :
    coordinateInsert i z = (coordinateChart i).symm z := rfl

/-- The exact conditioning sigma algebra, not an abstract projection parameter. -/
noncomputable def coordinateSigma {n : ℕ} (i : Fin n) : MeasurableSpace (EuclideanSpace ℝ (Fin n)) :=
  MeasurableSpace.comap (fun x : EuclideanSpace ℝ (Fin n) => (coordinateChart i x).1)
    inferInstance

theorem coordinateSigma_le {n : ℕ} (i : Fin n) :
    coordinateSigma i ≤ (inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin n))) :=
  (measurable_fst.comp (coordinateChart i).measurable).comap_le

end HitAndRun.Markov
