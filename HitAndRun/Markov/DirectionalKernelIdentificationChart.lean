module
public import HitAndRun.Markov.DirectionalAnnihilationChart
public import HitAndRun.Markov.CoordinateKernelIdentificationTransport
@[expose] public section

namespace HitAndRun.Markov
open Set MeasureTheory HitAndRun.Geometry HitAndRun.Sobolev
variable {n : ℕ} [NeZero n] (θ : UnitDirection n)

noncomputable def directionalChart : EuclideanSpace ℝ (Fin n) ≃ᵐ OtherCoordinates (0 : Fin n) × ℝ :=
  (directionRotation θ).symm.toMeasurableEquiv.trans (coordinateChart (0 : Fin n))

noncomputable def directionalInsert : OtherCoordinates (0 : Fin n) × ℝ →L[ℝ]
    EuclideanSpace ℝ (Fin n) :=
  (directionRotation θ).toContinuousLinearEquiv.toContinuousLinearMap.comp (coordinateInsert 0)

@[simp] theorem directionalInsert_apply (z : OtherCoordinates (0 : Fin n) × ℝ) :
    directionalInsert θ z = directionRotation θ (coordinateInsert 0 z) := rfl

@[simp] theorem directionalChart_symm (z : OtherCoordinates (0 : Fin n) × ℝ) :
    (directionalChart θ).symm z = directionalInsert θ z := rfl

@[simp] theorem directionalChart_fst (x : EuclideanSpace ℝ (Fin n))
    (j : {j : Fin n // j ≠ 0}) :
    (directionalChart θ x).1 j = ((directionRotation θ).symm x) j := rfl

theorem directionalChart_volume :
    MeasurePreserving (directionalChart θ) volume (volume.prod volume) :=
  (directionRotation θ).symm.measurePreserving.trans (coordinateChart_volume 0)

/-- The rotated chart conditions on exactly the actual perpendicular projection. -/
theorem directionalChart_sigma :
    MeasurableSpace.comap (fun x => (directionalChart θ x).1) inferInstance = directionalSigma θ := by
  let X : EuclideanSpace ℝ (Fin n) → OtherCoordinates (0 : Fin n) :=
    fun x => (directionalChart θ x).1
  let F : OtherCoordinates (0 : Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun z => directionQuotient θ (directionalInsert θ (z, 0))
  have hX : Measurable X := measurable_fst.comp (directionalChart θ).measurable
  have hF : Measurable F := (directionQuotient θ).continuous.measurable.comp
    ((directionalInsert θ).continuous.measurable.comp (measurable_id.prodMk measurable_const))
  have hθ : (directionRotation θ).symm θ = EuclideanSpace.basisFun (Fin n) ℝ (0 : Fin n) := by
    rw [← directionRotation_basis θ, LinearIsometryEquiv.symm_apply_apply]
  have hx : X = X ∘ directionQuotient θ := by
    funext x
    funext j
    change ((directionRotation θ).symm x) j =
      ((directionRotation θ).symm (directionQuotient θ x)) j
    simp only [directionQuotient, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smulRight_apply, map_sub, map_smul, hθ]
    simp [EuclideanSpace.basisFun_apply, j.property]
  have hq : (directionQuotient θ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) = F ∘ X := by
    funext x
    have h := directionQuotient_rotation_factor θ ((directionRotation θ).symm x)
    simpa [F, X, directionalChart] using h
  apply le_antisymm
  · change MeasurableSpace.comap X _ ≤ MeasurableSpace.comap (directionQuotient θ) _
    rw [hx, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hX.comap_le
  · change MeasurableSpace.comap (directionQuotient θ) _ ≤ MeasurableSpace.comap X _
    rw [hq, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hF.comap_le

end HitAndRun.Markov
