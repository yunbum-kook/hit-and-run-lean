module
public import HitAndRun.Geometry.TranslatedDomain
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev.BoundedOpenDomain
open MeasureTheory Set
open scoped ENNReal
variable {n : ℕ} [NeZero n]

def linearImage (K : BoundedOpenDomain n)
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) : BoundedOpenDomain n where
  carrier := L '' K.carrier
  isOpen := L.toHomeomorph.isOpenMap _ K.isOpen
  nonempty := K.nonempty.image _
  isBounded := L.toContinuousLinearMap.lipschitzWith.isBounded_image K.isBounded

theorem linearImage_map_volume (K : BoundedOpenDomain n)
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    (volume.restrict K.carrier).map L =
      ENNReal.ofReal |(LinearMap.det L.toLinearEquiv.toLinearMap)⁻¹| •
        volume.restrict (K.linearImage L).carrier := by
  have hm := Measure.map_linearMap_addHaar_eq_smul_addHaar volume L.toLinearEquiv.isUnit_det'.ne_zero
  have hr := L.toHomeomorph.measurableEmbedding.restrict_map volume (L '' K.carrier)
  change (Measure.map L volume).restrict (L '' K.carrier) =
    (volume.restrict (L ⁻¹' (L '' K.carrier))).map L at hr
  rw [Set.preimage_image_eq _ L.injective] at hr
  rw [← hr]
  change (Measure.map L.toLinearEquiv.toLinearMap volume).restrict _ = _
  rw [hm, Measure.restrict_smul]
  rfl

theorem linearImage_volume_factor (K : BoundedOpenDomain n)
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    volume K.carrier = ENNReal.ofReal |(LinearMap.det L.toLinearEquiv.toLinearMap)⁻¹| *
      volume (K.linearImage L).carrier := by
  have h := congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin n)) => μ Set.univ)
    (K.linearImage_map_volume L)
  simpa [Measure.map_apply L.continuous.measurable MeasurableSet.univ] using h

theorem linearImage_uniform_map (K : BoundedOpenDomain n)
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    (uniformMeasure K.carrier).map L = uniformMeasure (K.linearImage L).carrier := by
  have hc0 : ENNReal.ofReal |(LinearMap.det L.toLinearEquiv.toLinearMap)⁻¹| ≠ 0 := by
    exact ENNReal.ofReal_ne_zero_iff.mpr (abs_pos.mpr (inv_ne_zero L.toLinearEquiv.isUnit_det'.ne_zero))
  simp only [uniformMeasure]
  rw [Measure.map_smul _ L.continuous.measurable.aemeasurable, K.linearImage_map_volume, smul_smul]
  rw [K.linearImage_volume_factor L, ENNReal.mul_inv (Or.inl hc0) (Or.inl ENNReal.ofReal_ne_top)]
  rw [mul_comm, ← mul_assoc, ENNReal.mul_inv_cancel hc0 ENNReal.ofReal_ne_top, one_mul]

theorem linearImage_measurePreserving (K : BoundedOpenDomain n)
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    MeasurePreserving L (uniformMeasure K.carrier) (uniformMeasure (K.linearImage L).carrier) :=
  ⟨L.continuous.measurable, K.linearImage_uniform_map L⟩

end HitAndRun.Sobolev.BoundedOpenDomain
