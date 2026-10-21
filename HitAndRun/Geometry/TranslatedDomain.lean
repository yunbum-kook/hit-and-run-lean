module
public import HitAndRun.Sobolev.PoincareConstants
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev.BoundedOpenDomain
open MeasureTheory Set
variable {n : ℕ} [NeZero n]

def translate (K : BoundedOpenDomain n) (c : EuclideanSpace ℝ (Fin n)) : BoundedOpenDomain n where
  carrier := (fun x => c + x) '' K.carrier
  isOpen := (Homeomorph.addLeft c).isOpenMap _ K.isOpen
  nonempty := K.nonempty.image _
  isBounded := K.isBounded.vadd c

@[simp] theorem translate_mem (K : BoundedOpenDomain n) (c x : EuclideanSpace ℝ (Fin n)) :
    c + x ∈ (K.translate c).carrier ↔ x ∈ K.carrier := by
  change c + x ∈ (fun y => c + y) '' K.carrier ↔ _
  simp only [mem_image, add_right_inj, exists_eq_right]

theorem translate_volume (K : BoundedOpenDomain n) (c : EuclideanSpace ℝ (Fin n)) :
    volume (K.translate c).carrier = volume K.carrier := by
  have h := (measurePreserving_add_left volume c).measure_preimage
    (K.translate c).isOpen.measurableSet.nullMeasurableSet
  have he : (fun x => c + x) ⁻¹' (K.translate c).carrier = K.carrier := by
    ext x
    exact K.translate_mem c x
  rw [he] at h
  exact h.symm

theorem translate_ambient (K : BoundedOpenDomain n) (c : EuclideanSpace ℝ (Fin n)) :
    (K.translate c).ambient = K.ambient := by
  simp only [ambient, normalizedAmbient, K.translate_volume]

theorem translate_measurePreserving (K : BoundedOpenDomain n) (c : EuclideanSpace ℝ (Fin n)) :
    MeasurePreserving (fun x => c + x) (K.ambient.restrict K.carrier)
      ((K.translate c).ambient.restrict (K.translate c).carrier) := by
  rw [K.translate_ambient]
  exact (measurePreserving_add_left K.ambient c).restrict_image_emb
    (Homeomorph.addLeft c).measurableEmbedding K.carrier

theorem translate_boundaryDistance (K : BoundedOpenDomain n) (c x : EuclideanSpace ℝ (Fin n)) :
    (K.translate c).boundaryDistance (c + x) = K.boundaryDistance x := by
  unfold boundaryDistance
  change Metric.infDist (c + x) (frontier ((Homeomorph.addLeft c) '' K.carrier)) = _
  rw [← (Homeomorph.addLeft c).image_frontier]
  exact Metric.infDist_image (isometry_add_left c)

theorem translate_integral (K : BoundedOpenDomain n) (c : EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∫ x, f (c + x) ∂K.ambient.restrict K.carrier) =
      ∫ x, f x ∂(K.translate c).ambient.restrict (K.translate c).carrier :=
  (K.translate_measurePreserving c).integral_comp (Homeomorph.addLeft c).measurableEmbedding f

end HitAndRun.Sobolev.BoundedOpenDomain
