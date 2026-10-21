module
public import HitAndRun.Geometry.UniformSphere
@[expose] public section

/-! Rotation invariance of the genuine normalized Euclidean sphere measure.
The construction reuses Mathlib's cone definition, not assumed moment identities. -/
namespace HitAndRun.Geometry
open MeasureTheory Set
open scoped Pointwise

variable {n : ℕ}

/-- The action of an orthogonal linear map on unit directions. -/
def sphereAction (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (θ : UnitDirection n) : UnitDirection n :=
  ⟨U θ, by simpa only [Metric.mem_sphere, dist_zero_right, U.norm_map] using θ.property⟩

theorem sphereAction_measurable
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    Measurable (sphereAction U) :=
  (U.continuous.comp continuous_subtype_val).subtype_mk _ |>.measurable

/-- Orthogonal maps commute with the radial cone operation. -/
theorem sphereAction_cone_preimage
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (s : Set (UnitDirection n)) :
    Ioo (0 : ℝ) 1 • (Subtype.val '' (sphereAction U ⁻¹' s)) =
      U ⁻¹' (Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
  ext x
  constructor
  · rintro ⟨r, hr, y, ⟨θ, hθ, rfl⟩, rfl⟩
    exact ⟨r, hr, U θ, ⟨sphereAction U θ, hθ, rfl⟩, U.map_smul r θ |>.symm⟩
  · rintro ⟨r, hr, y, ⟨θ, hθ, rfl⟩, hx⟩
    refine ⟨r, hr, U.symm θ, ⟨sphereAction U.symm θ, ?_, rfl⟩, ?_⟩
    · simpa only [mem_preimage, sphereAction, U.apply_symm_apply] using hθ
    · apply U.injective
      simpa only [U.map_smul, U.apply_symm_apply] using hx

/-- Actual surface measure is orthogonally invariant. -/
theorem sphereAction_surface_measurePreserving
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    MeasurePreserving (sphereAction U)
      (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere
      (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere := by
  refine ⟨sphereAction_measurable U, ?_⟩
  ext s hs
  rw [Measure.map_apply (sphereAction_measurable U) hs,
    Measure.toSphere_apply' _ ((sphereAction_measurable U) hs),
    Measure.toSphere_apply' _ hs, sphereAction_cone_preimage]
  rw [U.measurePreserving.measure_preimage_emb U.toHomeomorph.measurableEmbedding]

/-- Normalization preserves orthogonal invariance. -/
theorem sphereAction_uniform_measurePreserving [NeZero n]
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    MeasurePreserving (sphereAction U) (uniformSphere n) (uniformSphere n) := by
  refine ⟨sphereAction_measurable U, ?_⟩
  unfold uniformSphere
  rw [Measure.map_smul _ (sphereAction_measurable U).aemeasurable,
    (sphereAction_surface_measurePreserving U).map_eq]

end HitAndRun.Geometry
