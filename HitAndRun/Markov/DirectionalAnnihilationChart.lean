module
public import HitAndRun.Markov.CoordinateAnnihilationTest
public import HitAndRun.Geometry.UniformSphere
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
@[expose] public section

namespace HitAndRun.Markov
open MeasureTheory Set EllipticPdes EllipticPdes.H1Graph
open scoped RealInnerProductSpace
variable {n : ℕ} [NeZero n]

/-- The actual orthogonal projection onto the hyperplane perpendicular to θ. -/
noncomputable def directionQuotient (θ : HitAndRun.Geometry.UnitDirection n) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  ContinuousLinearMap.id ℝ _ - (innerSL ℝ (θ : EuclideanSpace ℝ (Fin n))).smulRight (θ : EuclideanSpace ℝ (Fin n))

@[simp] theorem directionQuotient_self (θ : HitAndRun.Geometry.UnitDirection n) :
    directionQuotient θ θ = 0 := by
  have h : ‖(θ : EuclideanSpace ℝ (Fin n))‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using θ.property
  simp [directionQuotient, real_inner_self_eq_norm_sq, h]

/-- The quotient really takes values in θ-perpendicular. -/
theorem directionQuotient_orthogonal (θ : HitAndRun.Geometry.UnitDirection n)
    (x : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (θ : EuclideanSpace ℝ (Fin n)) (directionQuotient θ x) = 0 := by
  have h : ‖(θ : EuclideanSpace ℝ (Fin n))‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using θ.property
  simp [directionQuotient, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, h]

noncomputable def directionRotation (θ : HitAndRun.Geometry.UnitDirection n) :
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  Submodule.reflection (ℝ ∙ (EuclideanSpace.basisFun (Fin n) ℝ (0 : Fin n) - θ))ᗮ

@[simp] theorem directionRotation_basis (θ : HitAndRun.Geometry.UnitDirection n) :
    directionRotation θ (EuclideanSpace.basisFun (Fin n) ℝ (0 : Fin n)) = θ := by
  apply Submodule.reflection_sub
  have h : ‖(θ : EuclideanSpace ℝ (Fin n))‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using θ.property
  simpa [h] using (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.norm_eq_one (0 : Fin n)

noncomputable def directionalSigma (θ : HitAndRun.Geometry.UnitDirection n) :
    MeasurableSpace (EuclideanSpace ℝ (Fin n)) :=
  MeasurableSpace.comap (directionQuotient θ) inferInstance

theorem directionalSigma_le (θ : HitAndRun.Geometry.UnitDirection n) :
    directionalSigma θ ≤ (inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin n))) :=
  (directionQuotient θ).continuous.measurable.comap_le

/-- Deleting the distinguished coordinate changes the rotated point only along θ. -/
theorem directionQuotient_rotation_factor (θ : HitAndRun.Geometry.UnitDirection n)
    (y : EuclideanSpace ℝ (Fin n)) :
    directionQuotient θ (directionRotation θ y) =
      directionQuotient θ (directionRotation θ
        (coordinateInsert (0 : Fin n) ((coordinateChart (0 : Fin n) y).1, 0))) := by
  have he : y = coordinateInsert (0 : Fin n) ((coordinateChart (0 : Fin n) y).1, 0) +
      y 0 • EuclideanSpace.basisFun (Fin n) ℝ (0 : Fin n) := by
    apply PiLp.ext
    intro j
    by_cases hj : j = 0
    · subst j
      change y 0 = (coordinateInsert (0 : Fin n) ((coordinateChart 0 y).1, 0)) 0 +
        y 0 * (EuclideanSpace.basisFun (Fin n) ℝ (0 : Fin n)) 0
      rw [coordinateInsert_at]
      simp [EuclideanSpace.basisFun_apply]
    · change y j = (coordinateInsert (0 : Fin n) ((coordinateChart 0 y).1, 0)) j +
        y 0 * (EuclideanSpace.basisFun (Fin n) ℝ (0 : Fin n)) j
      rw [coordinateInsert_other (0 : Fin n) _ ⟨j, hj⟩]
      simp [EuclideanSpace.basisFun_apply, hj]
  conv_lhs => rw [he]
  simp only [map_add, map_smul, directionRotation_basis, directionQuotient_self,
    smul_zero, add_zero]

end HitAndRun.Markov
