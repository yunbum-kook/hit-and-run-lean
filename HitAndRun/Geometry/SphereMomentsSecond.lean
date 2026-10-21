module
public import HitAndRun.Geometry.SphereMoments
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
@[expose] public section

namespace HitAndRun.Geometry
open MeasureTheory Set
variable {n : ℕ} [NeZero n]

/-- Every continuous scalar function on the sphere is integrable. -/
theorem uniformSphere_integrable {f : UnitDirection n → ℝ} (hf : Continuous f) :
    Integrable f (uniformSphere n) := by
  letI := uniformSphere_probability n
  letI : CompactSpace (UnitDirection n) := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
  exact integrableOn_univ.mp (hf.continuousOn.integrableOn_compact isCompact_univ)

/-- Integrating a continuous function is unchanged by an orthogonal map. -/
theorem uniformSphere_integral_rotation
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    {f : UnitDirection n → ℝ} (hf : Continuous f) :
    (∫ θ, f (sphereAction U θ) ∂uniformSphere n) = ∫ θ, f θ ∂uniformSphere n := by
  have h := sphereAction_uniform_measurePreserving U
  calc
    _ = ∫ θ, f θ ∂Measure.map (sphereAction U) (uniformSphere n) :=
      (integral_map h.aemeasurable hf.aestronglyMeasurable).symm
    _ = _ := by rw [h.map_eq]

/-- The coordinate square sum on the sphere is exactly one. -/
theorem unitDirection_sum_sq (θ : UnitDirection n) : ∑ i, (θ.val i)^2 = 1 := by
  rw [← EuclideanSpace.real_norm_sq_eq]
  have h : ‖θ.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using θ.property
  rw [h, one_pow]

/-- Permutation symmetry identifies all diagonal second moments. -/
theorem uniformSphere_integral_sq_eq (i j : Fin n) :
    (∫ θ : UnitDirection n, (θ.val i)^2 ∂uniformSphere n) =
      ∫ θ : UnitDirection n, (θ.val j)^2 ∂uniformSphere n := by
  let U := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j)
  have h := uniformSphere_integral_rotation U
    ((PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).comp continuous_subtype_val |>.pow 2)
  simpa [U, sphereAction, LinearIsometryEquiv.piLpCongrLeft_apply] using h.symm

/-- Each diagonal second moment of the actual uniform sphere is 1/n. -/
theorem uniformSphere_integral_sq (i : Fin n) :
    (∫ θ : UnitDirection n, (θ.val i)^2 ∂uniformSphere n) = 1 / (n : ℝ) := by
  letI := uniformSphere_probability n
  have hsum : (∑ j : Fin n, ∫ θ : UnitDirection n, (θ.val j)^2 ∂uniformSphere n) = 1 := by
    rw [← integral_finsetSum]
    · simp only [unitDirection_sum_sq]
      simp
    · intro j _
      exact uniformSphere_integrable ((PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j).comp continuous_subtype_val |>.pow 2)
  have heq : (∑ j : Fin n, ∫ θ : UnitDirection n, (θ.val j)^2 ∂uniformSphere n) =
      (n : ℝ) * (∫ θ : UnitDirection n, (θ.val i)^2 ∂uniformSphere n) := by
    simp_rw [uniformSphere_integral_sq_eq _ i]
    simp
  rw [heq] at hsum
  apply (eq_div_iff (by exact Nat.cast_ne_zero.mpr (NeZero.ne n))).2
  simpa [mul_comm] using hsum

/-- Flip one coordinate, leaving the other coordinates unchanged. -/
noncomputable def coordinateFlip (i : Fin n) :
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearIsometryEquiv.piLpCongrRight 2
    (fun j => if j = i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)

@[simp] theorem coordinateFlip_apply (i j : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    coordinateFlip i x j = if j = i then -x j else x j := by
  simp only [coordinateFlip, LinearIsometryEquiv.piLpCongrRight_apply]
  split_ifs <;> rfl

/-- Distinct coordinate second moments vanish by a genuine sign-flip symmetry. -/
theorem uniformSphere_integral_mul_eq_zero (i j : Fin n) (hij : i ≠ j) :
    (∫ θ : UnitDirection n, θ.val i * θ.val j ∂uniformSphere n) = 0 := by
  have h := uniformSphere_integral_rotation (coordinateFlip i)
    (((PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).comp continuous_subtype_val).mul
      ((PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j).comp continuous_subtype_val))
  simp [Function.comp_def, sphereAction, hij.symm, integral_neg] at h
  linarith

/-- Complete coordinate covariance formula for the genuine uniform sphere. -/
theorem uniformSphere_integral_mul (i j : Fin n) :
    (∫ θ : UnitDirection n, θ.val i * θ.val j ∂uniformSphere n) =
      if i = j then 1 / (n : ℝ) else 0 := by
  by_cases h : i = j
  · subst j
    simpa [sq] using uniformSphere_integral_sq i
  · simpa [h] using uniformSphere_integral_mul_eq_zero i j h

end HitAndRun.Geometry
