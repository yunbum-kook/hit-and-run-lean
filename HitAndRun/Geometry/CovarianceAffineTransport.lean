module
public import HitAndRun.Geometry.LinearImageDomain
public import HitAndRun.Geometry.CovariancePoincare
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev.BoundedOpenDomain
open MeasureTheory ProbabilityTheory
variable {n : ℕ} [NeZero n]

theorem linearImage_mean (K : BoundedOpenDomain n)
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    (∫ x, x ∂uniformMeasure (K.linearImage L).carrier) =
      L (∫ x, x ∂uniformMeasure K.carrier) := by
  letI := uniformMeasure_isProbabilityMeasure K.isOpen K.nonempty K.isBounded
  rw [← K.linearImage_uniform_map L]
  calc
    _ = ∫ x, L x ∂uniformMeasure K.carrier := by
      simpa only [id_eq] using integral_map L.continuous.measurable.aemeasurable aestronglyMeasurable_id
    _ = _ := L.toContinuousLinearMap.integral_comp_comm (K.uniform_memLp_id.integrable (by simp))

theorem linearImage_covarianceBilin (K : BoundedOpenDomain n)
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (v w : EuclideanSpace ℝ (Fin n)) :
    covarianceBilin (uniformMeasure (K.linearImage L).carrier) v w =
      covarianceBilin (uniformMeasure K.carrier)
        (L.toContinuousLinearMap.adjoint v) (L.toContinuousLinearMap.adjoint w) := by
  letI := uniformMeasure_isProbabilityMeasure K.isOpen K.nonempty K.isBounded
  rw [← K.linearImage_uniform_map L]
  exact covarianceBilin_map K.uniform_memLp_id L.toContinuousLinearMap v w

theorem linearImage_centeredCovarianceOperator (K : BoundedOpenDomain n)
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    (K.linearImage L).centeredCovarianceOperator =
      L.toContinuousLinearMap.comp
        (K.centeredCovarianceOperator.comp L.toContinuousLinearMap.adjoint) := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_right ℝ
  intro w
  rw [(K.linearImage L).centeredCovarianceOperator_inner, K.linearImage_covarianceBilin]
  simp only [ContinuousLinearMap.comp_apply]
  rw [← L.toContinuousLinearMap.adjoint_inner_right]
  exact (K.centeredCovarianceOperator_inner _ _).symm

theorem translate_uniform_map (K : BoundedOpenDomain n) (c : EuclideanSpace ℝ (Fin n)) :
    (uniformMeasure K.carrier).map (fun x => c + x) = uniformMeasure (K.translate c).carrier := by
  simpa only [K.measure_eq_uniform, (K.translate c).measure_eq_uniform] using
    (K.translate_measurePreserving c).map_eq

theorem translate_mean (K : BoundedOpenDomain n) (c : EuclideanSpace ℝ (Fin n)) :
    (∫ x, x ∂uniformMeasure (K.translate c).carrier) =
      c + ∫ x, x ∂uniformMeasure K.carrier := by
  letI := uniformMeasure_isProbabilityMeasure K.isOpen K.nonempty K.isBounded
  rw [← K.translate_uniform_map c]
  calc
    _ = ∫ x, c + x ∂uniformMeasure K.carrier := by
      simpa only [id_eq] using integral_map (μ := uniformMeasure K.carrier)
        (φ := fun x => c + x) (measurable_const.add measurable_id).aemeasurable aestronglyMeasurable_id
    _ = _ := by
      simpa only [id_eq, integral_const, probReal_univ, one_smul] using
        integral_add (integrable_const c) (K.uniform_memLp_id.integrable (by simp))

theorem translate_covarianceBilin (K : BoundedOpenDomain n) (c : EuclideanSpace ℝ (Fin n)) :
    covarianceBilin (uniformMeasure (K.translate c).carrier) =
      covarianceBilin (uniformMeasure K.carrier) := by
  letI := uniformMeasure_isProbabilityMeasure K.isOpen K.nonempty K.isBounded
  rw [← K.translate_uniform_map c]
  exact covarianceBilin_map_const_add c

theorem translate_centeredCovarianceOperator (K : BoundedOpenDomain n)
    (c : EuclideanSpace ℝ (Fin n)) :
    (K.translate c).centeredCovarianceOperator = K.centeredCovarianceOperator := by
  simp only [centeredCovarianceOperator, K.translate_covarianceBilin]

end HitAndRun.Sobolev.BoundedOpenDomain
