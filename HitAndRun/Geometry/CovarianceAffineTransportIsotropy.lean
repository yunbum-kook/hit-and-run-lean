module
public import HitAndRun.Geometry.CovarianceAffineTransportWhitening
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev.BoundedOpenDomain
open MeasureTheory ProbabilityTheory
variable {n : ℕ} [NeZero n]

theorem uniform_integrable_coordinate (K : BoundedOpenDomain n) (i : Fin n) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) => x i) (uniformMeasure K.carrier) := by
  rw [← K.measure_eq_uniform]
  exact (continuous_memLp_bounded_restrict K.isBounded K.isOpen.measurableSet
    (f := fun x : EuclideanSpace ℝ (Fin n) => x i) (by fun_prop)).integrable (by simp)

theorem uniform_integrable_coordinate_product (K : BoundedOpenDomain n) (i j : Fin n) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) => x i * x j) (uniformMeasure K.carrier) := by
  rw [← K.measure_eq_uniform]
  exact (continuous_memLp_bounded_restrict K.isBounded K.isOpen.measurableSet
    (f := fun x : EuclideanSpace ℝ (Fin n) => x i * x j) (by fun_prop)).integrable (by simp)

theorem whitenedDomain_coordinate_mean (K : BoundedOpenDomain n) (i : Fin n) :
    (∫ x : EuclideanSpace ℝ (Fin n), x i ∂uniformMeasure K.whitenedDomain.carrier) = 0 := by
  letI := uniformMeasure_isProbabilityMeasure K.whitenedDomain.isOpen
    K.whitenedDomain.nonempty K.whitenedDomain.isBounded
  have h := congrArg (fun x : EuclideanSpace ℝ (Fin n) => x i) K.whitenedDomain_mean
  have hi := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i).integral_comp_comm
    (K.whitenedDomain.uniform_memLp_id.integrable (by simp))
  simpa only [id_eq, PiLp.proj_apply, PiLp.zero_apply] using hi.trans h

theorem whitenedDomain_coordinate_secondMoment (K : BoundedOpenDomain n) (i j : Fin n) :
    (∫ x : EuclideanSpace ℝ (Fin n), x i * x j ∂uniformMeasure K.whitenedDomain.carrier) =
      if i = j then 1 else 0 := by
  letI := uniformMeasure_isProbabilityMeasure K.whitenedDomain.isOpen
    K.whitenedDomain.nonempty K.whitenedDomain.isBounded
  have h := K.whitenedDomain.centeredCovarianceOperator_inner
    (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  rw [K.whitenedDomain_covariance, ContinuousLinearMap.id_apply,
    covarianceBilin_apply K.whitenedDomain.uniform_memLp_id] at h
  simpa [K.whitenedDomain_mean, EuclideanSpace.inner_single_left, PiLp.single_apply,
    id_eq, eq_comm] using h.symm
end HitAndRun.Sobolev.BoundedOpenDomain
