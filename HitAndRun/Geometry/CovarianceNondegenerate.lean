module
public import HitAndRun.Geometry.CovariancePoincare
public import Mathlib.MeasureTheory.Measure.OpenPos
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev.BoundedOpenDomain
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n : ℕ} [NeZero n]

/-- A zero-variance scalar projection is constant everywhere on the open domain. -/
theorem inner_eq_mean_of_centeredCovarianceOperator_eq_zero
    (K : BoundedOpenDomain n) (v : EuclideanSpace ℝ (Fin n))
    (h : inner ℝ (K.centeredCovarianceOperator v) v = 0) :
    Set.EqOn (fun x => inner ℝ v x)
      (fun _ => ∫ x, inner ℝ v x ∂uniformMeasure K.carrier) K.carrier := by
  let := uniformMeasure_isProbabilityMeasure K.isOpen K.nonempty K.isBounded
  rw [K.centeredCovarianceOperator_inner, covarianceBilin_self K.uniform_memLp_id] at h
  have hae := ae_eq_integral_of_variance_eq_zero (K.uniform_memLp_id.const_inner v) h
  have hc : (volume K.carrier)⁻¹ ≠ 0 :=
    ENNReal.inv_ne_zero.mpr K.isBounded.measure_lt_top.ne
  rw [uniformMeasure, Measure.ae_ennreal_smul_measure_eq hc] at hae
  exact MeasureTheory.Measure.eqOn_open_of_ae_eq hae K.isOpen
    (by fun_prop) continuousOn_const

/-- The actual centered covariance is strictly positive in every nonzero direction. -/
theorem centeredCovarianceOperator_inner_pos (K : BoundedOpenDomain n)
    (v : EuclideanSpace ℝ (Fin n)) (hv : v ≠ 0) :
    0 < inner ℝ (K.centeredCovarianceOperator v) v := by
  by_contra hpos
  have hz : inner ℝ (K.centeredCovarianceOperator v) v = 0 :=
    le_antisymm (le_of_not_gt hpos) (K.centeredCovarianceOperator_positive.inner_nonneg_left v)
  have heq := K.inner_eq_mean_of_centeredCovarianceOperator_eq_zero v hz
  obtain ⟨x, hx⟩ := K.nonempty
  have hevent : (fun y => inner ℝ v y) =ᶠ[nhds x]
      (fun _ => ∫ z, inner ℝ v z ∂uniformMeasure K.carrier) :=
    Filter.eventuallyEq_of_mem (K.isOpen.mem_nhds hx) heq
  have hd := hevent.fderiv_eq (𝕜 := ℝ)
  have hdual : InnerProductSpace.toDual ℝ _ v = 0 := by
    change fderiv ℝ ((InnerProductSpace.toDual ℝ _ v) : _ → ℝ) x = _ at hd
    simpa only [ContinuousLinearMap.fderiv, fderiv_const_apply] using hd
  exact hv ((InnerProductSpace.toDual ℝ _).injective (by simpa using hdual))

/-- No nonzero direction belongs to the covariance kernel. -/
theorem centeredCovarianceOperator_ker (K : BoundedOpenDomain n) :
    LinearMap.ker K.centeredCovarianceOperator.toLinearMap = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro v hv
  by_contra hne
  have hp := K.centeredCovarianceOperator_inner_pos v hne
  change K.centeredCovarianceOperator v = 0 at hv
  rw [hv, inner_zero_left] at hp
  exact (lt_irrefl 0) hp

theorem centeredCovarianceOperator_bijective (K : BoundedOpenDomain n) :
    Function.Bijective K.centeredCovarianceOperator := by
  have hi : Function.Injective K.centeredCovarianceOperator :=
    LinearMap.ker_eq_bot.mp K.centeredCovarianceOperator_ker
  exact ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩

/-- The centered covariance is an invertible linear equivalence in finite dimension. -/
def centeredCovarianceEquiv (K : BoundedOpenDomain n) :
    EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearEquiv.ofBijective K.centeredCovarianceOperator.toLinearMap
    K.centeredCovarianceOperator_bijective

@[simp] theorem centeredCovarianceEquiv_apply (K : BoundedOpenDomain n)
    (v : EuclideanSpace ℝ (Fin n)) :
    K.centeredCovarianceEquiv v = K.centeredCovarianceOperator v := rfl

end HitAndRun.Sobolev.BoundedOpenDomain
