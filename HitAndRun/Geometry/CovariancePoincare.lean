module
public import HitAndRun.Sobolev.PoincareConstants
public import HitAndRun.Sobolev.SmoothGraph
public import Mathlib.Probability.Moments.CovarianceBilin
public import Mathlib.Analysis.InnerProductSpace.Rayleigh
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev.BoundedOpenDomain
open MeasureTheory ProbabilityTheory EllipticPdes EllipticPdes.H1Graph
open scoped ENNReal
variable {n : ℕ} [NeZero n]

theorem uniform_memLp_id (K : BoundedOpenDomain n) :
    MemLp id 2 (uniformMeasure K.carrier) := by
  rw [← K.measure_eq_uniform]
  exact continuous_memLp_bounded_restrict K.isBounded K.isOpen.measurableSet continuous_id

def linearH1 (K : BoundedOpenDomain n) (v : EuclideanSpace ℝ (Fin n)) : K.H1 :=
  smoothH1 K.isBounded K.isOpen (fun x => inner ℝ v x) (InnerProductSpace.toDual ℝ _ v).contDiff

theorem linearH1_fn (K : BoundedOpenDomain n) (v : EuclideanSpace ℝ (Fin n)) :
    (fnL (K.linearH1 v : H1Graph K.ambient K.carrier) : _ → ℝ)
      =ᵐ[K.ambient.restrict K.carrier] (fun x => inner ℝ v x) :=
  smoothGraph_fn K.isBounded K.isOpen _ (InnerProductSpace.toDual ℝ _ v).contDiff

theorem gradient_linear (v : EuclideanSpace ℝ (Fin n)) :
    gradient (fun x => inner ℝ v x) = fun _ => v := by
  funext x
  apply ext_inner_right ℝ
  intro y
  rw [inner_gradient_left]
  change fderiv ℝ ((InnerProductSpace.toDual ℝ _ v) : _ → ℝ) x y = _
  rw [ContinuousLinearMap.fderiv]
  rfl

theorem linearH1_grad (K : BoundedOpenDomain n) (v : EuclideanSpace ℝ (Fin n)) :
    (gradL (K.linearH1 v : H1Graph K.ambient K.carrier) : _ → _)
      =ᵐ[K.ambient.restrict K.carrier] (fun _ => v) := by
  exact (smoothGraph_grad K.isBounded K.isOpen _ (InnerProductSpace.toDual ℝ _ v).contDiff).trans (Filter.Eventually.of_forall
    fun x => congrFun (gradient_linear v) x)

theorem linearH1_gradientEnergy (K : BoundedOpenDomain n)
    (v : EuclideanSpace ℝ (Fin n)) :
    K.gradientEnergy (K.linearH1 v) = ENNReal.ofReal (‖v‖ ^ 2) := by
  letI := uniformMeasure_isProbabilityMeasure K.isOpen K.nonempty K.isBounded
  rw [K.gradientEnergy_eq_lintegral]
  calc
    _ = ∫⁻ _x, ‖v‖ₑ ^ 2 ∂K.ambient.restrict K.carrier := lintegral_congr_ae (by
      filter_upwards [K.linearH1_grad v] with x hx
      rw [hx])
    _ = _ := by
      rw [K.measure_eq_uniform]
      simp [ENNReal.ofReal_pow, ofReal_norm]

/-- The centered covariance operator, associated to the genuine covariance bilinear form.
Mathlib's `covarianceOperator` itself is the uncentered second-moment operator. -/
def centeredCovarianceOperator (K : BoundedOpenDomain n) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  InnerProductSpace.continuousLinearMapOfBilin (covarianceBilin (uniformMeasure K.carrier))

theorem centeredCovarianceOperator_inner (K : BoundedOpenDomain n)
    (v w : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (K.centeredCovarianceOperator v) w =
      covarianceBilin (uniformMeasure K.carrier) v w :=
  InnerProductSpace.continuousLinearMapOfBilin_apply _ _ _

theorem centeredCovarianceOperator_positive (K : BoundedOpenDomain n) :
    K.centeredCovarianceOperator.IsPositive := by
  constructor
  · intro v w
    change inner ℝ (K.centeredCovarianceOperator v) w = inner ℝ v (K.centeredCovarianceOperator w)
    rw [← real_inner_comm v (K.centeredCovarianceOperator w),
      K.centeredCovarianceOperator_inner, K.centeredCovarianceOperator_inner]
    exact covarianceBilin_comm v w
  · intro v
    simpa only [ContinuousLinearMap.reApplyInnerSelf_apply, K.centeredCovarianceOperator_inner,
      RCLike.re_to_real] using covarianceBilin_self_nonneg (μ := uniformMeasure K.carrier) v

theorem linearH1_varianceEnergy (K : BoundedOpenDomain n)
    (v : EuclideanSpace ℝ (Fin n)) :
    K.varianceEnergy (K.linearH1 v) =
      ENNReal.ofReal (inner ℝ (K.centeredCovarianceOperator v) v) := by
  letI := uniformMeasure_isProbabilityMeasure K.isOpen K.nonempty K.isBounded
  rw [varianceEnergy, evariance_congr (K.linearH1_fn v), K.measure_eq_uniform,
    K.centeredCovarianceOperator_inner, covarianceBilin_self K.uniform_memLp_id]
  exact (ofReal_variance (K.uniform_memLp_id.const_inner v)).symm

theorem centeredCovarianceOperator_quadratic_le (K : BoundedOpenDomain n)
    (hfin : K.poincareConstant < ⊤) (v : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (K.centeredCovarianceOperator v) v ≤ K.poincareConstant.toReal * ‖v‖ ^ 2 := by
  have h := K.poincareConstant_admissible_of_lt_top hfin (K.linearH1 v)
  rw [K.linearH1_varianceEnergy, K.linearH1_gradientEnergy] at h
  have ht := ENNReal.toReal_mono (ENNReal.mul_ne_top hfin.ne ENNReal.ofReal_ne_top) h
  simpa only [ENNReal.toReal_ofReal (K.centeredCovarianceOperator_positive.inner_nonneg_left v),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg ‖v‖)] using ht

/-- Linear genuine W12 tests bound the actual centered covariance by the optimal PI constant. -/
theorem norm_centeredCovarianceOperator_le (K : BoundedOpenDomain n)
    (hfin : K.poincareConstant < ⊤) :
    ‖K.centeredCovarianceOperator‖ ≤ K.poincareConstant.toReal := by
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient _
    K.centeredCovarianceOperator_positive.isSymmetric]
  apply ciSup_le
  intro v
  rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
    RCLike.re_to_real, abs_of_nonneg (div_nonneg
      (K.centeredCovarianceOperator_positive.inner_nonneg_left v) (sq_nonneg _))]
  by_cases hv : v = 0
  · simp [hv]
  · exact (div_le_iff₀ (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hv))).mpr
      (K.centeredCovarianceOperator_quadratic_le hfin v)
end HitAndRun.Sobolev.BoundedOpenDomain
