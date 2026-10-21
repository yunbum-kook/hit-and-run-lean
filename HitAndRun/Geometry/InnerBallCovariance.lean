module
public import HitAndRun.Geometry.ConvexCovarianceRadius
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev.BoundedOpenDomain
open MeasureTheory Set
open scoped ENNReal
variable {n : ℕ} [NeZero n]

/-- A half-radius ball captures at most half the uniform mass whenever the body
contains a radius-r ball. No convexity or centering assumption is used. -/
theorem uniform_ball_half_le (K : BoundedOpenDomain n) {r : ℝ} (_hr : 0 < r)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r ⊆ K.carrier)
    (c : EuclideanSpace ℝ (Fin n)) :
    uniformMeasure K.carrier (Metric.ball c (r / 2)) ≤ ENNReal.ofReal (1/2 : ℝ) := by
  have hv := domain_volume_bounds K.isOpen K.nonempty K.isBounded
  have hp : (1/2 : ℝ)^n ≤ 1/2 := by
    simpa using pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) ≤ 1) (NeZero.one_le : 1 ≤ n)
  have hb : volume (Metric.ball c (r/2)) =
      ENNReal.ofReal ((1/2:ℝ)^n) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) := by
    convert Measure.addHaar_ball_mul_of_pos volume c (by norm_num : (0:ℝ) < 1/2) r using 1 <;>
      simp [finrank_euclideanSpace, div_eq_mul_inv, mul_comm]
  calc
    _ ≤ (volume K.carrier)⁻¹ * volume (Metric.ball c (r/2)) := by
      simp only [uniformMeasure, Measure.smul_apply, smul_eq_mul]
      gcongr
      exact Measure.restrict_le_self
    _ = (volume K.carrier)⁻¹ * (ENNReal.ofReal ((1/2:ℝ)^n) *
          volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r)) := by rw [hb]
    _ ≤ (volume K.carrier)⁻¹ * (ENNReal.ofReal ((1/2:ℝ)^n) * volume K.carrier) :=
      by gcongr
    _ = ENNReal.ofReal ((1/2:ℝ)^n) := by
      rw [mul_left_comm, ENNReal.inv_mul_cancel hv.1.ne' hv.2.ne, mul_one]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hp

/-- The actual centered second moment is at least r²/8. -/
theorem innerBall_le_centered_secondMoment (K : BoundedOpenDomain n) {r : ℝ}
    (hr : 0 < r)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r ⊆ K.carrier) :
    r^2 / 8 ≤ ∫ z, ‖z - K.barycenter‖^2 ∂uniformMeasure K.carrier := by
  let := uniformMeasure_isProbabilityMeasure K.isOpen K.nonempty K.isBounded
  let μ := uniformMeasure K.carrier
  have hi : Integrable (fun z => ‖z - K.barycenter‖^2) μ :=
    (K.uniform_memLp_id.sub (memLp_const K.barycenter)).norm.integrable_sq
  have hm : μ.real (Metric.ball K.barycenter (r/2)) ≤ 1/2 := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (K.uniform_ball_half_le hr hball K.barycenter)
    simpa only [μ, measureReal_def, ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1/2)] using this
  have hc : (1/2 : ℝ) ≤ μ.real (Metric.ball K.barycenter (r/2))ᶜ := by
    rw [measureReal_compl measurableSet_ball]
    simpa only [probReal_univ] using (by linarith : (1/2:ℝ) ≤ 1 - μ.real (Metric.ball K.barycenter (r/2)))
  have he : {z : EuclideanSpace ℝ (Fin n) | (r/2)^2 ≤ ‖z-K.barycenter‖^2} =
      (Metric.ball K.barycenter (r/2))ᶜ := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Metric.mem_ball, dist_eq_norm, not_lt]
    exact sq_le_sq₀ (by positivity) (norm_nonneg _)
  have hh := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (Filter.Eventually.of_forall (fun z => sq_nonneg ‖z-K.barycenter‖)) hi ((r/2)^2)
  rw [he] at hh
  have ht := mul_le_mul_of_nonneg_left hc (sq_nonneg (r/2))
  dsimp [μ] at hh ht ⊢
  nlinarith

/-- Trace is bounded by dimension times operator norm for the genuine centered covariance. -/
theorem centered_secondMoment_le (K : BoundedOpenDomain n) :
    (∫ z, ‖z - K.barycenter‖^2 ∂uniformMeasure K.carrier) ≤
      (n : ℝ) * ‖K.centeredCovarianceOperator‖ := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have he : ∀ z, ‖z - K.barycenter‖^2 = ∑ i : Fin n, K.centeredProjection (b i) z ^ 2 := by
    intro z
    exact (b.sum_sq_inner_right (z-K.barycenter)).symm
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => (K.centeredProjection_memLp (b i)).integrable_sq)]
  simp_rw [K.integral_centeredProjection_sq]
  calc
    _ ≤ ∑ i : Fin n, ‖K.centeredCovarianceOperator‖ := by
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ ‖K.centeredCovarianceOperator (b i)‖ * ‖b i‖ := real_inner_le_norm _ _
        _ ≤ (‖K.centeredCovarianceOperator‖ * ‖b i‖) * ‖b i‖ :=
          mul_le_mul_of_nonneg_right (K.centeredCovarianceOperator.le_opNorm _) (norm_nonneg _)
        _ = _ := by simp [b.norm_eq_one]
    _ = _ := by simp

/-- Containment of a radius-r ball forces a nonzero covariance scale, with no
convexity, centroid, or moment assumptions beyond the actual bounded open domain. -/
theorem innerBall_covariance_lower (K : BoundedOpenDomain n) {r : ℝ}
    (hr : 0 < r)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r ⊆ K.carrier) :
    r^2 / (8 * (n : ℝ)) ≤ ‖K.centeredCovarianceOperator‖ := by
  have h := (K.innerBall_le_centered_secondMoment hr hball).trans K.centered_secondMoment_le
  have hn : (0:ℝ) < n := by exact_mod_cast NeZero.pos n
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith

/-- The actual covariance is strictly positive as soon as the body contains a
positive-radius ball. -/
theorem innerBall_covariance_pos (K : BoundedOpenDomain n) {r : ℝ}
    (hr : 0 < r)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r ⊆ K.carrier) :
    0 < ‖K.centeredCovarianceOperator‖ := by
  have hn : (0:ℝ) < n := by exact_mod_cast NeZero.pos n
  exact lt_of_lt_of_le (by positivity) (K.innerBall_covariance_lower hr hball)

/-- Dimensionless scale for absorbing additive constants in source estimates. -/
theorem one_le_innerBall_covariance_scale (K : BoundedOpenDomain n) {r : ℝ}
    (hr : 0 < r)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r ⊆ K.carrier) :
    1 ≤ 8 * (n : ℝ) * ‖K.centeredCovarianceOperator‖ / r^2 := by
  have hn : (0:ℝ) < n := by exact_mod_cast NeZero.pos n
  have h := (div_le_iff₀ (by positivity : 0 < 8 * (n : ℝ))).mp
    (K.innerBall_covariance_lower hr hball)
  apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
  nlinarith

end HitAndRun.Sobolev.BoundedOpenDomain
