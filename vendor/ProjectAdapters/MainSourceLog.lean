module
public import MainSourceGap
@[expose] public section
noncomputable section
namespace HitAndRun.Markov
open HitAndRun.Sobolev HitAndRun.Geometry

def mainSourceConstant : ℝ := Real.log 2 / (15 * mainSourceDenominator)
theorem mainSourceConstant_pos : 0 < mainSourceConstant := by
  have := mainSourceDenominator_pos
  have : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold mainSourceConstant
  positivity

variable {n : ℕ} [NeZero n]
/-- Source log(n), not log(en), with n≥2 and the genuine covariance PI input. -/
theorem mainSource_log_rate_le_CPI (K : BoundedOpenDomain n)
    (hn : 2 ≤ n) (hc : Convex ℝ K.carrier)
    (hball : (∃ a, Metric.ball a 1 ⊆ K.carrier))
    (hPI : K.poincareConstant.toReal ≤ 15 * ‖K.centeredCovarianceOperator‖) (k : ℕ) :
    mainSourceConstant / ((n : ℝ)^k * ‖K.centeredCovarianceOperator‖ * Real.log n) ≤
      1 / (mainSourceDenominator * (n : ℝ)^k * K.poincareConstant.toReal) := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  have hp := K.poincareConstant_toReal_pos_convex hc
  have hs := mainSource_covariance_pos K hball
  have hd := mainSourceDenominator_pos
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hln : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn2
  have hln0 : 0 < Real.log n := hl2.trans_le hln
  have hx : K.poincareConstant.toReal * Real.log 2 ≤
      15 * ‖K.centeredCovarianceOperator‖ * Real.log n := by
    exact (mul_le_mul_of_nonneg_right hPI hl2.le).trans
      (mul_le_mul_of_nonneg_left hln (by positivity))
  unfold mainSourceConstant
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (show 0 < 15 * mainSourceDenominator by positivity)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hx (show 0 ≤ mainSourceDenominator * (n : ℝ)^k by positivity)]

/-- Both printed covariance-log gap branches for the actual nonlazy algorithms. -/
theorem mainSource_covariance_log_gaps (K : BoundedOpenDomain n)
    (hn : 2 ≤ n) (hc : Convex ℝ K.carrier)
    (hball : (∃ a, Metric.ball a 1 ⊆ K.carrier))
    (hRB : UniversalOrdinaryL1ReverseBuser 256)
    (hPI : K.poincareConstant.toReal ≤ 15 * ‖K.centeredCovarianceOperator‖) :
    mainSourceConstant / ((n : ℝ)^2 * ‖K.centeredCovarianceOperator‖ * Real.log n) ≤
      spectralGap K (hitAndRunOperator K) ∧
    mainSourceConstant / ((n : ℝ)^3 * ‖K.centeredCovarianceOperator‖ * Real.log n) ≤
      spectralGap K (coordinateHeatBath K) := by
  have hg := mainSource_CPI_gaps K hc hball hRB
  exact ⟨(mainSource_log_rate_le_CPI K hn hc hball hPI 2).trans hg.1,
    (mainSource_log_rate_le_CPI K hn hc hball hPI 3).trans hg.2⟩
end HitAndRun.Markov
