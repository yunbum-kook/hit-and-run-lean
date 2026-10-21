module
public import HitAndRun.Markov.ImprovedPoincareGap
public import HitAndRun.Geometry.WeightedPoincareBodySource
public import HitAndRun.Geometry.InnerBallCovariance
public import HitAndRun.Geometry.ConvexPoincareFinite
public import HitAndRun.Geometry.CovarianceAffineTransport
@[expose] public section
noncomputable section
namespace HitAndRun.Markov
open HitAndRun.Sobolev HitAndRun.Geometry
open scoped ENNReal
variable {n : ℕ} [NeZero n]
def mainSourceDenominator : ℝ := 24 + 16 * (1036 : ℝ)^2

theorem mainSourceDenominator_pos : 0 < mainSourceDenominator := by norm_num [mainSourceDenominator]

/-- Inner-ball covariance positivity at an arbitrary center, using only measure/covariance
translation, never a translation assumption on either Markov kernel. -/
theorem mainSource_covariance_pos (K : BoundedOpenDomain n)
    (hball : ∃ a, Metric.ball a 1 ⊆ K.carrier) :
    0 < ‖K.centeredCovarianceOperator‖ := by
  obtain ⟨a, ha⟩ := hball
  have h := (K.translate (-a)).innerBall_covariance_pos (r := 1) (by norm_num)
    (K.translate_neg_inner_ball ha)
  simpa only [K.translate_centeredCovarianceOperator] using h

/-- Actual source hypotheses; reverse-Buser is still an explicit analytic input. -/
theorem mainSource_BA_bound (K : BoundedOpenDomain n) (hc : Convex ℝ K.carrier)
    (hball : (∃ a, Metric.ball a 1 ⊆ K.carrier))
    (hRB : UniversalOrdinaryL1ReverseBuser 256) :
    K.constant < ⊤ ∧ 2 + K.constant.toReal ≤
      mainSourceDenominator * (n : ℝ)^2 * K.poincareConstant.toReal := by
  have hfin := K.poincareConstant_lt_top_convex hc
  obtain ⟨a, ha⟩ := hball
  have hi := conditional_reverseBuser_arbitrary_center_IPI K hc hfin (b := 256) (r := 1)
    (by norm_num) (by norm_num) ha hRB
  have hI : K.improvedPoincareConstant < ⊤ := lt_of_le_of_lt hi ENNReal.ofReal_lt_top
  have hir := ENNReal.toReal_mono ENNReal.ofReal_ne_top hi
  have hip : K.improvedPoincareConstant.toReal ≤
      4 * (1036 : ℝ)^2 * (n : ℝ)^2 * K.poincareConstant.toReal := by
    rw [ENNReal.toReal_ofReal (by positivity)] at hir
    simp only [div_one, mul_pow, Real.sq_sqrt ENNReal.toReal_nonneg] at hir
    norm_num at hir
    nlinarith
  have hs := (K.translate (-a)).one_le_innerBall_covariance_scale (r := 1)
    (by norm_num) (K.translate_neg_inner_ball ha)
  rw [K.translate_centeredCovarianceOperator] at hs
  have hcov := K.norm_centeredCovarianceOperator_le hfin
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast NeZero.one_le (n := n)
  have hp : 0 ≤ K.poincareConstant.toReal := ENNReal.toReal_nonneg
  have hscale : 1 ≤ 8 * (n : ℝ)^2 * K.poincareConstant.toReal := by
    have hnc : 8 * (n : ℝ) * ‖K.centeredCovarianceOperator‖ ≤
        8 * (n : ℝ)^2 * K.poincareConstant.toReal := by gcongr <;> nlinarith
    have hs' : 1 ≤ 8 * (n : ℝ) * ‖K.centeredCovarianceOperator‖ := by simpa using hs
    exact hs'.trans hnc
  refine ⟨finite_constant_of_finite_improvedPoincare K hI, ?_⟩
  have hb := constant_toReal_le_improvedPoincare K hI
  dsimp [mainSourceDenominator]
  nlinarith

/-- Explicit numerical source rates bounded by the actual BA rates of both chains. -/
theorem mainSource_rates_le_BA (K : BoundedOpenDomain n) (hc : Convex ℝ K.carrier)
    (hball : (∃ a, Metric.ball a 1 ⊆ K.carrier))
    (hRB : UniversalOrdinaryL1ReverseBuser 256) :
    1 / (mainSourceDenominator * (n : ℝ)^2 * K.poincareConstant.toReal) ≤
      ((n : ℝ)+2) / ((n : ℝ)*(2+K.constant.toReal)) ∧
    1 / (mainSourceDenominator * (n : ℝ)^3 * K.poincareConstant.toReal) ≤
      1 / ((n : ℝ)*K.constant.toReal) := by
  have hb := mainSource_BA_bound K hc hball hRB
  have hn : 0 < (n : ℝ) := by exact_mod_cast NeZero.pos n
  have hp := K.poincareConstant_toReal_pos_convex hc
  have hd := mainSourceDenominator_pos
  have hC := finite_constant_toReal_pos K hb.1
  constructor
  · apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hb.2 hn.le]
  · apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hb.2 hn.le]

/-- Both actual Rayleigh spectral gaps, in the manuscript CPI scale. -/
theorem mainSource_CPI_gaps (K : BoundedOpenDomain n) (hc : Convex ℝ K.carrier)
    (hball : (∃ a, Metric.ball a 1 ⊆ K.carrier))
    (hRB : UniversalOrdinaryL1ReverseBuser 256) :
    1 / (mainSourceDenominator * (n : ℝ)^2 * K.poincareConstant.toReal) ≤
      spectralGap K (hitAndRunOperator K) ∧
    1 / (mainSourceDenominator * (n : ℝ)^3 * K.poincareConstant.toReal) ≤
      spectralGap K (coordinateHeatBath K) := by
  have hb := mainSource_BA_bound K hc hball hRB
  have hr := mainSource_rates_le_BA K hc hball hRB
  exact ⟨hr.1.trans (hitAndRun_source_gap K hb.1),
    hr.2.trans (coordinateHitAndRun_source_gap K hb.1).2⟩
end HitAndRun.Markov
