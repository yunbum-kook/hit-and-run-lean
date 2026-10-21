module
public import HitAndRun.Markov.MixingAccuracy
public import HitAndRun.Sobolev.BabuskaAzizSource
@[expose] public section
namespace HitAndRun.Markov
open HitAndRun.Sobolev
variable {n : ℕ} [NeZero n] (K : BoundedOpenDomain n)

/-- Actual finite IPI implies finite divergence constant. -/
theorem finite_constant_of_finite_improvedPoincare
    (hI : K.improvedPoincareConstant < ⊤) : K.constant < ⊤ :=
  lt_of_le_of_lt (K.constant_le_of_finite_improvedPoincare hI) ENNReal.ofReal_lt_top

/-- Actual numerical comparison, with finiteness established before taking real values. -/
theorem constant_toReal_le_improvedPoincare
    (hI : K.improvedPoincareConstant < ⊤) :
    K.constant.toReal ≤ 1 + 4 * K.improvedPoincareConstant.toReal := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (K.constant_le_of_finite_improvedPoincare hI)
  simpa only [ENNReal.toReal_ofReal (by positivity :
    0 ≤ 1 + 4 * K.improvedPoincareConstant.toReal)] using h

/-- The actual nonlazy HAR spectral gap in terms of the actual finite IPI. -/
theorem hitAndRun_gap_of_improvedPoincare (hI : K.improvedPoincareConstant < ⊤) :
    ((n : ℝ) + 2) / ((n : ℝ) * (3 + 4 * K.improvedPoincareConstant.toReal)) ≤
      spectralGap K (hitAndRunOperator K) := by
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have hb := constant_toReal_le_improvedPoincare K hI
  apply le_trans _ (hitAndRun_source_gap K (finite_constant_of_finite_improvedPoincare K hI))
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  exact mul_le_mul_of_nonneg_left (by linarith) hn.le

/-- The actual nonlazy coordinate HAR spectral gap in terms of the actual finite IPI. -/
theorem coordinateHitAndRun_gap_of_improvedPoincare
    (hI : K.improvedPoincareConstant < ⊤) :
    1 / ((n : ℝ) * (1 + 4 * K.improvedPoincareConstant.toReal)) ≤
      spectralGap K (coordinateHeatBath K) := by
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have hC := finite_constant_of_finite_improvedPoincare K hI
  have hp := finite_constant_toReal_pos K hC
  apply le_trans _ (coordinateHitAndRun_source_gap K hC).2
  apply div_le_div_of_nonneg_left (by norm_num) (mul_pos hn hp)
  exact mul_le_mul_of_nonneg_left (constant_toReal_le_improvedPoincare K hI) hn.le
end HitAndRun.Markov
