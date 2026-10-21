module
public import MainSourceLog
@[expose] public section
noncomputable section
namespace HitAndRun.Markov
open MeasureTheory ProbabilityTheory HitAndRun.Sobolev HitAndRun.Geometry DikinD2
open scoped ENNReal
variable {n : ℕ} [NeZero n]

/-- Exact native-law source exponential bound, including infinite initial error. -/
theorem mixingSource_HAR (K : BoundedOpenDomain n) (hn : 2 ≤ n)
    (hc : Convex ℝ K.carrier) (hball : (∃ a, Metric.ball a 1 ⊆ K.carrier))
    (hRB : UniversalOrdinaryL1ReverseBuser 256)
    (hPI : K.poincareConstant.toReal ≤ 15 * ‖K.centeredCovarianceOperator‖)
    (ν : Measure K.carrier) [IsProbabilityMeasure ν] (N : ℕ) :
    ChiSquareDensity.chiSquare
      (NativeL2.lawOrbit (hitAndRun K.carrier K.isOpen K.isBounded) ν N) K.bodyUniform ≤
      ChiSquareDensity.chiSquare ν K.bodyUniform * ENNReal.ofReal
        (Real.exp (-2 * (mainSourceConstant /
          ((n : ℝ)^2 * ‖K.centeredCovarianceOperator‖ * Real.log n)) * N)) := by
  have hb := mainSource_BA_bound K hc hball hRB
  have hr := (mainSource_log_rate_le_CPI K hn hc hball hPI 2).trans
    (mainSource_rates_le_BA K hc hball hRB).1
  apply (hitAndRun_chiSquare K hb.1 ν N).trans
  gcongr 1
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]

/-- Coordinate native-law source exponential bound, with the same universal constant. -/
theorem mixingSource_CHAR (K : BoundedOpenDomain n) (hn : 2 ≤ n)
    (hc : Convex ℝ K.carrier) (hball : (∃ a, Metric.ball a 1 ⊆ K.carrier))
    (hRB : UniversalOrdinaryL1ReverseBuser 256)
    (hPI : K.poincareConstant.toReal ≤ 15 * ‖K.centeredCovarianceOperator‖)
    (ν : Measure K.carrier) [IsProbabilityMeasure ν] (N : ℕ) :
    ChiSquareDensity.chiSquare
      (NativeL2.lawOrbit (coordinateHitAndRun K.carrier K.isOpen.measurableSet) ν N) K.bodyUniform ≤
      ChiSquareDensity.chiSquare ν K.bodyUniform * ENNReal.ofReal
        (Real.exp (-2 * (mainSourceConstant /
          ((n : ℝ)^3 * ‖K.centeredCovarianceOperator‖ * Real.log n)) * N)) := by
  have hb := mainSource_BA_bound K hc hball hRB
  have hr := (mainSource_log_rate_le_CPI K hn hc hball hPI 3).trans
    (mainSource_rates_le_BA K hc hball hRB).2
  apply (coordinateHitAndRun_chiSquare K hb.1 ν N).trans
  gcongr 1
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]

theorem mixingSource_rate_pos (K : BoundedOpenDomain n) (hn : 2 ≤ n)
    (hball : (∃ a, Metric.ball a 1 ⊆ K.carrier)) (k : ℕ) :
    0 < mainSourceConstant / ((n : ℝ)^k * ‖K.centeredCovarianceOperator‖ * Real.log n) := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hs := mainSource_covariance_pos K hball
  have hl : 0 < Real.log n := Real.log_pos (by linarith)
  have := mainSourceConstant_pos
  positivity

/-- Finite χ² initialization yields the exact integer logarithmic budget, zero if already accurate. -/
theorem mixingSource_HAR_accuracy (K : BoundedOpenDomain n) (hn : 2 ≤ n)
    (hc : Convex ℝ K.carrier) (hball : (∃ a, Metric.ball a 1 ⊆ K.carrier))
    (hRB : UniversalOrdinaryL1ReverseBuser 256)
    (hPI : K.poincareConstant.toReal ≤ 15 * ‖K.centeredCovarianceOperator‖)
    (ν : Measure K.carrier) [IsProbabilityMeasure ν]
    (hM : ChiSquareDensity.chiSquare ν K.bodyUniform < ⊤)
    (ε : ℝ) (hε : 0 < ε) (N : ℕ)
    (hN : mixingBudget (mainSourceConstant /
      ((n : ℝ)^2 * ‖K.centeredCovarianceOperator‖ * Real.log n))
      (ChiSquareDensity.chiSquare ν K.bodyUniform).toReal ε ≤ N) :
    ChiSquareDensity.chiSquare
      (NativeL2.lawOrbit (hitAndRun K.carrier K.isOpen K.isBounded) ν N) K.bodyUniform ≤
      ENNReal.ofReal ε :=
  ennreal_error_le_accuracy (mixingSource_rate_pos K hn hball 2) hε _ _ hM N hN
    (mixingSource_HAR K hn hc hball hRB hPI ν N)

theorem mixingSource_CHAR_accuracy (K : BoundedOpenDomain n) (hn : 2 ≤ n)
    (hc : Convex ℝ K.carrier) (hball : (∃ a, Metric.ball a 1 ⊆ K.carrier))
    (hRB : UniversalOrdinaryL1ReverseBuser 256)
    (hPI : K.poincareConstant.toReal ≤ 15 * ‖K.centeredCovarianceOperator‖)
    (ν : Measure K.carrier) [IsProbabilityMeasure ν]
    (hM : ChiSquareDensity.chiSquare ν K.bodyUniform < ⊤)
    (ε : ℝ) (hε : 0 < ε) (N : ℕ)
    (hN : mixingBudget (mainSourceConstant /
      ((n : ℝ)^3 * ‖K.centeredCovarianceOperator‖ * Real.log n))
      (ChiSquareDensity.chiSquare ν K.bodyUniform).toReal ε ≤ N) :
    ChiSquareDensity.chiSquare
      (NativeL2.lawOrbit (coordinateHitAndRun K.carrier K.isOpen.measurableSet) ν N) K.bodyUniform ≤
      ENNReal.ofReal ε :=
  ennreal_error_le_accuracy (mixingSource_rate_pos K hn hball 3) hε _ _ hM N hN
    (mixingSource_CHAR K hn hc hball hRB hPI ν N)
end HitAndRun.Markov
