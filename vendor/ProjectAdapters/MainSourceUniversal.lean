module
public import MixingSource
@[expose] public section
noncomputable section
namespace HitAndRun.Markov
open MeasureTheory HitAndRun.Sobolev HitAndRun.Geometry DikinD2
open scoped ENNReal

/-- Source-form universal quantifier order, with both external analytic inputs visible.
No source completion is asserted until those inputs are supplied by verified theorems. -/
theorem mainSource_universal
    (hRB : UniversalOrdinaryL1ReverseBuser 256)
    (hPI : ∀ (n : ℕ) [NeZero n] (K : BoundedOpenDomain n), Convex ℝ K.carrier →
      K.poincareConstant.toReal ≤ 15 * ‖K.centeredCovarianceOperator‖) :
    ∃ D : ℝ, 0 < D ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (n : ℕ) [NeZero n] (K : BoundedOpenDomain n), 2 ≤ n → Convex ℝ K.carrier →
      (∃ a, Metric.ball a 1 ⊆ K.carrier) →
      (c / ((n : ℝ)^2 * ‖K.centeredCovarianceOperator‖ * Real.log n) ≤
          1 / (D * (n : ℝ)^2 * K.poincareConstant.toReal) ∧
        1 / (D * (n : ℝ)^2 * K.poincareConstant.toReal) ≤ spectralGap K (hitAndRunOperator K)) ∧
      (c / ((n : ℝ)^3 * ‖K.centeredCovarianceOperator‖ * Real.log n) ≤
          1 / (D * (n : ℝ)^3 * K.poincareConstant.toReal) ∧
        1 / (D * (n : ℝ)^3 * K.poincareConstant.toReal) ≤ spectralGap K (coordinateHeatBath K)) := by
  refine ⟨mainSourceDenominator, mainSourceDenominator_pos,
    mainSourceConstant, mainSourceConstant_pos, ?_⟩
  intro n inst K hn hc hb
  have hg := mainSource_CPI_gaps K hc hb hRB
  exact ⟨⟨mainSource_log_rate_le_CPI K hn hc hb (hPI n K hc) 2, hg.1⟩,
    ⟨mainSource_log_rate_le_CPI K hn hc hb (hPI n K hc) 3, hg.2⟩⟩

/-- One universal positive exponential constant for both actual native algorithms.
The law is arbitrary, so infinite initial χ² remains included (vacuously). -/
theorem mixingSource_universal
    (hRB : UniversalOrdinaryL1ReverseBuser 256)
    (hPI : ∀ (n : ℕ) [NeZero n] (K : BoundedOpenDomain n), Convex ℝ K.carrier →
      K.poincareConstant.toReal ≤ 15 * ‖K.centeredCovarianceOperator‖) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (n : ℕ) [NeZero n] (K : BoundedOpenDomain n), 2 ≤ n → Convex ℝ K.carrier →
      (∃ a, Metric.ball a 1 ⊆ K.carrier) → ∀ (ν : Measure K.carrier) [IsProbabilityMeasure ν] (N : ℕ),
      ChiSquareDensity.chiSquare
        (NativeL2.lawOrbit (hitAndRun K.carrier K.isOpen K.isBounded) ν N) K.bodyUniform ≤
          ChiSquareDensity.chiSquare ν K.bodyUniform * ENNReal.ofReal
            (Real.exp (-(c*N) / ((n : ℝ)^2 * ‖K.centeredCovarianceOperator‖ * Real.log n))) ∧
      ChiSquareDensity.chiSquare
        (NativeL2.lawOrbit (coordinateHitAndRun K.carrier K.isOpen.measurableSet) ν N) K.bodyUniform ≤
          ChiSquareDensity.chiSquare ν K.bodyUniform * ENNReal.ofReal
            (Real.exp (-(c*N) / ((n : ℝ)^3 * ‖K.centeredCovarianceOperator‖ * Real.log n))) := by
  refine ⟨2 * mainSourceConstant, mul_pos (by norm_num) mainSourceConstant_pos, ?_⟩
  intro n inst K hn hc hb ν instν N
  have he (d : ℝ) : -(2 * mainSourceConstant * N) / d =
      -2 * (mainSourceConstant / d) * N := by ring
  simp_rw [he]
  exact ⟨mixingSource_HAR K hn hc hb hRB (hPI n K hc) ν N,
    mixingSource_CHAR K hn hc hb hRB (hPI n K hc) ν N⟩
end HitAndRun.Markov
