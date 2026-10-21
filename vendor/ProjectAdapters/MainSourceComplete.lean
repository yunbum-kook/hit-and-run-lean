module
public import MainSourceUniversal
public import HitAndRun.Geometry.ReverseBuserSource
public import KLS15UniformConsumer
@[expose] public section
noncomputable section
namespace HitAndRun.Markov
open MeasureTheory HitAndRun.Sobolev HitAndRun.Geometry DikinD2
open scoped ENNReal
theorem mainSource_complete
 :
    ∃ D : ℝ, 0 < D ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (n : ℕ) [NeZero n] (K : BoundedOpenDomain n), 2 ≤ n → Convex ℝ K.carrier →
      (∃ a, Metric.ball a 1 ⊆ K.carrier) →
      (c / ((n : ℝ)^2 * ‖K.centeredCovarianceOperator‖ * Real.log n) ≤
          1 / (D * (n : ℝ)^2 * K.poincareConstant.toReal) ∧
        1 / (D * (n : ℝ)^2 * K.poincareConstant.toReal) ≤ spectralGap K (hitAndRunOperator K)) ∧
      (c / ((n : ℝ)^3 * ‖K.centeredCovarianceOperator‖ * Real.log n) ≤
          1 / (D * (n : ℝ)^3 * K.poincareConstant.toReal) ∧
        1 / (D * (n : ℝ)^3 * K.poincareConstant.toReal) ≤ spectralGap K (coordinateHeatBath K)) :=
  mainSource_universal universalOrdinaryL1ReverseBuser_256
    (fun n _ K hc => KLS15ProductionAudit.actualSobolev15_real K hc)

theorem mixingSource_complete
 :
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
            (Real.exp (-(c*N) / ((n : ℝ)^3 * ‖K.centeredCovarianceOperator‖ * Real.log n))) :=
  mixingSource_universal universalOrdinaryL1ReverseBuser_256
    (fun n _ K hc => KLS15ProductionAudit.actualSobolev15_real K hc)

variable {n : ℕ} [NeZero n]
theorem mixingSource_HAR_accuracy_complete (K : BoundedOpenDomain n) (hn : 2 ≤ n)
    (hc : Convex ℝ K.carrier) (hball : (∃ a, Metric.ball a 1 ⊆ K.carrier))
    (ν : Measure K.carrier) [IsProbabilityMeasure ν]
    (hM : ChiSquareDensity.chiSquare ν K.bodyUniform < ⊤)
    (ε : ℝ) (hε : 0 < ε) (N : ℕ)
    (hN : mixingBudget (mainSourceConstant /
      ((n : ℝ)^2 * ‖K.centeredCovarianceOperator‖ * Real.log n))
      (ChiSquareDensity.chiSquare ν K.bodyUniform).toReal ε ≤ N) :
    ChiSquareDensity.chiSquare
      (NativeL2.lawOrbit (hitAndRun K.carrier K.isOpen K.isBounded) ν N) K.bodyUniform ≤
      ENNReal.ofReal ε :=
  mixingSource_HAR_accuracy K hn hc hball universalOrdinaryL1ReverseBuser_256
    (KLS15ProductionAudit.actualSobolev15_real K hc) ν hM ε hε N hN

theorem mixingSource_CHAR_accuracy_complete (K : BoundedOpenDomain n) (hn : 2 ≤ n)
    (hc : Convex ℝ K.carrier) (hball : (∃ a, Metric.ball a 1 ⊆ K.carrier))
    (ν : Measure K.carrier) [IsProbabilityMeasure ν]
    (hM : ChiSquareDensity.chiSquare ν K.bodyUniform < ⊤)
    (ε : ℝ) (hε : 0 < ε) (N : ℕ)
    (hN : mixingBudget (mainSourceConstant /
      ((n : ℝ)^3 * ‖K.centeredCovarianceOperator‖ * Real.log n))
      (ChiSquareDensity.chiSquare ν K.bodyUniform).toReal ε ≤ N) :
    ChiSquareDensity.chiSquare
      (NativeL2.lawOrbit (coordinateHitAndRun K.carrier K.isOpen.measurableSet) ν N) K.bodyUniform ≤
      ENNReal.ofReal ε :=
  mixingSource_CHAR_accuracy K hn hc hball universalOrdinaryL1ReverseBuser_256
    (KLS15ProductionAudit.actualSobolev15_real K hc) ν hM ε hε N hN

end HitAndRun.Markov
