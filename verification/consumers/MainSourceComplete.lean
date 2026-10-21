import MainSourceComplete
import MixingSourceBudget
noncomputable section
namespace HitAndRun.Markov
open MeasureTheory HitAndRun.Sobolev HitAndRun.Geometry DikinD2
open scoped ENNReal
example
 :
    ∃ D : ℝ, 0 < D ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (n : ℕ) [NeZero n] (K : BoundedOpenDomain n), 2 ≤ n → Convex ℝ K.carrier →
      (∃ a, Metric.ball a 1 ⊆ K.carrier) →
      (c / ((n : ℝ)^2 * ‖K.centeredCovarianceOperator‖ * Real.log n) ≤
          1 / (D * (n : ℝ)^2 * K.poincareConstant.toReal) ∧
        1 / (D * (n : ℝ)^2 * K.poincareConstant.toReal) ≤ spectralGap K (hitAndRunOperator K)) ∧
      (c / ((n : ℝ)^3 * ‖K.centeredCovarianceOperator‖ * Real.log n) ≤
          1 / (D * (n : ℝ)^3 * K.poincareConstant.toReal) ∧
        1 / (D * (n : ℝ)^3 * K.poincareConstant.toReal) ≤ spectralGap K (coordinateHeatBath K)) := mainSource_complete 
#print axioms mainSource_complete

example
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
            (Real.exp (-(c*N) / ((n : ℝ)^3 * ‖K.centeredCovarianceOperator‖ * Real.log n))) := mixingSource_complete 
#print axioms mixingSource_complete

variable {n : ℕ} [NeZero n]
example (K : BoundedOpenDomain n) (hn : 2 ≤ n)
    (hc : Convex ℝ K.carrier) (hball : (∃ a, Metric.ball a 1 ⊆ K.carrier))
    (ν : Measure K.carrier) [IsProbabilityMeasure ν]
    (hM : ChiSquareDensity.chiSquare ν K.bodyUniform < ⊤)
    (ε : ℝ) (hε : 0 < ε) (N : ℕ)
    (hN : mixingBudget (mainSourceConstant /
      ((n : ℝ)^2 * ‖K.centeredCovarianceOperator‖ * Real.log n))
      (ChiSquareDensity.chiSquare ν K.bodyUniform).toReal ε ≤ N) :
    ChiSquareDensity.chiSquare
      (NativeL2.lawOrbit (hitAndRun K.carrier K.isOpen K.isBounded) ν N) K.bodyUniform ≤
      ENNReal.ofReal ε := mixingSource_HAR_accuracy_complete K hn hc hball ν hM ε hε N hN
#print axioms mixingSource_HAR_accuracy_complete

variable {n : ℕ} [NeZero n]
example (K : BoundedOpenDomain n) (hn : 2 ≤ n)
    (hc : Convex ℝ K.carrier) (hball : (∃ a, Metric.ball a 1 ⊆ K.carrier))
    (ν : Measure K.carrier) [IsProbabilityMeasure ν]
    (hM : ChiSquareDensity.chiSquare ν K.bodyUniform < ⊤)
    (ε : ℝ) (hε : 0 < ε) (N : ℕ)
    (hN : mixingBudget (mainSourceConstant /
      ((n : ℝ)^3 * ‖K.centeredCovarianceOperator‖ * Real.log n))
      (ChiSquareDensity.chiSquare ν K.bodyUniform).toReal ε ≤ N) :
    ChiSquareDensity.chiSquare
      (NativeL2.lawOrbit (coordinateHitAndRun K.carrier K.isOpen.measurableSet) ν N) K.bodyUniform ≤
      ENNReal.ofReal ε := mixingSource_CHAR_accuracy_complete K hn hc hball ν hM ε hε N hN
#print axioms mixingSource_CHAR_accuracy_complete

example {n : ℕ} [NeZero n] (K : BoundedOpenDomain n) (hn : 2 ≤ n)
    (hc : Convex ℝ K.carrier) (a : EuclideanSpace ℝ (Fin n))
    (ha : Metric.ball a 1 ⊆ K.carrier) :
    mainSourceConstant / ((n : ℝ)^2 * ‖K.centeredCovarianceOperator‖ * Real.log n) ≤
      spectralGap K (hitAndRunOperator K) ∧
    mainSourceConstant / ((n : ℝ)^3 * ‖K.centeredCovarianceOperator‖ * Real.log n) ≤
      spectralGap K (coordinateHeatBath K) :=
  mainSource_covariance_log_gaps K hn hc ⟨a, ha⟩ universalOrdinaryL1ReverseBuser_256
    (KLS15ProductionAudit.actualSobolev15_real K hc)
end HitAndRun.Markov
