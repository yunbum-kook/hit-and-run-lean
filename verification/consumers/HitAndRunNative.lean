import HitAndRun.Markov.HitAndRunOperatorMixing
open MeasureTheory ProbabilityTheory HitAndRun.Sobolev HitAndRun.Markov DikinD2
open scoped ENNReal ProbabilityTheory RealInnerProductSpace
variable {n : ℕ} [NeZero n] (K : BoundedOpenDomain n)
example : (hitAndRunNativeOperator K).IsPositive := hitAndRunNativeOperator_positive K
example : ReversibleSupport.JointReversible
    (hitAndRun K.carrier K.isOpen K.isBounded) K.bodyUniform := hitAndRun_jointReversible K
example (hC : K.constant < ⊤) (ν : Measure K.carrier) [IsProbabilityMeasure ν] (N : ℕ) :
    ChiSquareDensity.chiSquare
      (NativeL2.lawOrbit (hitAndRun K.carrier K.isOpen K.isBounded) ν N) K.bodyUniform ≤
      ChiSquareDensity.chiSquare ν K.bodyUniform *
        ENNReal.ofReal (Real.exp (-2 * (((n : ℝ) + 2) / ((n : ℝ) * (2 + K.constant.toReal))) * N)) :=
  hitAndRun_chiSquare K hC ν N
#print axioms hitAndRunNativeOperator_symmetric
#print axioms hitAndRunNativeOperator_positive
#print axioms hitAndRun_jointReversible
#print axioms hitAndRun_gap_at_most_one
#print axioms hitAndRunNativeOperator_gap
#print axioms hitAndRun_chiSquare
