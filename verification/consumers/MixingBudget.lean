import HitAndRun.Markov.MixingAccuracy
open MeasureTheory ProbabilityTheory HitAndRun.Markov HitAndRun.Sobolev DikinD2
open scoped ENNReal ProbabilityTheory
example {r M ε : ℝ} (hr : 0 < r) (hM : 0 ≤ M) (hε : 0 < ε) (N : ℕ)
    (hN : mixingBudget r M ε ≤ N) : M * Real.exp (-2 * r * N) ≤ ε :=
  exp_error_le_accuracy hr hM hε N hN
example (r : ℝ) (N : ℕ) (e : ℝ≥0∞) : e ≤ ⊤ * ENNReal.ofReal (Real.exp (-2 * r * N)) :=
  infinite_initial_error_vacuous r N e
variable {n : ℕ} [NeZero n] (K : BoundedOpenDomain n)
example (hC : K.constant < ⊤) (ν : Measure K.carrier) [IsProbabilityMeasure ν]
    (hM : ChiSquareDensity.chiSquare ν K.bodyUniform < ⊤) (ε : ℝ) (hε : 0 < ε) (N : ℕ)
    (hN : mixingBudget (1 / ((n : ℝ) * K.constant.toReal))
      (ChiSquareDensity.chiSquare ν K.bodyUniform).toReal ε ≤ N) :
    ChiSquareDensity.chiSquare
      (NativeL2.lawOrbit (coordinateHitAndRun K.carrier K.isOpen.measurableSet) ν N) K.bodyUniform ≤
      ENNReal.ofReal ε := coordinateHitAndRun_accuracy K hC ν hM ε hε N hN
example (hC : K.constant < ⊤) (ν : Measure K.carrier) [IsProbabilityMeasure ν]
    (hM : ChiSquareDensity.chiSquare ν K.bodyUniform < ⊤) (ε : ℝ) (hε : 0 < ε) (N : ℕ)
    (hN : mixingBudget (((n : ℝ) + 2) / ((n : ℝ) * (2 + K.constant.toReal)))
      (ChiSquareDensity.chiSquare ν K.bodyUniform).toReal ε ≤ N) :
    ChiSquareDensity.chiSquare
      (NativeL2.lawOrbit (hitAndRun K.carrier K.isOpen K.isBounded) ν N) K.bodyUniform ≤
      ENNReal.ofReal ε := hitAndRun_accuracy K hC ν hM ε hε N hN
#print axioms mixingBudget_zero_step
#print axioms exp_error_le_accuracy
#print axioms ennreal_error_le_accuracy
#print axioms infinite_initial_error_vacuous
#print axioms finite_constant_toReal_pos
#print axioms coordinateHitAndRun_accuracy
#print axioms hitAndRun_accuracy
