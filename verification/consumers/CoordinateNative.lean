import HitAndRun.Markov.CoordinateKernelIdentificationMixing
open MeasureTheory ProbabilityTheory HitAndRun.Sobolev HitAndRun.Markov DikinD2
open scoped ENNReal ProbabilityTheory RealInnerProductSpace
variable {n : ℕ} [NeZero n] (K : BoundedOpenDomain n)
example : coordinateHitAndRun K.carrier K.isOpen.measurableSet ∘ₘ K.bodyUniform = K.bodyUniform :=
  coordinateHitAndRun_stationary K
example (f : Lp ℝ 2 (K.ambient.restrict K.carrier)) :
    coordinateNativeOperator K (K.bodyL2Isometry f) = K.bodyL2Isometry (coordinateHeatBath K f) :=
  coordinateNativeOperator_conjugate K f
example : ReversibleSupport.JointReversible
    (coordinateHitAndRun K.carrier K.isOpen.measurableSet) K.bodyUniform :=
  coordinateHitAndRun_jointReversible K
example (hC : K.constant < ⊤) (ν : Measure K.carrier) [IsProbabilityMeasure ν] (N : ℕ) :
    ChiSquareDensity.chiSquare
      (NativeL2.lawOrbit (coordinateHitAndRun K.carrier K.isOpen.measurableSet) ν N) K.bodyUniform ≤
      ChiSquareDensity.chiSquare ν K.bodyUniform *
        ENNReal.ofReal (Real.exp (-2 * (1 / ((n : ℝ) * K.constant.toReal)) * N)) :=
  coordinateHitAndRun_chiSquare K hC ν N
#print axioms integral_measure_kernel_comp
#print axioms coordinateDirection_stationary
#print axioms finiteAverageKernel_stationary
#print axioms coordinateHitAndRun_stationary
#print axioms coordinateNativeOperator_conjugate
#print axioms coordinateNativeOperator_symmetric
#print axioms coordinateNativeOperator_positive
#print axioms jointReversible_of_native_symmetric
#print axioms coordinateHitAndRun_jointReversible
#print axioms coordinate_gap_at_most_one
#print axioms coordinateNativeOperator_gap
#print axioms coordinateHitAndRun_chiSquare
