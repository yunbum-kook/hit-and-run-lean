import HitAndRun.Markov.CoordinateKernelIdentificationL2
open Set MeasureTheory ProbabilityTheory HitAndRun.Markov HitAndRun.Geometry HitAndRun.Sobolev
open scoped ENNReal ProbabilityTheory
example {n : ℕ} (i : Fin n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (ho : IsOpen K) (hne : K.Nonempty) (hb : Bornology.IsBounded K)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Integrable f (uniformMeasure K)) :
    (uniformMeasure K)[f | coordinateSigma i] =ᵐ[uniformMeasure K]
      fun x => ∫ y, f y ∂chordLaw K x (EuclideanSpace.basisFun (Fin n) ℝ i) :=
  condExp_eq_coordinateChord i ho hne hb f hf
example {n : ℕ} [NeZero n] (K : BoundedOpenDomain n)
    (f : Lp ℝ 2 (K.ambient.restrict K.carrier)) :
    K.bodyL2Isometry (coordinateHeatBath K f) =ᵐ[K.bodyUniform]
      fun x => ∫ y : K.carrier, f y.val ∂coordinateHitAndRun K.carrier K.isOpen.measurableSet x :=
  coordinateHeatBath_bodyKernel_ae K f
example {n : ℕ} [NeZero n] (K : BoundedOpenDomain n) (hC : K.constant < ⊤) :
    (∀ f : Lp ℝ 2 (K.ambient.restrict K.carrier),
      K.bodyL2Isometry (coordinateHeatBath K f) =ᵐ[K.bodyUniform]
        fun x => ∫ y : K.carrier, f y.val ∂coordinateHitAndRun K.carrier K.isOpen.measurableSet x) ∧
    1 / ((n : ℝ) * K.constant.toReal) ≤ spectralGap K (coordinateHeatBath K) :=
  coordinateHitAndRun_source_gap K hC
#print axioms HitAndRun.Markov.restricted_product_fst
#print axioms HitAndRun.Markov.restricted_product_disintegration
#print axioms HitAndRun.Markov.condDistrib_eq_normalizedSection
#print axioms HitAndRun.Markov.condExp_eq_normalizedSection
#print axioms HitAndRun.Markov.coordinateChart_uniform
#print axioms HitAndRun.Markov.condExp_eq_coordinateChord
#print axioms HitAndRun.Markov.integrable_coordinateChord_ae
#print axioms HitAndRun.Markov.coordinateProjection_bodyKernel_ae
#print axioms HitAndRun.Markov.coordinateChord_congr_ae
#print axioms HitAndRun.Markov.coordinateChord_integral_preserved
#print axioms HitAndRun.Markov.coordinateHeatBath_bodyKernel_ae
#print axioms HitAndRun.Markov.coordinateHitAndRun_source_gap
