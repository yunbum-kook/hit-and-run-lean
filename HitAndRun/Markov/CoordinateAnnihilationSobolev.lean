module
public import HitAndRun.Markov.CoordinateAnnihilationTest
public import HitAndRun.Sobolev.UniformSource
@[expose] public section

namespace HitAndRun.Markov
open MeasureTheory Set EllipticPdes EllipticPdes.H1Graph HitAndRun.Sobolev
variable {n : ℕ} [NeZero n] (K : BoundedOpenDomain n) (i : Fin n)

/-- Cancellation survives restriction to the body and its exact uniform normalization. -/
theorem test_partial_coordinate_integrals (φ : testFunctions K.carrier)
    (s : Set (EuclideanSpace ℝ (Fin n))) (hs : MeasurableSet[coordinateSigma i] s) :
    (∫ x in s, fderiv ℝ (φ : EuclideanSpace ℝ (Fin n) → ℝ) x
      (EuclideanSpace.basisFun (Fin n) ℝ i) ∂(K.ambient.restrict K.carrier)) = 0 := by
  have hs0 := coordinateSigma_le i s hs
  let d : EuclideanSpace ℝ (Fin n) → ℝ := fun x =>
    fderiv ℝ (φ : EuclideanSpace ℝ (Fin n) → ℝ) x (EuclideanSpace.basisFun (Fin n) ℝ i)
  have hd : (∫ x in s, d x ∂(volume.restrict K.carrier)) = ∫ x in s, d x := by
    rw [Measure.restrict_restrict hs0, inter_comm,
      ← Measure.restrict_restrict K.isOpen.measurableSet]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    dsimp [d]
    rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (φ.2.2.2 h))]
    simp
  change (∫ x in s, d x ∂((volume K.carrier)⁻¹ • volume).restrict K.carrier) = 0
  simp only [Measure.restrict_smul, integral_smul_measure]
  rw [hd]
  rcases hs with ⟨t, ht, rfl⟩
  have hz := integral_coordinate_cylinder_zero i φ t
  change (∫ x in (fun y => (coordinateChart i y).1) ⁻¹' t, d x) = 0 at hz
  rw [hz]
  simp

/-- Every actual compact smooth test derivative is killed by the coordinate projection. -/
theorem test_partial_coordinate_projection (φ : testFunctions K.carrier) :
    conditionalProjection (coordinateSigma_le i)
      (partialCls K.ambient K.carrier φ (EuclideanSpace.basisFun (Fin n) ℝ i)) = 0 := by
  apply conditionalProjection_eq_zero_of_integrals
  intro s hs _
  rw [integral_congr_ae (ae_restrict_of_ae
    (coeFn_partialCls φ (EuclideanSpace.basisFun (Fin n) ℝ i)))]
  exact test_partial_coordinate_integrals K i φ s hs

/-- Coordinate heat-bath cancellation is proved on genuine H01 by closure,
not assumed as a property of an abstract divergence certificate. -/
theorem h01_partial_coordinate_projection (u : H01 K.ambient K.carrier) :
    conditionalProjection (coordinateSigma_le i)
      (partialL (EuclideanSpace.basisFun (Fin n) ℝ i) (u : H1Graph K.ambient K.carrier)) = 0 := by
  apply H01_subset_of_isClosed
    (isClosed_eq
      (((condExpL2 ℝ ℝ (coordinateSigma_le i)).continuous.subtype_val).comp
        (partialL (EuclideanSpace.basisFun (Fin n) ℝ i)).continuous)
      continuous_const)
    (fun φ => ?_) u.property
  change conditionalProjection (coordinateSigma_le i)
    (partialL (EuclideanSpace.basisFun (Fin n) ℝ i) (testGraphₗ K.ambient K.carrier φ)) = 0
  rw [partialL_testGraphₗ]
  exact test_partial_coordinate_projection K i φ

/-- Actual coordinate projection preserves the ambient uniform mean. -/
theorem coordinateProjection_mean (f : Lp ℝ 2 (K.ambient.restrict K.carrier)) :
    meanCLM K.ambient K.carrier (conditionalProjection (coordinateSigma_le i) f) =
      meanCLM K.ambient K.carrier f := by
  rw [meanCLM_eq_integral, meanCLM_eq_integral]
  have h := integral_condExpL2_eq_of_fin_meas_real (hm := coordinateSigma_le i) f
    MeasurableSet.univ (measure_ne_top (K.ambient.restrict K.carrier) univ)
  simpa only [setIntegral_univ, conditionalProjection] using h

/-- The same result for the actual closed gradient-range carrier. -/
theorem gradient_partial_coordinate_projection (w : gradientSpace K.ambient K.carrier) :
    conditionalProjection (coordinateSigma_le i)
      ((innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)).compLpL 2
        (K.ambient.restrict K.carrier) (w : Lp (EuclideanSpace ℝ (Fin n)) 2
          (K.ambient.restrict K.carrier))) = 0 := by
  rcases w.property with ⟨u, hu⟩
  rw [← hu]
  exact h01_partial_coordinate_projection K i u

end HitAndRun.Markov
