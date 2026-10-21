module
public import HitAndRun.Markov.DirectionalAnnihilationTest
public import HitAndRun.Sobolev.UniformSource
@[expose] public section

namespace HitAndRun.Markov
open MeasureTheory Set EllipticPdes EllipticPdes.H1Graph HitAndRun.Sobolev
variable {n : ℕ} [NeZero n] (K : BoundedOpenDomain n) (θ : HitAndRun.Geometry.UnitDirection n)

/-- Cancellation survives restriction to the body and its exact uniform normalization. -/
theorem test_directional_integrals (φ : testFunctions K.carrier)
    (s : Set (EuclideanSpace ℝ (Fin n))) (hs : MeasurableSet[directionalSigma θ] s) :
    (∫ x in s, fderiv ℝ (φ : EuclideanSpace ℝ (Fin n) → ℝ) x
      θ ∂(K.ambient.restrict K.carrier)) = 0 := by
  have hs0 := directionalSigma_le θ s hs
  let d : EuclideanSpace ℝ (Fin n) → ℝ := fun x =>
    fderiv ℝ (φ : EuclideanSpace ℝ (Fin n) → ℝ) x θ
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
  have hz := integral_directional_cylinder_zero θ φ t
  change (∫ x in directionQuotient θ ⁻¹' t, d x) = 0 at hz
  rw [hz]
  simp

/-- Every actual compact smooth test derivative is killed by the directional projection. -/
theorem test_directional_projection (φ : testFunctions K.carrier) :
    conditionalProjection (directionalSigma_le θ)
      (partialCls K.ambient K.carrier φ θ) = 0 := by
  apply conditionalProjection_eq_zero_of_integrals
  intro s hs _
  rw [integral_congr_ae (ae_restrict_of_ae
    (coeFn_partialCls φ θ))]
  exact test_directional_integrals K θ φ s hs

/-- Directional heat-bath cancellation is proved on genuine H01 by closure,
not assumed as a property of an abstract divergence certificate. -/
theorem h01_directional_projection (u : H01 K.ambient K.carrier) :
    conditionalProjection (directionalSigma_le θ)
      (partialL (θ : EuclideanSpace ℝ (Fin n)) (u : H1Graph K.ambient K.carrier)) = 0 := by
  apply H01_subset_of_isClosed
    (isClosed_eq
      (((condExpL2 ℝ ℝ (directionalSigma_le θ)).continuous.subtype_val).comp
        (partialL (θ : EuclideanSpace ℝ (Fin n))).continuous)
      continuous_const)
    (fun φ => ?_) u.property
  change conditionalProjection (directionalSigma_le θ)
    (partialL (θ : EuclideanSpace ℝ (Fin n)) (testGraphₗ K.ambient K.carrier φ)) = 0
  rw [partialL_testGraphₗ]
  exact test_directional_projection K θ φ


end HitAndRun.Markov
