module
public import HitAndRun.Markov.CoordinateKernelIdentificationL2
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.Invariance
@[expose] public section

namespace HitAndRun.Markov
open Set MeasureTheory ProbabilityTheory HitAndRun.Geometry HitAndRun.Sobolev
open scoped ENNReal ProbabilityTheory

/-- Bochner integration through actual measure-kernel composition. -/
theorem integral_measure_kernel_comp {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) [SFinite μ] (κ : Kernel A B) [IsSFiniteKernel κ]
    (f : B → ℝ) (hf : Integrable f (κ ∘ₘ μ)) :
    (∫ y, f y ∂(κ ∘ₘ μ)) = ∫ x, (∫ y, f y ∂κ x) ∂μ := by
  rw [Measure.comp_eq_comp_const_apply] at hf ⊢
  exact ProbabilityTheory.Kernel.integral_comp hf

variable {n : ℕ} [NeZero n] (K : BoundedOpenDomain n)

/-- Each genuine coordinate transition preserves the actual subtype uniform probability. -/
theorem coordinateDirection_stationary (i : Fin n) :
    directionKernel K.carrier K.isOpen.measurableSet
      (EuclideanSpace.basisFun (Fin n) ℝ i)
      ((EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one i) ∘ₘ K.bodyUniform = K.bodyUniform := by
  let κ := directionKernel K.carrier K.isOpen.measurableSet
    (EuclideanSpace.basisFun (Fin n) ℝ i)
    ((EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one i)
  letI : IsMarkovKernel κ := directionKernel_markov K.isOpen K.isBounded _ _
  letI := uniformMeasure_isProbabilityMeasure K.isOpen K.nonempty K.isBounded
  let emb := MeasurableEmbedding.subtype_coe K.isOpen.measurableSet
  apply emb.map_injective
  rw [K.bodyUniform_map]
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [emb.integral_map]
  have hf : Integrable (fun y : K.carrier => f y.val) (κ ∘ₘ K.bodyUniform) :=
    emb.integrable_map_iff.1 (f.integrable ((κ ∘ₘ K.bodyUniform).map Subtype.val))
  rw [integral_measure_kernel_comp K.bodyUniform κ _ hf]
  dsimp only [κ]
  simp_rw [directionKernel_integral_subtype K.isOpen K.isBounded]
  have hmp : MeasurePreserving (Subtype.val : K.carrier → EuclideanSpace ℝ (Fin n))
      K.bodyUniform (uniformMeasure K.carrier) :=
    ⟨measurable_subtype_coe, K.bodyUniform_map⟩
  rw [hmp.integral_comp emb (fun x => ∫ y, f y ∂chordLaw K.carrier x
    (EuclideanSpace.basisFun (Fin n) ℝ i))]
  exact coordinateChord_integral_preserved K i f (f.integrable _)

/-- Finite uniform averaging preserves a common invariant measure exactly. -/
theorem finiteAverageKernel_stationary {A ι : Type*} [MeasurableSpace A]
    [Fintype ι] [Nonempty ι] (μ : Measure A) (κ : ι → Kernel A A)
    (hκ : ∀ i, κ i ∘ₘ μ = μ) : finiteAverageKernel κ ∘ₘ μ = μ := by
  ext S hS
  rw [Measure.bind_apply hS (finiteAverageKernel κ).aemeasurable]
  have hi : ∀ i, (∫⁻ x, κ i x S ∂μ) = μ S := by
    intro i
    rw [← Measure.bind_apply hS (κ i).aemeasurable, hκ i]
  change (∫⁻ x, ((Fintype.card ι : ℝ≥0∞)⁻¹ • ∑ i, κ i x) S ∂μ) = μ S
  simp only [Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]
  rw [lintegral_const_mul _ (Finset.measurable_fun_sum _ (fun i _ => (κ i).measurable_coe hS)),
    lintegral_finsetSum _ (fun i _ => (κ i).measurable_coe hS)]
  simp only [hi, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, ENNReal.inv_mul_cancel
    (by exact_mod_cast (Fintype.card_ne_zero : Fintype.card ι ≠ 0)) (ENNReal.natCast_ne_top _), one_mul]

/-- The actual coordinate Hit-and-Run kernel leaves the actual uniform law invariant. -/
theorem coordinateHitAndRun_stationary :
    coordinateHitAndRun K.carrier K.isOpen.measurableSet ∘ₘ K.bodyUniform = K.bodyUniform :=
  finiteAverageKernel_stationary K.bodyUniform _ (coordinateDirection_stationary K)

end HitAndRun.Markov
