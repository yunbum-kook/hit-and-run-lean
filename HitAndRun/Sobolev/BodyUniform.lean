module
public import HitAndRun.Sobolev.UniformSource
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
@[expose] public section

/-! The genuine subtype uniform measure and its isometric identification with
ambient restricted L². No transport is postulated: it is pullback by inclusion. -/
noncomputable section
namespace HitAndRun.Sobolev.BoundedOpenDomain
open MeasureTheory
open scoped ENNReal
variable {n : ℕ} [NeZero n]

/-- Uniform probability on the actual body subtype. -/
def bodyUniform (K : BoundedOpenDomain n) : Measure K.carrier :=
  (uniformMeasure K.carrier).comap Subtype.val

/-- Inclusion pushes the subtype measure to the ambient uniform measure. -/
theorem bodyUniform_map (K : BoundedOpenDomain n) :
    K.bodyUniform.map Subtype.val = uniformMeasure K.carrier := by
  rw [bodyUniform, map_comap_subtype_coe K.isOpen.measurableSet]
  simp [uniformMeasure, Measure.restrict_smul, Measure.restrict_restrict,
    K.isOpen.measurableSet]

/-- The same pushforward is the normalized ambient restriction used by Sobolev spaces. -/
theorem bodyUniform_map_restrict (K : BoundedOpenDomain n) :
    K.bodyUniform.map Subtype.val = K.ambient.restrict K.carrier := by
  rw [bodyUniform_map, K.measure_eq_uniform]

instance (K : BoundedOpenDomain n) : IsProbabilityMeasure K.bodyUniform := by
  haveI := uniformMeasure_isProbabilityMeasure K.isOpen K.nonempty K.isBounded
  haveI : IsProbabilityMeasure (K.bodyUniform.map Subtype.val) := by
    rw [K.bodyUniform_map]
    infer_instance
  exact Measure.isProbabilityMeasure_of_map measurable_subtype_coe.aemeasurable

/-- Body inclusion is measure-preserving for the actual normalized restriction. -/
theorem bodyUniform_measurePreserving (K : BoundedOpenDomain n) :
    MeasurePreserving (Subtype.val : K.carrier → EuclideanSpace ℝ (Fin n))
      K.bodyUniform (K.ambient.restrict K.carrier) :=
  ⟨measurable_subtype_coe, K.bodyUniform_map_restrict⟩

/-- The concrete pullback linear isometry on scalar L². -/
def bodyL2Isometry (K : BoundedOpenDomain n) :
    Lp ℝ 2 (K.ambient.restrict K.carrier) →ₗᵢ[ℝ] Lp ℝ 2 K.bodyUniform :=
  Lp.compMeasurePreservingₗᵢ ℝ Subtype.val K.bodyUniform_measurePreserving

/-- Representatives are restricted by inclusion, almost everywhere. -/
theorem bodyL2Isometry_coe (K : BoundedOpenDomain n)
    (f : Lp ℝ 2 (K.ambient.restrict K.carrier)) :
    K.bodyL2Isometry f =ᵐ[K.bodyUniform] f ∘ Subtype.val :=
  Lp.coeFn_compMeasurePreserving f K.bodyUniform_measurePreserving

/-- Every subtype L² class extends measurably to an ambient restricted L² class. -/
theorem bodyL2Isometry_surjective (K : BoundedOpenDomain n) :
    Function.Surjective K.bodyL2Isometry := by
  intro f
  obtain ⟨g, hg, heq⟩ :=
    (MeasurableEmbedding.subtype_coe K.isOpen.measurableSet).exists_measurable_extend
      (Lp.stronglyMeasurable f).measurable (fun _ => inferInstance)
  have hgLp : MemLp g 2 (K.ambient.restrict K.carrier) := by
    rw [← K.bodyUniform_map_restrict]
    apply (memLp_map_measure_iff hg.aestronglyMeasurable
      measurable_subtype_coe.aemeasurable).2
    rw [heq]
    exact Lp.memLp f
  refine ⟨hgLp.toLp g, Lp.ext ?_⟩
  apply (K.bodyL2Isometry_coe (hgLp.toLp g)).trans
  have h := K.bodyUniform_measurePreserving.quasiMeasurePreserving.ae_eq_comp
    hgLp.coeFn_toLp
  simpa only [heq] using h

/-- The actual body and ambient restricted scalar L² spaces are linearly isometric. -/
def bodyL2Equiv (K : BoundedOpenDomain n) :
    Lp ℝ 2 (K.ambient.restrict K.carrier) ≃ₗᵢ[ℝ] Lp ℝ 2 K.bodyUniform :=
  LinearIsometryEquiv.ofSurjective K.bodyL2Isometry K.bodyL2Isometry_surjective

@[simp] theorem bodyL2Equiv_apply (K : BoundedOpenDomain n)
    (f : Lp ℝ 2 (K.ambient.restrict K.carrier)) :
    K.bodyL2Equiv f = K.bodyL2Isometry f := rfl

end HitAndRun.Sobolev.BoundedOpenDomain
