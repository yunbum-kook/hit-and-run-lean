module
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
@[expose] public section

/-! Uniform probability as restriction of a genuinely normalized ambient Haar measure. -/
noncomputable section
namespace HitAndRun.Sobolev
open MeasureTheory
open scoped ENNReal
variable {n : ℕ}

/-- Normalize ambient volume by the domain volume, before restricting. -/
def normalizedAmbient (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    Measure (EuclideanSpace ℝ (Fin n)) := (volume Ω)⁻¹ • volume

/-- The actual uniform measure used in the paper. -/
def uniformMeasure (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    Measure (EuclideanSpace ℝ (Fin n)) := (volume Ω)⁻¹ • volume.restrict Ω

theorem normalizedAmbient_restrict (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    (normalizedAmbient Ω).restrict Ω = uniformMeasure Ω := by
  simp [normalizedAmbient, uniformMeasure, Measure.restrict_smul]

/-- Bounded nonempty open domains have positive finite volume, not assumed constants. -/
theorem domain_volume_bounds {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (ho : IsOpen Ω) (hne : Ω.Nonempty) (hb : Bornology.IsBounded Ω) :
    0 < volume Ω ∧ volume Ω < ⊤ :=
  ⟨ho.measure_pos volume hne, hb.measure_lt_top⟩

/-- Positive finite normalization preserves ambient Haar structure. -/
theorem normalizedAmbient_isAddHaarMeasure {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (ho : IsOpen Ω) (hne : Ω.Nonempty) (hb : Bornology.IsBounded Ω) :
    (normalizedAmbient Ω).IsAddHaarMeasure := by
  have h := domain_volume_bounds ho hne hb
  exact MeasureTheory.Measure.IsAddHaarMeasure.smul volume
    (ENNReal.inv_ne_zero.mpr (ne_of_lt h.2)) (ENNReal.inv_ne_top.mpr (ne_of_gt h.1))

/-- The restricted normalized Haar measure is a probability measure. -/
theorem uniformMeasure_isProbabilityMeasure {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (ho : IsOpen Ω) (hne : Ω.Nonempty) (hb : Bornology.IsBounded Ω) :
    IsProbabilityMeasure (uniformMeasure Ω) := by
  have h := domain_volume_bounds ho hne hb
  constructor
  simp only [uniformMeasure, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (ne_of_gt h.1) (ne_of_lt h.2)

/-- Finite-measure instance required by the concrete L2 integration operator. -/
theorem normalizedAmbient_restrict_finite {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (ho : IsOpen Ω) (hne : Ω.Nonempty) (hb : Bornology.IsBounded Ω) :
    IsFiniteMeasure ((normalizedAmbient Ω).restrict Ω) := by
  rw [normalizedAmbient_restrict]
  letI := uniformMeasure_isProbabilityMeasure ho hne hb
  infer_instance
end HitAndRun.Sobolev
