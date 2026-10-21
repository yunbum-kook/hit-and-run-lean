module
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
@[expose] public section

/-! The normalized spherical measure obtained from actual Euclidean volume. -/
namespace HitAndRun.Geometry
open MeasureTheory Set
open scoped ENNReal

abbrev UnitDirection (n : ℕ) := Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1

noncomputable def uniformSphere (n : ℕ) [NeZero n] : Measure (UnitDirection n) :=
  (((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) univ)⁻¹ •
    (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere

theorem uniformSphere_probability (n : ℕ) [NeZero n] :
    IsProbabilityMeasure (uniformSphere n) := by
  have hn : (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere ≠ 0 :=
    Measure.toSphere_ne_zero volume
  constructor
  simp only [uniformSphere, Measure.smul_apply, smul_eq_mul]
  apply ENNReal.inv_mul_cancel
  · intro hz
    exact hn (Measure.measure_univ_eq_zero.mp hz)
  · exact measure_ne_top _ _

end HitAndRun.Geometry
