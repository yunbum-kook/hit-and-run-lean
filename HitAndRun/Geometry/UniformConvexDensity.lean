module
public import HitAndRun.Sobolev.UniformSource
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Analysis.Convex.Function
@[expose] public section
noncomputable section
namespace HitAndRun.Sobolev.BoundedOpenDomain
open MeasureTheory Set
open scoped ENNReal
variable {n : ℕ}

/-- The actual normalized Lebesgue indicator density, not an abstract probability witness. -/
def uniformDensity (K : BoundedOpenDomain n) : EuclideanSpace ℝ (Fin n) → ℝ :=
  K.carrier.indicator (fun _ => (volume K.carrier).toReal⁻¹)

theorem uniformDensity_normalizer_pos (K : BoundedOpenDomain n) :
    0 < (volume K.carrier).toReal⁻¹ := by
  have h := domain_volume_bounds K.isOpen K.nonempty K.isBounded
  exact inv_pos.mpr (ENNReal.toReal_pos h.1.ne' h.2.ne)

theorem uniformDensity_nonnegative (K : BoundedOpenDomain n) (x) :
    0 ≤ K.uniformDensity x := by
  exact indicator_nonneg (fun _ _ => K.uniformDensity_normalizer_pos.le) x

theorem uniformDensity_measurable (K : BoundedOpenDomain n) :
    Measurable K.uniformDensity :=
  measurable_const.indicator K.isOpen.measurableSet

theorem uniformDensity_positive_support (K : BoundedOpenDomain n) :
    {x | 0 < K.uniformDensity x} = K.carrier := by
  ext x
  by_cases hx : x ∈ K.carrier
  · simp [uniformDensity, hx, K.uniformDensity_normalizer_pos]
  · simp [uniformDensity, hx]

theorem uniformDensity_withDensity (K : BoundedOpenDomain n) :
    volume.withDensity (fun x => ENNReal.ofReal (K.uniformDensity x)) =
      uniformMeasure K.carrier := by
  have h := domain_volume_bounds K.isOpen K.nonempty K.isBounded
  have he : (fun x => ENNReal.ofReal (K.uniformDensity x)) =
      K.carrier.indicator (fun _ => (volume K.carrier)⁻¹) := by
    funext x
    by_cases hx : x ∈ K.carrier
    · simp [uniformDensity, hx, ENNReal.ofReal_inv_of_pos
        (ENNReal.toReal_pos h.1.ne' h.2.ne), ENNReal.ofReal_toReal h.2.ne]
    · simp [uniformDensity, hx]
  rw [he, withDensity_indicator K.isOpen.measurableSet, withDensity_const]
  rfl

theorem uniformDensity_probability (K : BoundedOpenDomain n) :
    IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (K.uniformDensity x))) := by
  rw [K.uniformDensity_withDensity]
  exact uniformMeasure_isProbabilityMeasure K.isOpen K.nonempty K.isBounded

theorem uniformDensity_log_concave (K : BoundedOpenDomain n)
    (hc : Convex ℝ K.carrier) :
    ConcaveOn ℝ {x | 0 < K.uniformDensity x} (fun x => Real.log (K.uniformDensity x)) := by
  rw [K.uniformDensity_positive_support]
  apply (concaveOn_const (Real.log ((volume K.carrier).toReal⁻¹)) hc).congr
  intro x hx
  simp [uniformDensity, hx]

end HitAndRun.Sobolev.BoundedOpenDomain
