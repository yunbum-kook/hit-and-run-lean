module
public import HitAndRun.Geometry.UniformConvexDensity
@[expose] public section
noncomputable section
open MeasureTheory HitAndRun.Sobolev
open scoped ENNReal
variable {n : ℕ}
example (K : BoundedOpenDomain n) (hc : Convex ℝ K.carrier) :
    (∀ x, 0 ≤ K.uniformDensity x) ∧ Measurable K.uniformDensity ∧
    IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (K.uniformDensity x))) ∧
    ConcaveOn ℝ {x | 0 < K.uniformDensity x} (fun x => Real.log (K.uniformDensity x)) :=
  ⟨K.uniformDensity_nonnegative, K.uniformDensity_measurable,
    K.uniformDensity_probability, K.uniformDensity_log_concave hc⟩
example (K : BoundedOpenDomain n) :
    volume.withDensity (fun x => ENNReal.ofReal (K.uniformDensity x)) =
      uniformMeasure K.carrier := K.uniformDensity_withDensity
#print axioms BoundedOpenDomain.uniformDensity_normalizer_pos
#print axioms BoundedOpenDomain.uniformDensity_nonnegative
#print axioms BoundedOpenDomain.uniformDensity_measurable
#print axioms BoundedOpenDomain.uniformDensity_positive_support
#print axioms BoundedOpenDomain.uniformDensity_withDensity
#print axioms BoundedOpenDomain.uniformDensity_probability
#print axioms BoundedOpenDomain.uniformDensity_log_concave
