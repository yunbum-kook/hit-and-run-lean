import HitAndRun.Sobolev.BodyUniform
noncomputable section
open MeasureTheory HitAndRun.Sobolev
open scoped ENNReal
variable {n : ℕ} [NeZero n]
example (K : BoundedOpenDomain n) : IsProbabilityMeasure K.bodyUniform := inferInstance
example (K : BoundedOpenDomain n) :
    K.bodyUniform.map Subtype.val = uniformMeasure K.carrier := K.bodyUniform_map
example (K : BoundedOpenDomain n) :
    Lp ℝ 2 (K.ambient.restrict K.carrier) ≃ₗᵢ[ℝ] Lp ℝ 2 K.bodyUniform := K.bodyL2Equiv
example (K : BoundedOpenDomain n) (f : Lp ℝ 2 K.bodyUniform) :
    ∃ g : Lp ℝ 2 (K.ambient.restrict K.carrier), K.bodyL2Equiv g = f :=
  K.bodyL2Equiv.surjective f
#print axioms BoundedOpenDomain.bodyUniform_map
#print axioms BoundedOpenDomain.bodyUniform_map_restrict
#print axioms BoundedOpenDomain.bodyUniform_measurePreserving
#print axioms BoundedOpenDomain.bodyL2Isometry
#print axioms BoundedOpenDomain.bodyL2Isometry_coe
#print axioms BoundedOpenDomain.bodyL2Isometry_surjective
#print axioms BoundedOpenDomain.bodyL2Equiv
