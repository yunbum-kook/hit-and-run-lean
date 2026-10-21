module
public import HitAndRun.Geometry.WeightedPoincareLipschitzExtension
@[expose] public section
noncomputable section
open MeasureTheory EllipticPdes EllipticPdes.H1Graph Set Filter HitAndRun.Sobolev HitAndRun.Geometry
open scoped Topology ENNReal RealInnerProductSpace
variable {n : ℕ} [NeZero n]
example (K : BoundedOpenDomain n)
    (hc : Convex ℝ K.carrier) {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball 0 r ⊆ K.carrier) {A : ℝ}
    (hbound : ∀ u : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ (⊤ : ℕ∞) u →
      ∃ z : ℝ, (∫ x in K.carrier, ‖u x - z‖ ∂K.ambient) ≤
        A * ∫ x in K.carrier, K.boundaryDistance x * ‖gradient u x‖ ∂K.ambient)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : LocallyLipschitz f) :
    ∃ m : ℝ, (∫ x in K.carrier, ‖f x - m‖ ∂K.ambient) ≤
      A * ∫ x in K.carrier, K.boundaryDistance x * ‖gradient f x‖ ∂K.ambient := by
  exact locallyLipschitz_exists_center_bound_of_smooth K hc hr hball hbound f hf
#print axioms locallyLipschitz_exists_center_bound_of_smooth
#print axioms locallyLipschitz_center_bound_of_smooth
#print axioms minimizing_center_bound_of_L1_limit
#print axioms tendsto_integral_weighted_norm_of_sq
