import HitAndRun.Sobolev.WeightedPoincareTransfer
open MeasureTheory ProbabilityTheory EllipticPdes EllipticPdes.H1Graph HitAndRun.Sobolev Filter Set
open scoped ENNReal Topology
variable {n : ℕ} [NeZero n] (K : BoundedOpenDomain n)
example {u : ℕ → K.H1} {v : K.H1}
    (hu : Tendsto (fun k => (u k).val) atTop (𝓝 v.val)) :
    Tendsto (fun k => (K.weightedGradientEnergy (u k)).toReal) atTop
      (𝓝 (K.weightedGradientEnergy v).toReal) := K.weightedGradientEnergy_tendsto hu
example {A r : ℝ} (hc : Convex ℝ K.carrier) (hr : 0 < r)
    (hball : Metric.ball 0 r ⊆ K.carrier)
    (hL1 : HitAndRun.Geometry.WeightedL1Bound
      (K.ambient.restrict K.carrier) K.boundaryDistance A) :
    ∀ u : K.H1, K.varianceEnergy u ≤ ENNReal.ofReal (4 * A ^ 2) * K.weightedGradientEnergy u :=
  K.improvedPoincare_of_weightedL1 hc hr hball hL1
example {A r : ℝ} (hc : Convex ℝ K.carrier) (hr : 0 < r)
    (hball : Metric.ball 0 r ⊆ K.carrier)
    (hL1 : HitAndRun.Geometry.WeightedL1Bound
      (K.ambient.restrict K.carrier) K.boundaryDistance A) :
    K.improvedPoincareConstant ≤ ENNReal.ofReal (4 * A ^ 2) :=
  K.improvedPoincareConstant_le_of_weightedL1 hc hr hball hL1
#print axioms DikinD2.Cheeger.exists_probability_median
#print axioms BoundedOpenDomain.boundaryMultiplier_ae
#print axioms BoundedOpenDomain.weightedGradientEnergy_eq_norm
#print axioms BoundedOpenDomain.weightedGradientEnergy_tendsto
#print axioms BoundedOpenDomain.weightedGradientEnergy_smooth
#print axioms BoundedOpenDomain.smooth_variance_of_weightedL1
#print axioms BoundedOpenDomain.improvedPoincare_of_weightedL1
#print axioms BoundedOpenDomain.improvedPoincareConstant_le_of_weightedL1
