module
public import HitAndRun.Geometry.WeightedPoincareConditionalSource
@[expose] public section
noncomputable section
open MeasureTheory HitAndRun.Geometry HitAndRun.Sobolev
open scoped ENNReal Topology
variable {n : ℕ} [NeZero n]
example (K : BoundedOpenDomain n)
    (hc : Convex ℝ K.carrier) (hfin : K.poincareConstant < ⊤)
    {b r : ℝ} (hb : 0 ≤ b) (hr : 0 < r) (hball : Metric.ball 0 r ⊆ K.carrier)
    (hRB : K.OrdinaryL1ReverseBuserInput b)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : LocallyLipschitz f) :
    ∃ z : ℝ, (∫ x in K.carrier, |f x-z| ∂K.ambient) ≤
      ((12 + 4*b) * (n : ℝ) * Real.sqrt K.poincareConstant.toReal / r) *
        ∫ x in K.carrier, K.boundaryDistance x * ‖gradient f x‖ ∂K.ambient := by
  exact BoundedOpenDomain.conditional_reverseBuser_locallyLipschitz K hc hfin hb hr hball hRB f hf
example (K : BoundedOpenDomain n)
    (hc : Convex ℝ K.carrier) (hfin : K.poincareConstant < ⊤)
    {b r : ℝ} (hb : 0 ≤ b) (hr : 0 < r) (hball : Metric.ball 0 r ⊆ K.carrier)
    (hRB : K.OrdinaryL1ReverseBuserInput b) :
    K.improvedPoincareConstant ≤ ENNReal.ofReal
      (4 * (((12 + 4*b) * (n : ℝ) * Real.sqrt K.poincareConstant.toReal / r) ^ 2)) := by
  exact BoundedOpenDomain.conditional_reverseBuser_IPI K hc hfin hb hr hball hRB
#print axioms BoundedOpenDomain.conditional_reverseBuser_weighted_center
#print axioms BoundedOpenDomain.conditional_reverseBuser_C1WeightedL1
#print axioms BoundedOpenDomain.conditional_reverseBuser_locallyLipschitz
#print axioms BoundedOpenDomain.conditional_reverseBuser_IPI
