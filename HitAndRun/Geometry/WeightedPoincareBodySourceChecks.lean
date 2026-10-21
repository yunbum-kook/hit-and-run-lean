module
public import HitAndRun.Geometry.WeightedPoincareBodySourceExact
@[expose] public section
noncomputable section
open MeasureTheory Set HitAndRun.Sobolev HitAndRun.Geometry
open scoped ENNReal Topology
variable {n : ℕ} [NeZero n]
example
    {K : Set (EuclideanSpace ℝ (Fin n))} (hbK : Bornology.IsBounded K)
    (hi : (interior K).Nonempty) (hc : Convex ℝ K)
    {b r : ℝ} (hb : 0 ≤ b) (hr : 0 < r) {a : EuclideanSpace ℝ (Fin n)}
    (hball : Metric.ball a r ⊆ K) (hRB : UniversalOrdinaryL1ReverseBuser b)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : LocallyLipschitz f) :
    ∃ z : ℝ, (∫ x in K, |f x-z|) ≤
      ((12+4*b)*(n : ℝ)*Real.sqrt (bodyInteriorDomain K hbK hi).poincareConstant.toReal/r) *
        ∫ x in K, Metric.infDist x (frontier K) * ‖gradient f x‖ := by
  exact conditional_reverseBuser_body hbK hi hc hb hr hball hRB f hf
example
    {K : Set (EuclideanSpace ℝ (Fin n))} (hbK : Bornology.IsBounded K)
    (hi : (interior K).Nonempty) (hc : Convex ℝ K)
    {b : ℝ} (hb : 0 ≤ b) (hRB : UniversalOrdinaryL1ReverseBuser b) :
    let Ω := bodyInteriorDomain K hbK hi
    let r := sSup {r : ℝ | 0 < r ∧ ∃ c, Metric.ball c r ⊆ K}
    Ω.improvedPoincareConstant ≤ ENNReal.ofReal
      (4 * (((12+4*b)*(n : ℝ)*Real.sqrt Ω.poincareConstant.toReal/r)^2)) := by
  exact conditional_reverseBuser_body_maximum_IPI hbK hi hc hb hRB
#print axioms conditional_reverseBuser_arbitrary_center
#print axioms conditional_reverseBuser_arbitrary_center_IPI
#print axioms conditional_reverseBuser_body
#print axioms conditional_reverseBuser_body_maximum_IPI

example
    {K : Set (EuclideanSpace ℝ (Fin n))} (hbK : Bornology.IsBounded K)
    (hi : (interior K).Nonempty) (hc : Convex ℝ K)
    {b r : ℝ} (hb : 0 ≤ b) (hr : 0 < r) {a : EuclideanSpace ℝ (Fin n)}
    (hball : Metric.ball a r ⊆ K) (hRB : UniversalOrdinaryL1ReverseBuser b)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : LocallyLipschitz f) :
    (⨅ z : ℝ, ∫ x in K, |f x-z|) ≤
      ((12+4*b)*(n : ℝ)*Real.sqrt (bodyInteriorDomain K hbK hi).poincareConstant.toReal/r) *
        ∫ x in K, Metric.infDist x (frontier K) * ‖gradient f x‖ := by
  exact conditional_reverseBuser_body_infimum hbK hi hc hb hr hball hRB f hf
#print axioms conditional_reverseBuser_body_infimum
