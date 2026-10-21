module
public import HitAndRun.Geometry.WeightedPoincareBodySourceBody
@[expose] public section
noncomputable section
namespace HitAndRun.Geometry
open MeasureTheory Set HitAndRun.Sobolev
open scoped ENNReal Topology
variable {n : ℕ} [NeZero n]
theorem conditional_reverseBuser_body_infimum
    {K : Set (EuclideanSpace ℝ (Fin n))} (hbK : Bornology.IsBounded K)
    (hi : (interior K).Nonempty) (hc : Convex ℝ K)
    {b r : ℝ} (hb : 0 ≤ b) (hr : 0 < r) {a : EuclideanSpace ℝ (Fin n)}
    (hball : Metric.ball a r ⊆ K) (hRB : UniversalOrdinaryL1ReverseBuser b)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : LocallyLipschitz f) :
    (⨅ z : ℝ, ∫ x in K, |f x-z|) ≤
      ((12+4*b)*(n : ℝ)*Real.sqrt (bodyInteriorDomain K hbK hi).poincareConstant.toReal/r) *
        ∫ x in K, Metric.infDist x (frontier K) * ‖gradient f x‖ := by
  obtain ⟨z, hz⟩ := conditional_reverseBuser_body hbK hi hc hb hr hball hRB f hf
  exact ciInf_le_of_le ⟨0, forall_mem_range.mpr (fun _ => integral_nonneg (fun _ => abs_nonneg _))⟩ z hz
end HitAndRun.Geometry
