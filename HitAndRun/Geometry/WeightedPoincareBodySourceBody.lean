module
public import HitAndRun.Geometry.WeightedPoincareBodySource
public import HitAndRun.Geometry.ConvexPoincareFinite
@[expose] public section
noncomputable section
namespace HitAndRun.Geometry
open MeasureTheory Set HitAndRun.Sobolev
open scoped ENNReal Topology
variable {n : ℕ} [NeZero n]

/-- Literal Lebesgue/body S07 form, conditional on the explicitly universal
ordinary L1 input. The inner ball may have any center. -/
theorem conditional_reverseBuser_body
    {K : Set (EuclideanSpace ℝ (Fin n))} (hbK : Bornology.IsBounded K)
    (hi : (interior K).Nonempty) (hc : Convex ℝ K)
    {b r : ℝ} (hb : 0 ≤ b) (hr : 0 < r) {a : EuclideanSpace ℝ (Fin n)}
    (hball : Metric.ball a r ⊆ K) (hRB : UniversalOrdinaryL1ReverseBuser b)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : LocallyLipschitz f) :
    ∃ z : ℝ, (∫ x in K, |f x-z|) ≤
      ((12+4*b)*(n : ℝ)*Real.sqrt (bodyInteriorDomain K hbK hi).poincareConstant.toReal/r) *
        ∫ x in K, Metric.infDist x (frontier K) * ‖gradient f x‖ := by
  let Ω := bodyInteriorDomain K hbK hi
  obtain ⟨z, hz⟩ := conditional_reverseBuser_arbitrary_center Ω hc.interior (Ω.poincareConstant_lt_top_convex hc.interior) hb hr
    (bodyInteriorDomain_ball hbK hi hball) hRB f hf
  refine ⟨z, ?_⟩
  rw [convex_integral_interior hc (fun x => |f x-z|),
    convex_boundary_weighted_integral_interior hc hi (fun x => ‖gradient f x‖)]
  change (∫ x in Ω.carrier, |f x-z|) ≤
    ((12+4*b)*(n : ℝ)*Real.sqrt Ω.poincareConstant.toReal/r) *
      ∫ x in Ω.carrier, Ω.boundaryDistance x * ‖gradient f x‖
  rw [Ω.integral_volume_eq_uniform (fun x => |f x-z|),
    Ω.integral_volume_eq_uniform (fun x => Ω.boundaryDistance x * ‖gradient f x‖)]
  convert mul_le_mul_of_nonneg_left hz (ENNReal.toReal_nonneg (a := volume Ω.carrier)) using 1 <;> ring

/-- Literal maximum-inscribed-radius S08 form. Neither a maximizing center nor
an attained-radius hypothesis is supplied: both are constructed. -/
theorem conditional_reverseBuser_body_maximum_IPI
    {K : Set (EuclideanSpace ℝ (Fin n))} (hbK : Bornology.IsBounded K)
    (hi : (interior K).Nonempty) (hc : Convex ℝ K)
    {b : ℝ} (hb : 0 ≤ b) (hRB : UniversalOrdinaryL1ReverseBuser b) :
    let Ω := bodyInteriorDomain K hbK hi
    let r := sSup {r : ℝ | 0 < r ∧ ∃ c, Metric.ball c r ⊆ K}
    Ω.improvedPoincareConstant ≤ ENNReal.ofReal
      (4 * (((12+4*b)*(n : ℝ)*Real.sqrt Ω.poincareConstant.toReal/r)^2)) := by
  obtain ⟨hr, a, _, hball⟩ := exists_inscribed_ball_at_sup hbK hi
  exact conditional_reverseBuser_arbitrary_center_IPI (bodyInteriorDomain K hbK hi)
    hc.interior ((bodyInteriorDomain K hbK hi).poincareConstant_lt_top_convex hc.interior) hb hr (bodyInteriorDomain_ball hbK hi hball) hRB
end HitAndRun.Geometry
