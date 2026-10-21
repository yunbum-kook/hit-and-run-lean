module
public import HitAndRun.Geometry.ConvexBodyInteriorRadii
@[expose] public section
noncomputable section
open MeasureTheory Set Metric HitAndRun.Geometry HitAndRun.Sobolev
open scoped Topology
variable {n : ℕ}
example {K : Set (EuclideanSpace ℝ (Fin n))} (hc : Convex ℝ K) :
    uniformMeasure K = uniformMeasure (interior K) := convex_uniformMeasure_interior hc
example [NeZero n] {K : Set (EuclideanSpace ℝ (Fin n))}
    (hb : Bornology.IsBounded K) (hi : (interior K).Nonempty) (hc : Convex ℝ K)
    (x : EuclideanSpace ℝ (Fin n)) :
    (bodyInteriorDomain K hb hi).boundaryDistance x = infDist x (frontier K) :=
  bodyInteriorDomain_boundaryDistance hb hi hc x
example {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsClosed K) :
    {r : ℝ | 0 < r ∧ ∃ c, closedBall c r ⊆ K} =
      {r : ℝ | 0 < r ∧ ∃ c, ball c r ⊆ interior K} := closed_body_inscribed_radii hK
#print axioms convex_ae_eq_interior
#print axioms convex_uniformMeasure_interior
#print axioms convex_frontier_interior
#print axioms bodyInteriorDomain_boundaryDistance
#print axioms convex_boundary_weighted_integral_interior
#print axioms closed_body_inscribed_radii
#print axioms interior_inscribed_radius_sup
