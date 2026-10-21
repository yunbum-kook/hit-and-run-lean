module
public import HitAndRun.Geometry.InnerBall
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Analysis.Normed.Module.Connected
@[expose] public section

namespace HitAndRun.Geometry
open Set Metric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual boundary distance on the contracted body, not an arbitrary weight. -/
theorem contraction_boundary_distance {K : Set E} (hK : Convex ℝ K) (ho : IsOpen K)
    (hfront : (frontier K).Nonempty) {r a : ℝ} (hball : ball (0 : E) r ⊆ K)
    {x : E} (hx : x ∈ K) (ha : 0 ≤ a) (ha1 : a < 1) :
    (1 - a) * r ≤ infDist (a • x) (frontier K) := by
  apply (le_infDist hfront).mpr
  intro y hy
  by_contra h
  have hin : y ∈ K := ball_subset_at_contraction hK hball hx ha ha1
    (by simpa [mem_ball, dist_comm] using (lt_of_not_ge h))
  exact (Set.disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr ho)) hy hin

/-- For the bounded nonempty bodies of the paper, the boundary is nonempty. -/
theorem contraction_boundary_distance_of_bounded [Nontrivial E] {K : Set E}
    (hK : Convex ℝ K) (ho : IsOpen K) (hb : Bornology.IsBounded K)
    {r a : ℝ} (hball : ball (0 : E) r ⊆ K) {x : E} (hx : x ∈ K)
    (ha : 0 ≤ a) (ha1 : a < 1) :
    (1 - a) * r ≤ infDist (a • x) (frontier K) := by
  have hne : (frontier K).Nonempty := nonempty_frontier_iff.mpr
    ⟨⟨x, hx⟩, fun h => NormedSpace.unbounded_univ ℝ E (h ▸ hb)⟩
  exact contraction_boundary_distance hK ho hne hball hx ha ha1
end HitAndRun.Geometry
