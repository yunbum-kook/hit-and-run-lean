module
public import HitAndRun.Geometry.ConvexBodyInteriorDomain
@[expose] public section
noncomputable section
namespace HitAndRun.Geometry
open Set Metric
open scoped Topology
variable {n : ℕ}

/-- For a closed body and positive radius, an inscribed open ball is equivalent
to the corresponding closed ball. No maximum-radius attainment is assumed. -/
theorem closedBall_subset_closed_body_iff {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsClosed K) {c : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r) :
    closedBall c r ⊆ K ↔ ball c r ⊆ K := by
  constructor
  · exact fun h => ball_subset_closedBall.trans h
  · intro h
    rw [← closure_ball c hr.ne']
    exact closure_minimal h hK

theorem closed_body_inscribed_radii {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsClosed K) :
    {r : ℝ | 0 < r ∧ ∃ c, closedBall c r ⊆ K} =
      {r : ℝ | 0 < r ∧ ∃ c, ball c r ⊆ interior K} := by
  ext r
  constructor
  · rintro ⟨hr, c, hc⟩
    exact ⟨hr, c, ball_subset_interior_iff.mpr
      ((closedBall_subset_closed_body_iff hK hr).mp hc)⟩
  · rintro ⟨hr, c, hc⟩
    exact ⟨hr, c, (closedBall_subset_closed_body_iff hK hr).mpr
      (ball_subset_interior_iff.mp hc)⟩
end HitAndRun.Geometry
