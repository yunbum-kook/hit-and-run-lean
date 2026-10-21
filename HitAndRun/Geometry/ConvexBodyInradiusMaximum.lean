module
public import HitAndRun.Geometry.ConvexBodyInradiusBoundary
@[expose] public section
noncomputable section
namespace HitAndRun.Geometry
open Set Metric
open scoped Topology
variable {n : ℕ} [NeZero n]

/-- The inscribed-radius center maximizes actual distance to the frontier over
the compact closure of the body. -/
theorem convex_inradius_isMaxOn
    {K : Set (EuclideanSpace ℝ (Fin n))} (hb : Bornology.IsBounded K)
    (hi : (interior K).Nonempty) (hc : Convex ℝ K) :
    ∃ c ∈ interior K, 0 < infDist c (frontier K) ∧
      IsMaxOn (fun x => infDist x (frontier K)) (closure K) c := by
  obtain ⟨c, R, hci, hR, hball, hmax⟩ := exists_maximal_inscribed_ball hb hi
  have hp : interior K ≠ univ := fun h =>
    NormedSpace.unbounded_univ ℝ _ (h ▸ hb.subset interior_subset)
  have hcomp : (interior K)ᶜ.Nonempty := nonempty_compl.mpr hp
  have hRc : R ≤ infDist c (frontier K) := by
    rw [← convex_frontier_interior hc hi, ← infDist_compl_eq_frontier_of_open isOpen_interior hp hci]
    apply (le_infDist hcomp).mpr
    intro y hy
    by_contra h
    exact hy (ball_subset_interior_iff.mpr hball
      (mem_ball.mpr (by simpa only [dist_comm] using lt_of_not_ge h)))
  refine ⟨c, hci, hR.trans_le hRc, ?_⟩
  intro x hx
  change infDist x (frontier K) ≤ infDist c (frontier K)
  by_cases hxi : x ∈ interior K
  · have he : infDist x (frontier K) = infDist x (interior K)ᶜ := by
      rw [← convex_frontier_interior hc hi, infDist_compl_eq_frontier_of_open isOpen_interior hp hxi]
    rw [he]
    have hpos : 0 < infDist x (interior K)ᶜ :=
      (isClosed_compl_iff.mpr isOpen_interior).notMem_iff_infDist_pos hcomp |>.mp (by simpa)
    exact (hmax _ hpos x (ball_infDist_compl_subset.trans interior_subset)).trans hRc
  · rw [infDist_zero_of_mem (show x ∈ frontier K from ⟨hx, hxi⟩)]
    exact infDist_nonneg
end HitAndRun.Geometry
