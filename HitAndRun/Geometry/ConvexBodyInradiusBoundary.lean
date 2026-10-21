module
public import HitAndRun.Geometry.ConvexBodyInradius
@[expose] public section
noncomputable section
namespace HitAndRun.Geometry
open Set Metric
open scoped Topology
variable {n : ℕ} [NeZero n]

/-- For a convex body, its supremal inscribed radius is attained and equals
actual distance to its frontier at an interior maximizing center. -/
theorem convex_exists_inradius_center
    {K : Set (EuclideanSpace ℝ (Fin n))} (hb : Bornology.IsBounded K)
    (hi : (interior K).Nonempty) (hc : Convex ℝ K) :
    let R := sSup {r : ℝ | 0 < r ∧ ∃ c, ball c r ⊆ K}
    0 < R ∧ ∃ c ∈ interior K, ball c R ⊆ K ∧ infDist c (frontier K) = R := by
  let R := sSup {r : ℝ | 0 < r ∧ ∃ c, ball c r ⊆ K}
  obtain ⟨hR, c, hci, hball⟩ := exists_inscribed_ball_at_sup hb hi
  have hp : interior K ≠ univ := fun h =>
    NormedSpace.unbounded_univ ℝ _ (h ▸ hb.subset interior_subset)
  have hcomp : (interior K)ᶜ.Nonempty := nonempty_compl.mpr hp
  have hd : 0 < infDist c (interior K)ᶜ :=
    (isClosed_compl_iff.mpr isOpen_interior).notMem_iff_infDist_pos hcomp |>.mp (by simpa)
  have hrle : R ≤ infDist c (interior K)ᶜ := by
    apply (le_infDist hcomp).mpr
    intro y hy
    by_contra h
    exact hy (ball_subset_interior_iff.mpr hball
      (mem_ball.mpr (by simpa only [dist_comm] using lt_of_not_ge h)))
  have hbound : BddAbove {r : ℝ | 0 < r ∧ ∃ c, ball c r ⊆ K} := by
    obtain ⟨a, s, _, _, _, hs⟩ := exists_maximal_inscribed_ball hb hi
    refine ⟨s, ?_⟩
    rintro r ⟨hr, a, ha⟩
    exact hs r hr a ha
  have hdle : infDist c (interior K)ᶜ ≤ R := le_csSup hbound
    (show infDist c (interior K)ᶜ ∈ {r : ℝ | 0 < r ∧ ∃ c, ball c r ⊆ K} from
      ⟨hd, c, ball_infDist_compl_subset.trans interior_subset⟩)
  refine ⟨hR, c, hci, hball, ?_⟩
  rw [← convex_frontier_interior hc hi, ← infDist_compl_eq_frontier_of_open isOpen_interior hp hci]
  exact le_antisymm hdle hrle

/-- Closed-body convention: the same positive supremal radius admits a closed ball. -/
theorem closed_convex_exists_inradius_closedBall
    {K : Set (EuclideanSpace ℝ (Fin n))} (hb : Bornology.IsBounded K)
    (hi : (interior K).Nonempty) (hc : Convex ℝ K) (hK : IsClosed K) :
    let R := sSup {r : ℝ | 0 < r ∧ ∃ c, ball c r ⊆ K}
    0 < R ∧ ∃ c ∈ interior K, closedBall c R ⊆ K ∧ infDist c (frontier K) = R := by
  obtain ⟨hR, c, hci, hball, hd⟩ := convex_exists_inradius_center hb hi hc
  exact ⟨hR, c, hci, (closedBall_subset_closed_body_iff hK hR).mpr hball, hd⟩
end HitAndRun.Geometry
