module
public import HitAndRun.Geometry.ConvexBodyInteriorRadii
public import Mathlib.Topology.Order.Compact
@[expose] public section
noncomputable section
namespace HitAndRun.Geometry
open Set Metric
open scoped Topology
variable {n : ℕ} [NeZero n]

/-- An actual maximum inscribed open ball exists, even without convexity.
All centers are allowed, and the original set need not be open or closed. -/
theorem exists_maximal_inscribed_ball
    {K : Set (EuclideanSpace ℝ (Fin n))} (hb : Bornology.IsBounded K)
    (hi : (interior K).Nonempty) :
    ∃ c : EuclideanSpace ℝ (Fin n), ∃ R : ℝ,
      c ∈ interior K ∧ 0 < R ∧ ball c R ⊆ K ∧
      (∀ r : ℝ, 0 < r → ∀ a, ball a r ⊆ K → r ≤ R) := by
  have hproper : interior K ≠ univ := fun h =>
    NormedSpace.unbounded_univ ℝ _ (h ▸ hb.subset interior_subset)
  have hcomp : (interior K)ᶜ.Nonempty := nonempty_compl.mpr hproper
  obtain ⟨x, hx⟩ := hi
  have hxpos : 0 < infDist x (interior K)ᶜ :=
    (isClosed_compl_iff.mpr isOpen_interior).notMem_iff_infDist_pos hcomp |>.mp (by simpa)
  obtain ⟨c, hc, hmax⟩ := hb.isCompact_closure.exists_isMaxOn
    ⟨x, subset_closure (interior_subset hx)⟩
    (continuous_infDist_pt (s := (interior K)ᶜ)).continuousOn
  have hpos : 0 < infDist c (interior K)ᶜ :=
    hxpos.trans_le (hmax (subset_closure (interior_subset hx)))
  have hci : c ∈ interior K := by
    by_contra h
    have hz := infDist_zero_of_mem (show c ∈ (interior K)ᶜ from h)
    linarith
  refine ⟨c, infDist c (interior K)ᶜ, hci, hpos,
    ball_infDist_compl_subset.trans interior_subset, ?_⟩
  intro r hr a ha
  have hai : ball a r ⊆ interior K := ball_subset_interior_iff.mpr ha
  have hac : a ∈ closure K := subset_closure (ha (mem_ball_self hr))
  apply le_trans _ (hmax hac)
  apply (le_infDist hcomp).mpr
  intro y hy
  by_contra h
  have : y ∈ ball a r := mem_ball.mpr (by simpa only [dist_comm] using lt_of_not_ge h)
  exact hy (hai this)

/-- The maximum is exactly the supremum of all positive admissible radii. -/
theorem exists_inscribed_ball_at_sup
    {K : Set (EuclideanSpace ℝ (Fin n))} (hb : Bornology.IsBounded K)
    (hi : (interior K).Nonempty) :
    let R := sSup {r : ℝ | 0 < r ∧ ∃ c, ball c r ⊆ K}
    0 < R ∧ ∃ c ∈ interior K, ball c R ⊆ K := by
  obtain ⟨c, R, hc, hR, hball, hmax⟩ := exists_maximal_inscribed_ball hb hi
  have hmem : R ∈ {r : ℝ | 0 < r ∧ ∃ c, ball c r ⊆ K} := ⟨hR, c, hball⟩
  have hgreat : IsGreatest {r : ℝ | 0 < r ∧ ∃ c, ball c r ⊆ K} R := by
    refine ⟨hmem, ?_⟩
    rintro r ⟨hr, a, ha⟩
    exact hmax r hr a ha
  have he := hgreat.isLUB.csSup_eq ⟨R, hmem⟩
  dsimp only
  rw [he]
  exact ⟨hR, c, hc, hball⟩

/-- Interior distance to the complement equals actual boundary distance. -/
theorem infDist_compl_eq_frontier_of_open
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (ho : IsOpen Ω) (hp : Ω ≠ univ)
    {c : EuclideanSpace ℝ (Fin n)} (hc : c ∈ Ω) :
    infDist c Ωᶜ = infDist c (frontier Ω) := by
  obtain ⟨y, hy, he⟩ := exists_mem_frontier_infDist_compl_eq_dist hc hp
  apply le_antisymm
  · apply infDist_le_infDist_of_subset _ ⟨y, hy⟩
    intro z hz
    exact fun h => (disjoint_frontier_iff_isOpen.mpr ho).le_bot ⟨hz, h⟩
  · exact (infDist_le_dist_of_mem hy).trans_eq he.symm
end HitAndRun.Geometry
