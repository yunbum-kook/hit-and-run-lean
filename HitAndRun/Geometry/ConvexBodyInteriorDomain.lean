module
public import HitAndRun.Geometry.ConvexBodyInterior
public import HitAndRun.Sobolev.PoincareConstants
@[expose] public section
noncomputable section
namespace HitAndRun.Geometry
open MeasureTheory Set Metric HitAndRun.Sobolev
open scoped Topology
variable {n : ℕ}

/-- A bounded full-dimensional convex body is represented by its actual interior,
not by an assumption that the original body was open. -/
def bodyInteriorDomain (K : Set (EuclideanSpace ℝ (Fin n)))
    (hb : Bornology.IsBounded K) (hi : (interior K).Nonempty) : BoundedOpenDomain n where
  carrier := interior K
  isOpen := isOpen_interior
  nonempty := hi
  isBounded := hb.subset interior_subset

theorem bodyInteriorDomain_convex {K : Set (EuclideanSpace ℝ (Fin n))}
    (hb : Bornology.IsBounded K) (hi : (interior K).Nonempty) (hc : Convex ℝ K) :
    Convex ℝ (bodyInteriorDomain K hb hi).carrier := hc.interior

theorem bodyInteriorDomain_ball {K : Set (EuclideanSpace ℝ (Fin n))}
    (hb : Bornology.IsBounded K) (hi : (interior K).Nonempty) {c : EuclideanSpace ℝ (Fin n)}
    {r : ℝ} (hball : ball c r ⊆ K) : ball c r ⊆ (bodyInteriorDomain K hb hi).carrier :=
  ball_subset_interior_iff.mpr hball

theorem bodyInteriorDomain_uniform {K : Set (EuclideanSpace ℝ (Fin n))}
    (hb : Bornology.IsBounded K) (hi : (interior K).Nonempty) (hc : Convex ℝ K) :
    uniformMeasure (bodyInteriorDomain K hb hi).carrier = uniformMeasure K :=
  (convex_uniformMeasure_interior hc).symm

theorem bodyInteriorDomain_boundaryDistance [NeZero n]
    {K : Set (EuclideanSpace ℝ (Fin n))} (hb : Bornology.IsBounded K)
    (hi : (interior K).Nonempty) (hc : Convex ℝ K) (x : EuclideanSpace ℝ (Fin n)) :
    (bodyInteriorDomain K hb hi).boundaryDistance x = infDist x (frontier K) :=
  convex_infDist_frontier_interior hc hi x

/-- The complete set of admissible open-ball radii is preserved, including all centers. -/
theorem interior_inscribed_radii (K : Set (EuclideanSpace ℝ (Fin n))) :
    {r : ℝ | 0 < r ∧ ∃ c, ball c r ⊆ interior K} =
      {r : ℝ | 0 < r ∧ ∃ c, ball c r ⊆ K} := by
  ext r
  simp only [mem_setOf_eq, ball_subset_interior_iff]

/-- Supremal inscribed radius transport requires no attainment assumption. -/
theorem interior_inscribed_radius_sup (K : Set (EuclideanSpace ℝ (Fin n))) :
    sSup {r : ℝ | 0 < r ∧ ∃ c, ball c r ⊆ interior K} =
      sSup {r : ℝ | 0 < r ∧ ∃ c, ball c r ⊆ K} := by
  rw [interior_inscribed_radii]

theorem convex_integral_interior {K : Set (EuclideanSpace ℝ (Fin n))}
    (hc : Convex ℝ K) (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∫ x in K, f x) = ∫ x in interior K, f x := by
  rw [convex_restrict_interior volume hc]

/-- The actual source weighted integral is unchanged by passing to the interior. -/
theorem convex_boundary_weighted_integral_interior
    {K : Set (EuclideanSpace ℝ (Fin n))} (hc : Convex ℝ K)
    (hi : (interior K).Nonempty) (g : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∫ x in K, infDist x (frontier K) * g x) =
      ∫ x in interior K, infDist x (frontier (interior K)) * g x := by
  rw [convex_frontier_interior hc hi, convex_restrict_interior volume hc]
end HitAndRun.Geometry
