module
public import HitAndRun.Geometry.ConvexBodyInradiusMaximum
@[expose] public section
noncomputable section
open Set Metric HitAndRun.Geometry
open scoped Topology
variable {n : ℕ} [NeZero n]
example {K : Set (EuclideanSpace ℝ (Fin n))} (hb : Bornology.IsBounded K)
    (hi : (interior K).Nonempty) :
    let R := sSup {r : ℝ | 0 < r ∧ ∃ c, ball c r ⊆ K}
    0 < R ∧ ∃ c ∈ interior K, ball c R ⊆ K := exists_inscribed_ball_at_sup hb hi
example {K : Set (EuclideanSpace ℝ (Fin n))} (hb : Bornology.IsBounded K)
    (hi : (interior K).Nonempty) (hc : Convex ℝ K) :
    let R := sSup {r : ℝ | 0 < r ∧ ∃ c, ball c r ⊆ K}
    0 < R ∧ ∃ c ∈ interior K, ball c R ⊆ K ∧ infDist c (frontier K) = R :=
  convex_exists_inradius_center hb hi hc
example {K : Set (EuclideanSpace ℝ (Fin n))} (hb : Bornology.IsBounded K)
    (hi : (interior K).Nonempty) (hc : Convex ℝ K) (hK : IsClosed K) :
    let R := sSup {r : ℝ | 0 < r ∧ ∃ c, ball c r ⊆ K}
    0 < R ∧ ∃ c ∈ interior K, closedBall c R ⊆ K ∧ infDist c (frontier K) = R :=
  closed_convex_exists_inradius_closedBall hb hi hc hK
#print axioms exists_maximal_inscribed_ball
#print axioms exists_inscribed_ball_at_sup
#print axioms infDist_compl_eq_frontier_of_open
#print axioms convex_exists_inradius_center
#print axioms closed_convex_exists_inradius_closedBall

example {K : Set (EuclideanSpace ℝ (Fin n))} (hb : Bornology.IsBounded K)
    (hi : (interior K).Nonempty) (hc : Convex ℝ K) :
    ∃ c ∈ interior K, 0 < infDist c (frontier K) ∧
      IsMaxOn (fun x => infDist x (frontier K)) (closure K) c :=
  convex_inradius_isMaxOn hb hi hc
#print axioms convex_inradius_isMaxOn
