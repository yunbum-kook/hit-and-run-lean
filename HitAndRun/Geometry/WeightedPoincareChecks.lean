module
public import HitAndRun.Geometry.WeightedPoincareGeometry
@[expose] public section
open Set Metric
open scoped Pointwise
open HitAndRun.Geometry
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
example {K : Set E} (hK : Convex ℝ K) (ho : IsOpen K)
    (hfront : (frontier K).Nonempty) {r : ℝ} (hr : 0 < r)
    (hball : ball (0 : E) r ⊆ K) {x : E} (hx : x ∈ K) :
    (1 - gauge K x) * r ≤ infDist x (frontier K) :=
  gauge_boundary_distance hK ho hfront hr hball hx
example {K : Set E} (hK : Convex ℝ K) (ho : IsOpen K) (hzero : (0 : E) ∈ K)
    {t : ℝ} (ht : 0 < t) (x : E) : x ∈ t • K ↔ gauge K x < t :=
  mem_dilation_iff_gauge_lt hK ho hzero ht x
example (n : ℕ) (hn : 0 < n) : (1 / 2 : ℝ) ≤ (1 - 1 / (2 * (n : ℝ))) ^ n :=
  contraction_power_lower n hn
example (n : ℕ) (hn : 0 < n) : ((1 - 1 / (2 * (n : ℝ))) ^ n)⁻¹ ≤ 2 :=
  contraction_inverse_power_upper n hn
#print axioms HitAndRun.Geometry.gauge_boundary_distance
#print axioms HitAndRun.Geometry.mem_dilation_iff_gauge_lt
#print axioms HitAndRun.Geometry.contraction_power_lower
#print axioms HitAndRun.Geometry.contraction_inverse_power_upper
