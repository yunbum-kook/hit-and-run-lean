module
public import HitAndRun.Geometry.BoundaryDistance
public import Mathlib.Analysis.Convex.Gauge
public import Mathlib.Algebra.Order.Ring.Pow
@[expose] public section

/-! Geometric prerequisites of source Theorem 3.1, not a weighted Poincare theorem. -/
namespace HitAndRun.Geometry
open Set Metric
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The gauge slack controls the actual distance to the frontier. No attainment
of the gauge infimum in the open body is assumed. -/
theorem gauge_boundary_distance {K : Set E} (hK : Convex ℝ K) (ho : IsOpen K)
    (hfront : (frontier K).Nonempty) {r : ℝ} (hr : 0 < r)
    (hball : ball (0 : E) r ⊆ K) {x : E} (hx : x ∈ K) :
    (1 - gauge K x) * r ≤ infDist x (frontier K) := by
  have hzero : (0 : E) ∈ K := hball (by simpa using hr)
  have habs : Absorbent ℝ K := absorbent_nhds_zero (ho.mem_nhds hzero)
  have hg : gauge K x < 1 := interior_subset_gauge_lt_one K (by rwa [ho.interior_eq])
  by_contra hn
  have hbad : infDist x (frontier K) < (1 - gauge K x) * r := lt_of_not_ge hn
  have hbound : gauge K x < 1 - infDist x (frontier K) / r := by
    apply (lt_sub_iff_add_lt).mpr
    have hd := (div_lt_iff₀ hr).mpr hbad
    linarith
  obtain ⟨a, hga, ha⟩ := exists_between (lt_min hg hbound)
  obtain ⟨b, hb, hba, y, hy, hxy⟩ := exists_lt_of_gauge_lt habs hga
  have hb1 : b < 1 := hba.trans (lt_min_iff.mp ha).1
  have hd := contraction_boundary_distance hK ho hfront hball hy hb.le hb1
  change b • y = x at hxy
  rw [hxy] at hd
  have hbr : b < 1 - infDist x (frontier K) / r :=
    hba.trans (lt_min_iff.mp ha).2
  have ht : infDist x (frontier K) < (1 - b) * r := by
    apply (div_lt_iff₀ hr).mp
    linarith
  exact (not_lt_of_ge hd) ht

/-- Exact open radial sections used in the Tonelli rearrangement. -/
theorem mem_dilation_iff_gauge_lt {K : Set E} (hK : Convex ℝ K)
    (ho : IsOpen K) (hzero : (0 : E) ∈ K) {t : ℝ} (ht : 0 < t) (x : E) :
    x ∈ t • K ↔ gauge K x < t := by
  rw [mem_smul_set_iff_inv_smul_mem₀ ht.ne']
  have he := gauge_lt_one_iff_mem_interior (x := t⁻¹ • x) hK (ho.mem_nhds hzero)
  rw [ho.interior_eq, gauge_smul_of_nonneg (inv_nonneg.mpr ht.le), smul_eq_mul,
    inv_mul_lt_iff₀ ht, mul_one] at he
  exact he.symm

/-- The paper's contraction loses at most a factor two of volume. -/
theorem contraction_power_lower (n : ℕ) (hn : 0 < n) :
    (1 / 2 : ℝ) ≤ (1 - 1 / (2 * (n : ℝ))) ^ n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hi : 0 < 1 / (2 * (n : ℝ)) := by positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hi1 : 1 / (2 * (n : ℝ)) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  have h := one_add_mul_le_pow (a := -(1 / (2 * (n : ℝ)))) (by linarith) n
  have he : 1 + (n : ℝ) * -(1 / (2 * (n : ℝ))) = 1 / 2 := by field_simp [ne_of_gt hn']; ring
  rw [he] at h
  simpa only [sub_eq_add_neg] using h

theorem contraction_inverse_power_upper (n : ℕ) (hn : 0 < n) :
    ((1 - 1 / (2 * (n : ℝ))) ^ n)⁻¹ ≤ 2 := by
  have h := contraction_power_lower n hn
  rw [inv_eq_one_div]
  apply (div_le_iff₀ (by linarith : 0 < (1 - 1 / (2 * (n : ℝ))) ^ n)).mpr
  linarith
end HitAndRun.Geometry
