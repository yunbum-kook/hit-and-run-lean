import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic

/-! The elementary convex-body contraction geometry used in Theorem 3.1.
This does not establish its weighted Poincare inequality. -/
namespace HitAndRun.Geometry
open Set Metric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem ball_subset_at_contraction {K : Set E} (hK : Convex ℝ K)
    {r a : ℝ} (hball : ball (0 : E) r ⊆ K)
    {x : E} (hx : x ∈ K) (ha : 0 ≤ a) (ha1 : a < 1) :
    ball (a • x) ((1 - a) * r) ⊆ K := by
  intro z hz
  have hb : 0 < 1 - a := sub_pos.mpr ha1
  let y : E := (1 - a)⁻¹ • (z - a • x)
  have hy : y ∈ ball (0 : E) r := by
    rw [mem_ball, dist_zero_right]
    dsimp [y]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hb)]
    rw [inv_mul_lt_iff₀ hb]
    simpa only [mem_ball, dist_eq_norm] using hz
  have h := hK hx (hball hy) ha hb.le (by ring : a + (1 - a) = 1)
  have he : a • x + (1 - a) • y = z := by
    dsimp [y]
    rw [smul_smul, mul_inv_cancel₀ hb.ne', one_smul]
    abel
  rwa [he] at h
end HitAndRun.Geometry
