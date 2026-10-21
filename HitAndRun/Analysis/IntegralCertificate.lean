module
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Tactic.Linarith
@[expose] public section

/-! Integral dual-certificate estimate, with genuine L2 membership. -/
namespace HitAndRun.Analysis
open MeasureTheory
open scoped RealInnerProductSpace
variable {α H : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem integral_certificate_energy (r g : α → H) (hr : MemLp r 2 μ)
    (hg : MemLp g 2 μ) (F C : ℝ) (hF : 0 ≤ F) (hC : 0 ≤ C)
    (hpair : (∫ x, inner ℝ (r x) (g x) ∂μ) = F)
    (hbound : (∫ x, ‖g x‖ ^ 2 ∂μ) ≤ C * F) :
    F ≤ C * ∫ x, ‖r x‖ ^ 2 ∂μ := by
  let a := hr.toLp r
  let b := hg.toLp g
  have hab : inner ℝ a b = F := by
    rw [L2.inner_def, ← hpair]
    apply integral_congr_ae
    filter_upwards [hr.coeFn_toLp, hg.coeFn_toLp] with x hx hy
    simp only [a, b, hx, hy]
  have hnorm (v : α → H) (hv : MemLp v 2 μ) :
      ‖hv.toLp v‖ ^ 2 = ∫ x, ‖v x‖ ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hv.coeFn_toLp] with x hx
    rw [hx, real_inner_self_eq_norm_sq]
  have hcs : F ≤ ‖a‖ * ‖b‖ := by
    rw [← hab]; exact real_inner_le_norm _ _
  have hs := mul_self_le_mul_self hF hcs
  have hb : ‖b‖ ^ 2 ≤ C * F := by
    simpa only [b, hnorm] using hbound
  have hm := mul_le_mul_of_nonneg_left hb (sq_nonneg ‖a‖)
  have ha : ‖a‖ ^ 2 = ∫ x, ‖r x‖ ^ 2 ∂μ := hnorm r hr
  by_cases hz : F = 0
  · rw [hz]
    exact mul_nonneg hC (integral_nonneg fun x => sq_nonneg ‖r x‖)
  · have hp : 0 < F := lt_of_le_of_ne hF (Ne.symm hz)
    rw [← ha]
    nlinarith
end HitAndRun.Analysis
