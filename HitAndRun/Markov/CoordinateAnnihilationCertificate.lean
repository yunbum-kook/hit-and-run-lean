module
public import HitAndRun.Markov.CoordinateAverage
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic.Positivity
@[expose] public section

/-! Finite-coordinate dual certificate. Its Sobolev instantiation must supply the
coordinate cancellation from actual weak derivatives, rather than assume it. -/
namespace HitAndRun.Markov
open MeasureTheory
open scoped BigOperators RealInnerProductSpace
variable {α ι : Type*} [Fintype ι] [Nonempty ι]
variable {m0 : MeasurableSpace α} {μ : @Measure α m0}

 theorem coordinate_certificate_energy (m : ι → MeasurableSpace α)
    (hm : ∀ i, m i ≤ m0) (f : Lp ℝ 2 μ) (g : ι → Lp ℝ 2 μ) (C : ℝ)
    (hsum : ∑ i, g i = f)
    (hzero : ∀ i, conditionalProjection (hm i) (g i) = 0)
    (hbound : ∑ i, ‖g i‖ ^ 2 ≤ C * ‖f‖ ^ 2) :
    ‖f‖ ^ 2 ≤ C * ∑ i, ‖f - conditionalProjection (hm i) f‖ ^ 2 := by
  let a : PiLp 2 (fun _ : ι => Lp ℝ 2 μ) :=
    WithLp.toLp 2 (fun i => f - conditionalProjection (hm i) f)
  let b : PiLp 2 (fun _ : ι => Lp ℝ 2 μ) := WithLp.toLp 2 g
  have hab : inner ℝ a b = ‖f‖ ^ 2 := by
    rw [PiLp.inner_apply]
    change (∑ i, inner ℝ (f - conditionalProjection (hm i) f) (g i)) = _
    simp_rw [inner_sub_left, conditionalProjection_symmetric, hzero, inner_zero_right, sub_zero]
    rw [← inner_sum, hsum, real_inner_self_eq_norm_sq]
  have hcs : ‖f‖ ^ 2 ≤ ‖a‖ * ‖b‖ := by
    rw [← hab]
    exact real_inner_le_norm _ _
  have hs := mul_self_le_mul_self (sq_nonneg ‖f‖) hcs
  have hb : ‖b‖ ^ 2 ≤ C * ‖f‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    exact hbound
  have ha : ‖a‖ ^ 2 = ∑ i, ‖f - conditionalProjection (hm i) f‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
  have hmul := mul_le_mul_of_nonneg_left hb (sq_nonneg ‖a‖)
  by_cases hf : f = 0
  · simp [hf, conditionalProjection]
  · have hp : 0 < ‖f‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hf)
    rw [← ha]
    nlinarith

end HitAndRun.Markov
