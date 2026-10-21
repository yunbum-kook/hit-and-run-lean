module
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Tactic

/-! L2 convergence of reciprocally weighted compact tests. The denominator
needs a lower bound only on the actual support, not on the whole space. -/
@[expose] public section
noncomputable section
namespace HitAndRun.Analysis
open MeasureTheory Filter Topology
variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsFiniteMeasureOnCompacts μ]

theorem integral_sq_quotient_sub_tendsto
    {f g : E → ℝ} {q : ℕ → E → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hq : ∀ k, Continuous (q k))
    {c : ℝ} (hc : 0 < c)
    (hgb : ∀ x ∈ Function.support f, c ≤ g x)
    (hqb : ∀ k x, x ∈ Function.support f → c ≤ q k x)
    (ht : ∀ x, Tendsto (fun k => q k x) atTop (𝓝 (g x))) :
    Tendsto (fun k => ∫ x, ‖f x / q k x - f x / g x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  have hi : Integrable (fun x => (2 / c) ^ 2 * (f x) ^ 2) μ := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact continuous_const.mul (hf.pow 2)
    · apply hfc.of_isClosed_subset (isClosed_tsupport _)
      apply closure_mono
      intro x hx
      by_contra hn
      exact hx (by simp [Function.notMem_support.mp hn])
  have hd := tendsto_integral_of_dominated_convergence
    (μ := μ) (F := fun k x => ‖f x / q k x - f x / g x‖ ^ 2)
    (f := fun _ => (0 : ℝ)) (fun x => (2 / c) ^ 2 * (f x) ^ 2)
    (fun k => (((hf.measurable.div (hq k).measurable).sub
      (hf.measurable.div hg.measurable )).norm.pow_const 2).aestronglyMeasurable)
    hi ?_ ?_
  · simpa using hd
  · intro k
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    by_cases hx : f x = 0
    · simp [hx]
    have hs : x ∈ Function.support f := hx
    have hgpos : 0 < g x := hc.trans_le (hgb x hs)
    have hqpos : 0 < q k x := hc.trans_le (hqb k x hs)
    have hg' : ‖f x / g x‖ ≤ ‖f x‖ / c := by
      rw [norm_div, Real.norm_of_nonneg hgpos.le]
      exact div_le_div_of_nonneg_left (norm_nonneg _) hc (hgb x hs)
    have hq' : ‖f x / q k x‖ ≤ ‖f x‖ / c := by
      rw [norm_div, Real.norm_of_nonneg hqpos.le]
      exact div_le_div_of_nonneg_left (norm_nonneg _) hc (hqb k x hs)
    have hb : ‖f x / q k x - f x / g x‖ ≤ (2 / c) * ‖f x‖ := by
      calc
        ‖f x / q k x - f x / g x‖ ≤ ‖f x / q k x‖ + ‖f x / g x‖ := norm_sub_le _ _
        _ ≤ ‖f x‖ / c + ‖f x‖ / c := add_le_add hq' hg'
        _ = (2 / c) * ‖f x‖ := by ring
    have hnon : 0 ≤ (2 / c) * ‖f x‖ := by positivity
    have hn : ‖f x‖ ^ 2 = (f x) ^ 2 := by simp
    nlinarith [norm_nonneg (f x / q k x - f x / g x)]
  · filter_upwards [] with x
    by_cases hx : f x = 0
    · simpa [hx] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    have hp : 0 < g x := hc.trans_le (hgb x hx)
    have hconst : Tendsto (fun _ : ℕ => f x) atTop (𝓝 (f x)) := tendsto_const_nhds
    have hh := (hconst.div (ht x) hp.ne').sub_const (f x / g x)
    simpa using hh.norm.pow 2
end HitAndRun.Analysis
