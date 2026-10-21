module
public import HitAndRun.Analysis.CompactQuotientLimit

/-! Convergence of the exact vector-test coefficient energy, not a coordinatewise
upper bound that would lose the sharp constant. -/
@[expose] public section
noncomputable section
namespace HitAndRun.Analysis
open MeasureTheory Filter Topology
variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
  {μ : Measure E} [IsFiniteMeasureOnCompacts μ]

theorem integral_sq_inv_smul_tendsto {f : E → F} {g : E → ℝ} {q : ℕ → E → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hq : ∀ k, Continuous (q k))
    {c : ℝ} (hc : 0 < c)
    (hgb : ∀ x ∈ Function.support f, c ≤ g x)
    (hqb : ∀ k x, x ∈ Function.support f → c ≤ q k x)
    (ht : ∀ x, Tendsto (fun k => q k x) atTop (𝓝 (g x))) :
    Tendsto (fun k => ∫ x, ‖(q k x)⁻¹ • f x‖ ^ 2 ∂μ) atTop
      (𝓝 (∫ x, ‖(g x)⁻¹ • f x‖ ^ 2 ∂μ)) := by
  have hi : Integrable (fun x => c⁻¹ ^ 2 * ‖f x‖ ^ 2) μ := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact continuous_const.mul (hf.norm.pow 2)
    · apply hfc.of_isClosed_subset (isClosed_tsupport _)
      apply closure_mono
      intro x hx
      by_contra hn
      exact hx (by simp [Function.notMem_support.mp hn])
  apply tendsto_integral_of_dominated_convergence (fun x => c⁻¹ ^ 2 * ‖f x‖ ^ 2)
  · intro k
    exact (((hq k).measurable.inv.smul hf.measurable).norm.pow_const 2).aestronglyMeasurable
  · exact hi
  · intro k
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    by_cases hx : f x = 0
    · simp [hx]
    have hp : 0 < q k x := hc.trans_le (hqb k x hx)
    have hb : ‖(q k x)⁻¹ • f x‖ ≤ c⁻¹ * ‖f x‖ := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hp.le)]
      exact mul_le_mul_of_nonneg_right (inv_anti₀ hc (hqb k x hx)) (norm_nonneg _)
    have hn : 0 ≤ c⁻¹ * ‖f x‖ := by positivity
    nlinarith [norm_nonneg ((q k x)⁻¹ • f x)]
  · filter_upwards [] with x
    by_cases hx : f x = 0
    · simpa [hx] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    have hp : 0 < g x := hc.trans_le (hgb x hx)
    exact (((ht x).inv₀ hp.ne').smul tendsto_const_nhds).norm.pow 2
end HitAndRun.Analysis
