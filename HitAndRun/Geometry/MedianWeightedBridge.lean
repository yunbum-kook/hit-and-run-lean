module
public import HitAndRun.Geometry.MedianL1Minimality
public import HitAndRun.Sobolev.WeightedPoincareTransferC1
@[expose] public section
namespace HitAndRun.Geometry
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsProbabilityMeasure μ]

/-- The existence-of-center weighted estimate supplies the exact median-zero
interface, without any factor loss or atomlessness assumption. -/
theorem C1WeightedL1Bound.of_exists_center {w : E → ℝ} {A : ℝ}
    (h : ∀ f : E → ℝ, ContDiff ℝ 1 f → Integrable f μ →
      Integrable (fun x => w x * ‖fderiv ℝ f x‖) μ →
      ∃ z : ℝ, (∫ x, |f x - z| ∂μ) ≤ A * ∫ x, w x * ‖fderiv ℝ f x‖ ∂μ) :
    C1WeightedL1Bound μ w A := by
  intro f hf hm hi hg
  obtain ⟨z, hz⟩ := h f hf hi hg
  have hmin : (∫ x, |f x| ∂μ) ≤ ∫ x, |f x - z| ∂μ := by
    simpa only [sub_zero] using hm.integral_abs_sub_le hi z
  exact hmin.trans hz
end HitAndRun.Geometry
