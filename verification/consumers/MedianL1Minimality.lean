import HitAndRun.Geometry.MedianWeightedBridge
open MeasureTheory HitAndRun.Geometry
open scoped ENNReal
example {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {f : α → ℝ} {m : ℝ} (hm : IsMedian μ f m) (hf : Integrable f μ) (z : ℝ) :
    (∫ x, |f x - m| ∂μ) ≤ ∫ x, |f x - z| ∂μ := hm.integral_abs_sub_le hf z
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsProbabilityMeasure μ]
    {w : E → ℝ} {A : ℝ}
    (h : ∀ f : E → ℝ, ContDiff ℝ 1 f → Integrable f μ →
      Integrable (fun x => w x * ‖fderiv ℝ f x‖) μ →
      ∃ z : ℝ, (∫ x, |f x - z| ∂μ) ≤ A * ∫ x, w x * ‖fderiv ℝ f x‖ ∂μ) :
    C1WeightedL1Bound μ w A := C1WeightedL1Bound.of_exists_center h
#print axioms HitAndRun.Geometry.integral_abs_sub_le_of_upper_tail
#print axioms HitAndRun.Geometry.IsMedian.integral_abs_sub_le
#print axioms HitAndRun.Geometry.C1WeightedL1Bound.of_exists_center
