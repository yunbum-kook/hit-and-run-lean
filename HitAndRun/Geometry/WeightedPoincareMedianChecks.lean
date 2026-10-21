module
public import HitAndRun.Geometry.WeightedPoincareMedian
@[expose] public section
open MeasureTheory ProbabilityTheory HitAndRun.Geometry
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsProbabilityMeasure μ]
    {f w : E → ℝ} {m A : ℝ} (hweighted : WeightedL1Bound μ w A)
    (hf : Differentiable ℝ f) (hmed : IsMedian μ f m) (hfL2 : MemLp f 2 μ)
    (hgrad : MemLp (fun x => w x * ‖fderiv ℝ f x‖) 2 μ) :
    variance f μ ≤ 4 * A ^ 2 * ∫ x, w x ^ 2 * ‖fderiv ℝ f x‖ ^ 2 ∂μ :=
  variance_bound_of_weightedL1 hweighted hf hmed hfL2 hgrad
example (t : ℝ) : HasDerivAt signedSquare (2 * |t|) t := hasDerivAt_signedSquare t
example {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ} {m : ℝ}
    (hm : IsMedian μ f m) : IsMedian μ (fun x => signedSquare (f x - m)) 0 :=
  hm.signedSquare_sub
#print axioms HitAndRun.Geometry.variance_bound_of_weightedL1
#print axioms HitAndRun.Geometry.variance_bound_of_signedSquare_L1
#print axioms HitAndRun.Geometry.hasDerivAt_signedSquare
#print axioms HitAndRun.Geometry.norm_fderiv_signedSquare_sub
#print axioms HitAndRun.Geometry.IsMedian.signedSquare_sub
#print axioms HitAndRun.Geometry.weighted_square_absorption
