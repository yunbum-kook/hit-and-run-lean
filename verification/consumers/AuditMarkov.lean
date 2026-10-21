import HitAndRun.Markov.CoordinateAverage
import HitAndRun.Analysis.PositiveContraction
#print axioms HitAndRun.Markov.coordinateAverage_positive
#print axioms HitAndRun.Markov.coordinateAverage_symmetric
#print axioms HitAndRun.Markov.coordinateAverage_energy
#print axioms HitAndRun.Analysis.norm_le_one_sub_gap
#print axioms HitAndRun.Analysis.iterate_sq_le_exp
#print axioms HitAndRun.Analysis.iterate_sq_le_exp_on_submodule
open MeasureTheory
example {α ι : Type*} [Fintype ι] [Nonempty ι] {m0 : MeasurableSpace α}
    {μ : @Measure α m0} (m : ι → MeasurableSpace α) (hm : ∀ i, m i ≤ m0)
    (f : Lp ℝ 2 μ) :
    inner ℝ f (f - HitAndRun.Markov.coordinateAverage m hm f) =
    (Fintype.card ι : ℝ)⁻¹ * ∑ i, ‖f - HitAndRun.Markov.conditionalProjection (hm i) f‖ ^ 2 :=
  HitAndRun.Markov.coordinateAverage_energy m hm f
