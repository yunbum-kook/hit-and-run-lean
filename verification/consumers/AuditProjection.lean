import HitAndRun.Markov.ConditionalProjection
open MeasureTheory
example {α : Type*} {m m0 : MeasurableSpace α} {μ : @Measure α m0}
  (hm : m ≤ m0) (f : Lp ℝ 2 μ) :
  inner ℝ f (f - HitAndRun.Markov.conditionalProjection hm f) =
  ‖f - HitAndRun.Markov.conditionalProjection hm f‖ ^ 2 :=
  HitAndRun.Markov.conditionalProjection_residual_energy hm f
#print axioms HitAndRun.Markov.conditionalProjection_idempotent
#print axioms HitAndRun.Markov.conditionalProjection_symmetric
#print axioms HitAndRun.Markov.conditionalProjection_positive
#print axioms HitAndRun.Markov.conditionalProjection_residual_energy
