import HitAndRun.Markov.CoordinateAnnihilation
import HitAndRun.Markov.CoordinateAnnihilationChart
open MeasureTheory HitAndRun.Markov
example {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    (∫ t, deriv f t) = 0 := integral_compact_derivative_zero hf hc
example {n : ℕ} (i : Fin n) :
    MeasurePreserving (coordinateChart i) volume (volume.prod volume) := coordinateChart_volume i
#print axioms integral_compact_derivative_zero
#print axioms integral_fiber_derivative_cylinder_zero
#print axioms conditionalProjection_eq_zero_of_integrals
#print axioms coordinateChart_volume
#print axioms coordinateInsert
#print axioms coordinateSigma_le
