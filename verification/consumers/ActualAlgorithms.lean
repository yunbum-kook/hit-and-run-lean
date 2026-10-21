module
public import HitAndRun.Markov.CoordinateKernel
public import HitAndRun.Markov.HitAndRunKernel
@[expose] public section
open MeasureTheory ProbabilityTheory HitAndRun.Geometry HitAndRun.Markov
example (n : ℕ) [NeZero n] : IsProbabilityMeasure (uniformSphere n) := uniformSphere_probability n
example {n : ℕ} [NeZero n] {K : Set (EuclideanSpace ℝ (Fin n))}
    (ho : IsOpen K) (hb : Bornology.IsBounded K) :
    IsMarkovKernel (coordinateHitAndRun K ho.measurableSet) := coordinateHitAndRun_markov ho hb
example {n : ℕ} [NeZero n] {K : Set (EuclideanSpace ℝ (Fin n))}
    (ho : IsOpen K) (hb : Bornology.IsBounded K) :
    IsMarkovKernel (hitAndRun K ho hb) := hitAndRun_markov ho hb
#print axioms HitAndRun.Geometry.uniformSphere_probability
#print axioms HitAndRun.Markov.bodyChordKernel_markov
#print axioms HitAndRun.Markov.directionKernel_markov
#print axioms HitAndRun.Markov.finiteAverageKernel_markov
#print axioms HitAndRun.Markov.coordinateHitAndRun_markov
#print axioms HitAndRun.Markov.randomDirectionKernel_markov
#print axioms HitAndRun.Markov.hitAndRun_markov
