module
public import HitAndRun.Markov.ChordKernel
public import HitAndRun.Geometry.BoundaryDistance
public import HitAndRun.Analysis.BabuskaAzizAlgebra
@[expose] public section
open Set MeasureTheory ProbabilityTheory HitAndRun.Geometry HitAndRun.Markov
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {K : Set E} (ho : IsOpen K) (hb : Bornology.IsBounded K) :
    IsMarkovKernel (chordKernel K ho.measurableSet) := chordKernel_markov ho hb
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
    {K : Set E} (hK : Convex ℝ K) (ho : IsOpen K) (hb : Bornology.IsBounded K)
    {r a : ℝ} (hball : Metric.ball (0 : E) r ⊆ K) {x : E} (hx : x ∈ K)
    (ha : 0 ≤ a) (ha1 : a < 1) :
    (1-a)*r ≤ Metric.infDist (a • x) (frontier K) :=
  contraction_boundary_distance_of_bounded hK ho hb hball hx ha ha1
#print axioms HitAndRun.Geometry.lineChord_volume
#print axioms HitAndRun.Geometry.chordLaw_probability
#print axioms HitAndRun.Geometry.chordLaw_apply
#print axioms HitAndRun.Geometry.chordLaw_body_mass
#print axioms HitAndRun.Geometry.contraction_boundary_distance_of_bounded
#print axioms HitAndRun.Markov.measurable_chordLaw
#print axioms HitAndRun.Markov.chordKernel_markov
#print axioms HitAndRun.Analysis.babuskaAziz_energy_algebra
