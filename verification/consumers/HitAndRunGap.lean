module
public import HitAndRun.Markov.HitAndRunGap
@[expose] public section
open HitAndRun.Sobolev HitAndRun.Markov
example {n : ℕ} [NeZero n] (K : BoundedOpenDomain n) (hC : K.constant < ⊤) :
    ((n : ℝ) + 2) / ((n : ℝ) * (2 + K.constant.toReal)) ≤
      spectralGap K (hitAndRunOperator K) := hitAndRun_source_gap K hC
#print axioms HitAndRun.Markov.hitAndRun_source_gap
#print axioms HitAndRun.Markov.hitAndRunOperator_energy
#print axioms HitAndRun.Markov.hitAndRunOperator_body
#print axioms HitAndRun.Markov.directionalResidual_memLp
