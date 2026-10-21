module
import HitAndRun.Markov.ImprovedPoincareGap
open HitAndRun.Sobolev HitAndRun.Markov
example {n : ℕ} [NeZero n] (K : BoundedOpenDomain n)
    (hI : K.improvedPoincareConstant < ⊤) :
    ((n : ℝ) + 2) / ((n : ℝ) * (3 + 4 * K.improvedPoincareConstant.toReal)) ≤
      spectralGap K (hitAndRunOperator K) := hitAndRun_gap_of_improvedPoincare K hI
example {n : ℕ} [NeZero n] (K : BoundedOpenDomain n)
    (hI : K.improvedPoincareConstant < ⊤) :
    1 / ((n : ℝ) * (1 + 4 * K.improvedPoincareConstant.toReal)) ≤
      spectralGap K (coordinateHeatBath K) := coordinateHitAndRun_gap_of_improvedPoincare K hI
#print axioms finite_constant_of_finite_improvedPoincare
#print axioms constant_toReal_le_improvedPoincare
#print axioms hitAndRun_gap_of_improvedPoincare
#print axioms coordinateHitAndRun_gap_of_improvedPoincare
