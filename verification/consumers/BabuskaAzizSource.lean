module
public import HitAndRun.Sobolev.BabuskaAzizSource
@[expose] public section
open HitAndRun.Sobolev
example {n : ℕ} [NeZero n] (K : BoundedOpenDomain n) :
    K.constant ≤ 1 + 4 * K.improvedPoincareConstant :=
  K.babuskaAziz_le_one_add_four_improvedPoincare
example {n : ℕ} [NeZero n] (K : BoundedOpenDomain n)
    (hC : K.improvedPoincareConstant < ⊤) :
    K.constant ≤ ENNReal.ofReal (1 + 4 * K.improvedPoincareConstant.toReal) :=
  K.constant_le_of_finite_improvedPoincare hC
#print axioms HitAndRun.Sobolev.BoundedOpenDomain.babuskaAziz_le_one_add_four_improvedPoincare
#print axioms HitAndRun.Sobolev.BoundedOpenDomain.constant_le_of_finite_improvedPoincare
