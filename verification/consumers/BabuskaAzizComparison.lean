module
public import HitAndRun.Sobolev.BabuskaAzizComparison
@[expose] public section
open HitAndRun.Sobolev
example {n : ℕ} [NeZero n] (K : BoundedOpenDomain n) (C : ℝ) (hC : 0 ≤ C)
    (hres : ∀ f : K.Target,
      ‖divergenceResidual f (K.rieszField f)‖ ^ 2 ≤ 4 * C *
        ∑ i, ∑ j, if i < j then
          ‖weakPartial (K.rieszField f) i j - weakPartial (K.rieszField f) j i‖ ^ 2 else 0) :
    K.constant ≤ ENNReal.ofReal (1 + 4 * C) := K.constant_le_of_residual_bound C hC hres
#print axioms HitAndRun.Sobolev.BoundedOpenDomain.constant_le_of_residual_bound
