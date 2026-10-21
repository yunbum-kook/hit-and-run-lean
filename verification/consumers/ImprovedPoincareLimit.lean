module
public import HitAndRun.Sobolev.ImprovedPoincareLimit
@[expose] public section
open MeasureTheory HitAndRun.Sobolev EllipticPdes EllipticPdes.H1Graph Filter
open scoped Topology
example {n : ℕ} [NeZero n] (K : BoundedOpenDomain n)
    (hC : K.improvedPoincareConstant < ⊤) (u : ℕ → K.H1) (f : K.Target) (R : ℝ)
    (hu : Tendsto (fun k => fnL (u k : H1Graph K.ambient K.carrier)) atTop (𝓝 f.val))
    (hE : Tendsto (fun k => (K.weightedGradientEnergy (u k)).toReal) atTop (𝓝 R)) :
    ‖f‖ ^ 2 ≤ K.improvedPoincareConstant.toReal * R :=
  K.improvedPoincare_centered_limit hC u f R hu hE
#print axioms HitAndRun.Sobolev.BoundedOpenDomain.lp_variance_eq
#print axioms HitAndRun.Sobolev.BoundedOpenDomain.continuous_lp_variance
#print axioms HitAndRun.Sobolev.BoundedOpenDomain.improvedPoincare_centered_limit
