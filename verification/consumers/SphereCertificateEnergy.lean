module
public import HitAndRun.Markov.SphereCertificateEnergy
@[expose] public section
open MeasureTheory HitAndRun.Geometry HitAndRun.Sobolev HitAndRun.Markov
example {n : ℕ} [NeZero n] (K : BoundedOpenDomain n) (hC : K.constant < ⊤)
    (f : K.Target) (hr : MemLp (directionalResidual K f) 2 (uniformSphere n)) :
    ‖f‖ ^ 2 ≤ ((n : ℝ) / (n + 2) * (2 + K.constant.toReal)) *
      ∫ θ, ‖directionalResidual K f θ‖ ^ 2 ∂uniformSphere n :=
  directional_energy_comparison K hC f hr
#print axioms HitAndRun.Markov.sphereCertificate_memLp
#print axioms HitAndRun.Markov.directional_energy_comparison
