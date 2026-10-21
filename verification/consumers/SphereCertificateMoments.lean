module
public import HitAndRun.Markov.SphereCertificateMoments
@[expose] public section
open MeasureTheory HitAndRun.Geometry HitAndRun.Sobolev HitAndRun.Markov
example {n : ℕ} [NeZero n]
    {μ : Measure (EuclideanSpace ℝ (Fin n))} [μ.IsAddHaarMeasure]
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (u : VectorField μ Ω) :
    (∫ θ, sphereCertificate u θ ∂uniformSphere n) = divergence μ Ω u :=
  sphereCertificate_mean u
example {n : ℕ} [NeZero n]
    {μ : Measure (EuclideanSpace ℝ (Fin n))} [μ.IsAddHaarMeasure]
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (u : VectorField μ Ω) :
    (∫ θ, ‖sphereCertificate u θ‖ ^ 2 ∂uniformSphere n) =
      (n : ℝ) / (n + 2) * (2 * ‖divergence μ Ω u‖ ^ 2 + ‖u‖ ^ 2) :=
  sphereCertificate_energy u
#print axioms HitAndRun.Markov.sphereCertificate_mean
#print axioms HitAndRun.Markov.sphereCertificate_energy
