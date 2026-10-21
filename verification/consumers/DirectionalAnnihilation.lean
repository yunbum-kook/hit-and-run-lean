module
import HitAndRun.Markov.DirectionalAnnihilationCertificate
open MeasureTheory EllipticPdes EllipticPdes.H1Graph HitAndRun.Sobolev HitAndRun.Geometry HitAndRun.Markov
example {n : ℕ} [NeZero n] (K : BoundedOpenDomain n) (θ : UnitDirection n)
    (u : H01 K.ambient K.carrier) :
    conditionalProjection (directionalSigma_le θ)
      (partialL (θ : EuclideanSpace ℝ (Fin n)) (u : H1Graph K.ambient K.carrier)) = 0 :=
  h01_directional_projection K θ u
example {n : ℕ} [NeZero n] (K : BoundedOpenDomain n) (θ : UnitDirection n)
    (u : VectorField K.ambient K.carrier) :
    conditionalProjection (directionalSigma_le θ) (sphereCertificate u θ) = 0 :=
  sphereCertificate_directional_projection K θ u
#print axioms directionQuotient_orthogonal
#print axioms integral_directional_cylinder_zero
#print axioms h01_directional_projection
#print axioms gradient_directional_projection
#print axioms sphereCertificate_directional_projection
