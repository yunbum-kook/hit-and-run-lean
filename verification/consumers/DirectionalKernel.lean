module
import HitAndRun.Markov.DirectionalKernelIdentificationL2
open MeasureTheory EllipticPdes HitAndRun.Sobolev HitAndRun.Geometry HitAndRun.Markov
example {n : ℕ} [NeZero n] (K : BoundedOpenDomain n) (θ : UnitDirection n)
    (f : Lp ℝ 2 (K.ambient.restrict K.carrier)) :
    conditionalProjection (directionalSigma_le θ) f =ᵐ[K.ambient.restrict K.carrier]
      fun x => ∫ y, f y ∂chordLaw K.carrier x θ := directionalProjection_chord_ae K θ f
example {n : ℕ} [NeZero n] (K : BoundedOpenDomain n) (θ : UnitDirection n)
    (u : VectorField K.ambient K.carrier) :
    (fun x => ∫ y, (sphereCertificate u θ) y ∂chordLaw K.carrier x θ)
      =ᵐ[K.ambient.restrict K.carrier] 0 := sphereCertificate_chord_ae K θ u
#print axioms directionalChart_sigma
#print axioms chordLaw_directionRotation
#print axioms condExp_eq_directionalChord
#print axioms integrable_directionalChord_ae
#print axioms directionalProjection_chord_ae
#print axioms directionalProjection_bodyKernel_ae
#print axioms directionalChord_integral_preserved
#print axioms sphereCertificate_chord_ae
