import HitAndRun.Markov.CoordinateAnnihilationSobolev
import HitAndRun.Markov.CoordinateAnnihilationGap
open MeasureTheory HitAndRun.Markov HitAndRun.Sobolev EllipticPdes EllipticPdes.H1Graph
example {n : ℕ} [NeZero n] (K : BoundedOpenDomain n) (i : Fin n)
    (u : H01 K.ambient K.carrier) :
    conditionalProjection (coordinateSigma_le i)
      (partialL (EuclideanSpace.basisFun (Fin n) ℝ i) (u : H1Graph K.ambient K.carrier)) = 0 :=
  h01_partial_coordinate_projection K i u
example {n : ℕ} [NeZero n] (K : BoundedOpenDomain n) (hC : K.constant < ⊤) :
    1 / ((n : ℝ) * K.constant.toReal) ≤ spectralGap K (coordinateHeatBath K) :=
  coordinateHeatBath_spectralGap K hC
#print axioms derivative_coordinate_fiber
#print axioms compactSupport_coordinate_fiber
#print axioms integral_coordinate_fiber_zero
#print axioms integral_coordinate_cylinder_zero
#print axioms test_partial_coordinate_integrals
#print axioms test_partial_coordinate_projection
#print axioms h01_partial_coordinate_projection
#print axioms gradient_partial_coordinate_projection
#print axioms coordinateProjection_mean
#print axioms coordinate_certificate_energy
#print axioms target_nontrivial
#print axioms rayleighValues_nonempty
#print axioms rayleighValues_bddBelow
#print axioms le_spectralGap
#print axioms coordinateHeatBath_energy_bound
#print axioms coordinateHeatBath_rayleigh_bound
#print axioms coordinateHeatBath_spectralGap
