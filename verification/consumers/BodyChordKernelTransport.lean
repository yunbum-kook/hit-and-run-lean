import HitAndRun.Markov.BodyChordKernelTransport
open Set MeasureTheory ProbabilityTheory HitAndRun.Geometry HitAndRun.Markov
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
example {K : Set E} (ho : IsOpen K) (hb : Bornology.IsBounded K)
    (θ : E) (hθ : ‖θ‖ = 1) (x : K) :
    (directionKernel K ho.measurableSet θ hθ x).map Subtype.val = chordLaw K x.val θ :=
  directionKernel_map_subtype ho hb θ hθ x
example {K : Set E} (ho : IsOpen K) (hb : Bornology.IsBounded K)
    (θ : E) (hθ : ‖θ‖ = 1) (x : K) (f : E → ℝ) :
    (∫ y : K, f y.val ∂directionKernel K ho.measurableSet θ hθ x) =
      ∫ y, f y ∂chordLaw K x.val θ := directionKernel_integral_subtype ho hb θ hθ x f
#print axioms directionKernel_map_subtype
#print axioms directionKernel_measurePreserving
#print axioms directionKernel_integral_subtype
