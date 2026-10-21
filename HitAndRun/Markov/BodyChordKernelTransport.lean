module
public import HitAndRun.Markov.BodyChordKernel
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
@[expose] public section

/-! Exact transport of the actual body-valued chord transition to ambient chord law. -/
namespace HitAndRun.Markov
open Set MeasureTheory ProbabilityTheory HitAndRun.Geometry
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- Inclusion of the body outcomes recovers the original ambient chord law. -/
theorem directionKernel_map_subtype {K : Set E} (ho : IsOpen K)
    (hb : Bornology.IsBounded K) (θ : E) (hθ : ‖θ‖ = 1) (x : K) :
    (directionKernel K ho.measurableSet θ hθ x).map Subtype.val =
      chordLaw K x.val θ := by
  change ((chordLaw K x.val θ).comap Subtype.val).map Subtype.val = _
  rw [map_comap_subtype_coe ho.measurableSet]
  apply Measure.restrict_eq_self_of_ae_mem
  letI := chordLaw_probability ho hb x.property hθ
  exact (mem_ae_iff_prob_eq_one ho.measurableSet).2
    (chordLaw_body_mass ho hb x.property hθ)

/-- Body inclusion transports each actual transition measure, not just its total mass. -/
theorem directionKernel_measurePreserving {K : Set E} (ho : IsOpen K)
    (hb : Bornology.IsBounded K) (θ : E) (hθ : ‖θ‖ = 1) (x : K) :
    MeasurePreserving (Subtype.val : K → E)
      (directionKernel K ho.measurableSet θ hθ x) (chordLaw K x.val θ) :=
  ⟨measurable_subtype_coe, directionKernel_map_subtype ho hb θ hθ x⟩

/-- Integral action agrees exactly with the ambient chord transition. -/
theorem directionKernel_integral_subtype {K : Set E} (ho : IsOpen K)
    (hb : Bornology.IsBounded K) (θ : E) (hθ : ‖θ‖ = 1) (x : K) (f : E → ℝ) :
    (∫ y : K, f y.val ∂directionKernel K ho.measurableSet θ hθ x) =
      ∫ y, f y ∂chordLaw K x.val θ :=
  (directionKernel_measurePreserving ho hb θ hθ x).integral_comp
    (MeasurableEmbedding.subtype_coe ho.measurableSet) f

end HitAndRun.Markov
