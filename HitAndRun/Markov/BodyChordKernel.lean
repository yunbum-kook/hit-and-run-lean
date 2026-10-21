module
public import HitAndRun.Markov.ChordKernel
public import Mathlib.Probability.Kernel.Composition.MapComap
@[expose] public section

namespace HitAndRun.Markov
open Set MeasureTheory ProbabilityTheory HitAndRun.Geometry
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- Restrict outcomes to the actual body using the proved full body mass. -/
noncomputable def bodyChordKernel (K : Set E) (hK : MeasurableSet K) :
    Kernel (ChordParameter K) K :=
  (chordKernel K hK).comapRight (MeasurableEmbedding.subtype_coe hK)

theorem bodyChordKernel_markov {K : Set E} (ho : IsOpen K) (hb : Bornology.IsBounded K) :
    IsMarkovKernel (bodyChordKernel K ho.measurableSet) := by
  apply Kernel.IsMarkovKernel.comapRight
  intro p
  simpa [chordKernel] using chordLaw_body_mass ho hb p.property.1 p.property.2

/-- The actual chord step in a fixed unit direction, on body-valued states. -/
noncomputable def directionKernel (K : Set E) (hK : MeasurableSet K)
    (θ : E) (hθ : ‖θ‖ = 1) : Kernel K K :=
  (bodyChordKernel K hK).comap
    (fun x => (⟨(x.val, θ), x.property, hθ⟩ : ChordParameter K))
    ((measurable_subtype_coe.prodMk measurable_const).subtype_mk)

theorem directionKernel_markov {K : Set E} (ho : IsOpen K) (hb : Bornology.IsBounded K)
    (θ : E) (hθ : ‖θ‖ = 1) : IsMarkovKernel (directionKernel K ho.measurableSet θ hθ) := by
  letI := bodyChordKernel_markov ho hb
  unfold directionKernel
  infer_instance
end HitAndRun.Markov
