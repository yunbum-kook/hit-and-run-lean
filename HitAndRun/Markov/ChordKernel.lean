module
public import HitAndRun.Geometry.ChordMeasure
public import Mathlib.Probability.Kernel.Basic
public import Mathlib.MeasureTheory.Measure.Prod
@[expose] public section

/-! The genuine jointly measurable, probability-valued uniform-chord transition.
This supplies the line kernel, not its stationarity or conditional-expectation identification. -/
namespace HitAndRun.Markov
open Set MeasureTheory ProbabilityTheory HitAndRun.Geometry
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem measurable_chord_volume {A : Set E} (hA : MeasurableSet A) :
    Measurable (fun p : E × E => volume ((fun t : ℝ => p.1 + t • p.2) ⁻¹' A)) := by
  have hc : Continuous (fun q : (E × E) × ℝ => q.1.1 + q.2 • q.1.2) :=
    continuous_fst.fst.add (continuous_snd.smul continuous_fst.snd)
  exact measurable_measure_prodMk_left (hA.preimage hc.measurable)

theorem measurable_chordLaw {K : Set E} (hK : MeasurableSet K) :
    Measurable (fun p : E × E => chordLaw K p.1 p.2) := by
  apply Measure.measurable_of_measurable_coe
  intro A hA
  have h := (measurable_chord_volume hK).inv.mul (measurable_chord_volume (hA.inter hK))
  convert h using 1
  funext p
  rw [chordLaw_apply K p.1 p.2 hA]
  rfl

/-- Valid source parameters: an actual body point and a unit direction. -/
abbrev ChordParameter (K : Set E) := {p : E × E // p.1 ∈ K ∧ ‖p.2‖ = 1}

noncomputable def chordKernel (K : Set E) (hK : MeasurableSet K) :
    Kernel (ChordParameter K) E where
  toFun p := chordLaw K p.val.1 p.val.2
  measurable' := (measurable_chordLaw hK).comp measurable_subtype_coe

theorem chordKernel_markov {K : Set E} (ho : IsOpen K) (hb : Bornology.IsBounded K) :
    IsMarkovKernel (chordKernel K ho.measurableSet) := by
  constructor
  intro p
  exact chordLaw_probability ho hb p.property.1 p.property.2

end HitAndRun.Markov
