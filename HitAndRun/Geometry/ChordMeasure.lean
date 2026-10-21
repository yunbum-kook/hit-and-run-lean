module
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Tactic
@[expose] public section

/-! Actual normalized one-dimensional chord measure. Joint parameter measurability
and conditional-expectation identification are subsequent obligations. -/
namespace HitAndRun.Geometry
open Set MeasureTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

def lineChord (K : Set E) (x θ : E) : Set ℝ := {t | x + t • θ ∈ K}

theorem line_isometry (x θ : E) (hθ : ‖θ‖ = 1) :
    Isometry (fun t : ℝ => x + t • θ) := by
  apply Isometry.of_dist_eq
  intro s t
  simp only [dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul, hθ, mul_one]

theorem lineChord_isOpen {K : Set E} (hK : IsOpen K) (x θ : E) :
    IsOpen (lineChord K x θ) :=
  hK.preimage (continuous_const.add (continuous_id.smul continuous_const))

theorem lineChord_nonempty {K : Set E} {x θ : E} (hx : x ∈ K) :
    (lineChord K x θ).Nonempty := ⟨0, by simpa [lineChord] using hx⟩

theorem lineChord_bounded {K : Set E} (hK : Bornology.IsBounded K)
    (x θ : E) (hθ : ‖θ‖ = 1) : Bornology.IsBounded (lineChord K x θ) :=
  (line_isometry x θ hθ).antilipschitzWith.isBounded_preimage hK

theorem lineChord_volume {K : Set E} (ho : IsOpen K) (hb : Bornology.IsBounded K)
    {x θ : E} (hx : x ∈ K) (hθ : ‖θ‖ = 1) :
    0 < volume (lineChord K x θ) ∧ volume (lineChord K x θ) < ⊤ :=
  ⟨(lineChord_isOpen ho x θ).measure_pos volume (lineChord_nonempty hx),
    (lineChord_bounded hb x θ hθ).measure_lt_top⟩

noncomputable def chordParameterLaw (K : Set E) (x θ : E) : Measure ℝ :=
  (volume (lineChord K x θ))⁻¹ • volume.restrict (lineChord K x θ)

noncomputable def chordLaw (K : Set E) (x θ : E) : Measure E :=
  (chordParameterLaw K x θ).map (fun t => x + t • θ)

theorem chordParameterLaw_probability {K : Set E} (ho : IsOpen K)
    (hb : Bornology.IsBounded K) {x θ : E} (hx : x ∈ K) (hθ : ‖θ‖ = 1) :
    IsProbabilityMeasure (chordParameterLaw K x θ) := by
  have hv := lineChord_volume ho hb hx hθ
  constructor
  simp only [chordParameterLaw, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (ne_of_gt hv.1) (ne_of_lt hv.2)

theorem chordLaw_probability {K : Set E} (ho : IsOpen K)
    (hb : Bornology.IsBounded K) {x θ : E} (hx : x ∈ K) (hθ : ‖θ‖ = 1) :
    IsProbabilityMeasure (chordLaw K x θ) := by
  letI := chordParameterLaw_probability ho hb hx hθ
  unfold chordLaw
  infer_instance

/-- Explicit pushforward formula; no nonmeasurable-map fallback is used. -/
theorem chordLaw_apply (K : Set E) (x θ : E) {A : Set E} (hA : MeasurableSet A) :
    chordLaw K x θ A = (volume (lineChord K x θ))⁻¹ *
      volume ((fun t : ℝ => x + t • θ) ⁻¹' A ∩ lineChord K x θ) := by
  have hf : Measurable (fun t : ℝ => x + t • θ) :=
    (continuous_const.add (continuous_id.smul continuous_const)).measurable
  rw [chordLaw, Measure.map_apply hf hA, chordParameterLaw, Measure.smul_apply,
    Measure.restrict_apply (hA.preimage hf)]
  rfl

/-- The transition is carried by the actual body. -/
theorem chordLaw_body_mass {K : Set E} (ho : IsOpen K) (hb : Bornology.IsBounded K)
    {x θ : E} (hx : x ∈ K) (hθ : ‖θ‖ = 1) : chordLaw K x θ K = 1 := by
  rw [chordLaw_apply K x θ ho.measurableSet]
  change (volume (lineChord K x θ))⁻¹ * volume (lineChord K x θ ∩ lineChord K x θ) = 1
  rw [inter_self]
  have hv := lineChord_volume ho hb hx hθ
  exact ENNReal.inv_mul_cancel (ne_of_gt hv.1) (ne_of_lt hv.2)

end HitAndRun.Geometry
